"""Extract Forsaken World (Shenmo) .SUP update packages, with ease.

   Written by Fyyre - https://github.com/Fyyre
"""

import argparse
import os
import struct
import sys
import zlib

AFPCK_VERSIONS = (0x00020002, 0x00020001)
SAFE_TAG1 = 0x4DCA23EF
SAFE_TAG2 = 0x56A089B7
PACK_FLAG_ENCRYPT = 0x80000000
MAX_FILE_PACKAGE = 0x7FFFFF00
FILEENTRY_SIZE = 276
FILEHEADER_SIZE = 272

# SetAlgorithmID: base + id * mul, mod 2^32.
_KEY_BASE = (
    0xFDFDFEEE,  # guard0
    0xF00DBEEF,  # guard1
    0xA8937462,  # mask
    0x59374231,  # check
)
_KEY_MUL = (
    0x072341F2,
    0x01237A73,
    0x0AB2321F,
    0x0987A223,
)
_KEY111 = (0xAB12908F, 0xB3231902, 0x2A63810E, 0x18734563)

_SAFE = struct.Struct("<III")
_U32 = struct.Struct("<I")
_I32 = struct.Struct("<i")
_HEADER = struct.Struct("<IIII252sI")
_ENTRY = struct.Struct("<260sIIIi")


def _u32(value):
    return value & 0xFFFFFFFF


def keys_for_id(algorithm_id):
    if algorithm_id == 111:
        return _KEY111
    return tuple(_u32(base + algorithm_id * mul) for base, mul in zip(_KEY_BASE, _KEY_MUL))


def detect_algorithm(guard0, guard1):
    if guard0 == _KEY111[0] and guard1 == _KEY111[1]:
        return 111, _KEY111[2], _KEY111[3]
    inv = pow(_KEY_MUL[1], -1, 2 ** 32)
    algorithm_id = _u32((guard1 - _KEY_BASE[1]) * inv)
    expect0, _expect1, mask, check = keys_for_id(algorithm_id)
    if expect0 != guard0:
        return None
    return algorithm_id, mask, check


def decrypt(data):
    length = len(data)
    mask = _u32(length + 0x739802AB)
    out = bytearray(data)
    for i in range(0, length - 3, 4):
        value = (out[i] << 24) | (out[i + 1] << 16) | (out[i + 2] << 8) | out[i + 3]
        value = _u32((value << 16) | (value >> 16))
        value ^= mask
        out[i] = (value >> 24) & 0xFF
        out[i + 1] = (value >> 16) & 0xFF
        out[i + 2] = (value >> 8) & 0xFF
        out[i + 3] = value & 0xFF
    return bytes(out)


# base64. 63rd character is - instead of /
_B64_ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+-"
_B64_VALUE = {ord(ch): idx for idx, ch in enumerate(_B64_ALPHABET)}
_B64_VALUE[ord("=")] = 0


def _is_b64(ch):
    return ord(ch) in _B64_VALUE


def _b64_decode(segment):
    raw = segment.encode("ascii")
    out = bytearray()
    for i in range(0, len(raw), 4):
        vals = []
        for k in range(4):
            if i + k < len(raw):
                vals.append(_B64_VALUE[raw[i + k]])
            else:
                vals.append(0)
        value = (vals[0] << 18) + (vals[1] << 12) + (vals[2] << 6) + vals[3]
        out.append((value >> 16) & 0xFF)
        out.append((value >> 8) & 0xFF)
        out.append(value & 0xFF)
    nul = out.find(b"\x00")
    if nul >= 0:
        del out[nul:]
    return bytes(out)


def _decode_segment(segment):
    if not segment or any(not _is_b64(ch) for ch in segment):
        return segment
    try:
        raw = _b64_decode(segment)
        return raw.decode("utf-8")
    except UnicodeDecodeError:
        return segment


def _decode_encoded_path(encoded):
    """base64 become UTF-8, neat"""
    out = []
    start = 0
    for i, ch in enumerate(encoded):
        if _is_b64(ch):
            continue
        if i != start:
            out.append(_decode_segment(encoded[start:i]))
        out.append(ch)
        start = i + 1
    if start != len(encoded):
        out.append(_decode_segment(encoded[start:]))
    return "".join(out)


def _apply_transfer_path(name, state):
    if name.startswith("/"):
        encoded = "." + name
        slash = encoded.rfind("/")
        state["fp"] = encoded[:slash + 1] if slash >= 0 else ""
        return encoded
    return state["fp"] + name


def _lookup_key(encoded):
    path = encoded.replace("/", "\\")
    if path.startswith(".\\"):
        path = path[2:]
    path = "element\\" + path.lstrip("\\")
    return path.lower()


def _output_rel(decoded):
    path = decoded.replace("\\", "/")
    if path.startswith("./"):
        path = path[2:]
    return path.lstrip("/")


def parse_inc(data):
    """map the lowercase paths to the UTF-8."""
    state = {"fp": ""}
    mapping = {}
    text = data.decode("ascii", errors="replace")
    for line in text.splitlines():
        if not line or line.startswith("#"):
            continue
        if line.startswith("-----BEGIN ELEMENT SIGNATURE-----"):
            break
        parts = line.split()
        if len(parts) < 2:
            continue
        token, fn = parts[0], parts[1]
        if token.startswith("-"):
            continue
        encoded = _apply_transfer_path(fn, state)
        decoded = _output_rel(_decode_encoded_path(encoded))
        if not decoded:
            continue
        mapping[_lookup_key(encoded)] = decoded
    return mapping


def unwrap_update_blob(data):
    """4-byte size + raw payload/zlib."""
    if len(data) < 4:
        return data, False
    size = struct.unpack_from("<I", data)[0]
    if size > 512 * 1024 * 1024:
        return data, False
    if size + 4 == len(data):
        return data[4:], True
    try:
        out = zlib.decompress(data[4:])
    except zlib.error:
        return data, False
    if len(out) != size:
        return data, False
    return out, True


class PackageFile(object):
    """process a single .SUP file, add .pkx when > 2GB"""
    def __init__(self, path):
        self.path = path
        self.file1 = open(path, "rb")
        self.file1.seek(0, os.SEEK_END)
        self.size1 = self.file1.tell()
        self.file2 = None
        self.size2 = 0
        pkx = os.path.splitext(path)[0] + ".pkx"
        if os.path.isfile(pkx):
            self.file2 = open(pkx, "rb")
            self.file2.seek(0, os.SEEK_END)
            self.size2 = self.file2.tell()

    def close(self):
        self.file1.close()
        if self.file2:
            self.file2.close()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        self.close()
        return False

    @property
    def size(self):
        return self.size1 + self.size2

    def read(self, offset, size):
        if size < 0 or offset < 0:
            raise ValueError("negative read...")
        if offset + size > self.size:
            raise IOError("read past end of package at %d" % offset)
        if self.file2 is None or offset + size <= MAX_FILE_PACKAGE:
            self.file1.seek(offset)
            data = self.file1.read(size)
        elif offset >= MAX_FILE_PACKAGE:
            self.file2.seek(offset - MAX_FILE_PACKAGE)
            data = self.file2.read(size)
        else:
            first = MAX_FILE_PACKAGE - offset
            self.file1.seek(offset)
            data = self.file1.read(first)
            self.file2.seek(0)
            data += self.file2.read(size - first)
        if len(data) != size:
            raise IOError("read at %d" % offset)
        return data


def _decode_name(raw):
    end = raw.find(b"\x00")
    if end >= 0:
        raw = raw[:end]
    if not raw:
        return ""
    try:
        return raw.decode("gb18030")
    except UnicodeDecodeError:
        return raw.decode("latin-1")


def _safe_parts(name):
    name = name.replace("/", "\\")
    parts = []
    for part in name.split("\\"):
        if part in ("", "."):
            continue
        if part == "..":
            raise ValueError("path escapes the archive: %s" % name)
        if ":" in part or part.startswith("\\\\"):
            raise ValueError("absolute path in archive: %s" % name)
        parts.append(part)
    if not parts:
        raise ValueError("empty file name!")
    return parts


def open_package(path):
    pkg = PackageFile(path)
    try:
        entries, info = _read_index(pkg)
    except Exception:
        pkg.close()
        raise
    return pkg, entries, info


def _read_index(pkg):
    if pkg.size < _SAFE.size + FILEHEADER_SIZE + 8:
        raise ValueError("file is too small to be a sup package")

    tag1, safe_offset, tag2 = _SAFE.unpack(pkg.read(0, _SAFE.size))
    if tag1 == SAFE_TAG1 and tag2 == SAFE_TAG2:
        if not (FILEHEADER_SIZE + 8 < safe_offset <= pkg.size):
            raise ValueError("safe header offset %d is outside the file" % safe_offset)
        end = safe_offset
        has_safe = True
    else:
        end = pkg.size
        has_safe = False

    version = _U32.unpack(pkg.read(end - 4, 4))[0]
    if version not in AFPCK_VERSIONS:
        raise ValueError("unsupported package version %#x" % version)

    count = _I32.unpack(pkg.read(end - 8, 4))[0]
    if count < 0 or count > 2000000:
        raise ValueError("unreasonable file count %d" % count)

    header = pkg.read(end - 8 - FILEHEADER_SIZE, FILEHEADER_SIZE)
    guard0, hdr_version, entry_offset, flags, description, guard1 = _HEADER.unpack(header)
    if b"lica File Package" not in description:
        raise ValueError("package description is missing")

    detected = detect_algorithm(guard0, guard1)
    if detected is None:
        raise ValueError("guard bytes %#x %#x do not match a known algorithm" % (guard0, guard1))
    algorithm_id, mask, check = detected
    entry_offset = _u32(entry_offset ^ mask)

    if entry_offset >= end:
        raise ValueError("entry table offset %#x is past the logical end" % entry_offset)

    entries = []
    cursor = entry_offset
    for index in range(count):
        if cursor + 8 > end:
            raise ValueError("entry table truncated at file %d" % index)
        comp_size = _u32(_I32.unpack(pkg.read(cursor, 4))[0] ^ mask)
        check_size = _u32(_I32.unpack(pkg.read(cursor + 4, 4))[0] ^ check ^ mask)
        cursor += 8
        if comp_size != check_size:
            raise ValueError("entry %d size check failed" % index)
        if comp_size == 0 or comp_size > 4096 or cursor + comp_size > end:
            raise ValueError("entry %d has a bad compressed size %d" % (index, comp_size))
        comp = pkg.read(cursor, comp_size)
        cursor += comp_size
        if comp_size == FILEENTRY_SIZE:
            raw_entry = comp
        else:
            try:
                raw_entry = zlib.decompress(comp)
            except zlib.error as exc:
                raise ValueError("entry %d failed to decompress: %s" % (index, exc))
        if len(raw_entry) != FILEENTRY_SIZE:
            raise ValueError("entry %d decompressed to %d bytes" % (index, len(raw_entry)))
        name_raw, offset, length, comp_len, _access = _ENTRY.unpack(raw_entry)
        name = _decode_name(name_raw)
        entries.append((name, offset, length, comp_len))

    info = {
        "version": version,
        "header_version": hdr_version,
        "count": count,
        "flags": flags,
        "algorithm": algorithm_id,
        "encrypted": flags == PACK_FLAG_ENCRYPT,
        "safe_header": has_safe,
        "logical_end": end,
    }
    return entries, info


def read_file_bytes(pkg, entry, encrypted):
    name, offset, length, comp_len = entry
    if length == 0:
        return b""
    if length > comp_len:
        data = pkg.read(offset, comp_len)
        if encrypted:
            data = decrypt(data)
        try:
            data = zlib.decompress(data)
        except zlib.error as exc:
            raise ValueError("%s: zlib error: %s" % (name, exc))
        if len(data) != length:
            raise ValueError("%s: decompressed %d bytes, entry says %d" % (name, len(data), length))
        return data
    data = pkg.read(offset, length)
    if encrypted:
        data = decrypt(data)
    return data


def _output_path(out_dir, parts):
    path = out_dir
    for part in parts:
        path = os.path.join(path, part)
    return path


def _display_name(entry_name, name_map):
    return name_map.get(entry_name.lower(), entry_name)


def _load_name_map(pkg, entries, encrypted):
    by_name = {entry[0].lower(): entry for entry in entries}
    inc_entry = by_name.get("inc")
    if inc_entry is None:
        return {}
    data = read_file_bytes(pkg, inc_entry, encrypted)
    return parse_inc(data)


def extract(path, out_dir, list_only=False):
    pkg, entries, info = open_package(path)
    try:
        name_map = _load_name_map(pkg, entries, info["encrypted"])
        print("package: %s" % path)
        print(
            "version: %d.%d  files: %d  algorithm: %d  encrypted: %s  names: %d"
            % (
                info["version"] >> 16,
                info["version"] & 0xFFFF,
                info["count"],
                info["algorithm"],
                "yes" if info["encrypted"] else "no",
                len(name_map),
            )
        )
        if list_only:
            for entry in entries:
                print("%10d  %s" % (entry[2], _display_name(entry[0], name_map)))
            return 0

        os.makedirs(out_dir, exist_ok=True)
        failed = 0
        written = 0
        wrapped = 0
        for entry in entries:
            shown = _display_name(entry[0], name_map)
            try:
                parts = _safe_parts(shown)
                data = read_file_bytes(pkg, entry, info["encrypted"])
                data, did_unwrap = unwrap_update_blob(data)
                if did_unwrap:
                    wrapped += 1
                elif entry[0].lower() in name_map:
                    print("warning: %s was not an update blob" % shown, file=sys.stderr)
                dest = _output_path(out_dir, parts)
                parent = os.path.dirname(dest)
                if parent:
                    os.makedirs(parent, exist_ok=True)
                with open(dest, "wb") as out:
                    out.write(data)
                written += 1
            except Exception as exc:
                failed += 1
                print("failed: %s: %s" % (shown, exc), file=sys.stderr)
        print("extracted %d files to %s" % (written, out_dir))
        print("unwrapped %d update blobs" % wrapped)
        if failed:
            print("%d files failed" % failed, file=sys.stderr)
            return 1
        return 0
    finally:
        pkg.close()


def main(argv):
    parser = argparse.ArgumentParser(
        prog="sup_extract.py",
        description="Forsaken World .SUP Extractor - Fyyre https://github.com/Fyyre",
    )
    parser.add_argument("sup_file", help="path to the .sup package")
    parser.add_argument(
        "output_dir",
        nargs="?",
        help="directory to write files into (default: ./<sup name>)",
    )
    parser.add_argument(
        "-l",
        "--list",
        action="store_true",
        help="list files instead of extracting them",
    )
    args = parser.parse_args(argv)
    sup_path = os.path.abspath(args.sup_file)
    if not os.path.isfile(sup_path):
        print("not a file: %s" % sup_path, file=sys.stderr)
        return 1
    if args.output_dir:
        out_dir = os.path.abspath(args.output_dir)
    else:
        stem = os.path.splitext(os.path.basename(sup_path))[0]
        out_dir = os.path.abspath(stem)
    try:
        return extract(sup_path, out_dir, list_only=args.list)
    except Exception as exc:
        print("error: %s" % exc, file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
