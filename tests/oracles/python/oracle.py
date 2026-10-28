"""The Python oracle: posixpath.normpath from the standard library.

It reads requests on standard input, one per line, as `path serve`
does (see the header of Main.lean), and answers `clean HEX` with OK and
the hex of posixpath.normpath. posixpath.join keeps only the last
rooted argument, which is not what Go's Join does, so `join` and
anything else get `n/a`. A path is the hex of its UTF-8 octets, and
the empty path is `-`.
"""

import posixpath
import sys


def field(f):
    if f == "-":
        return ""
    if not f:
        return None
    try:
        return bytes.fromhex(f).decode("utf-8")
    except ValueError:
        return None


def out(s):
    return s.encode("utf-8").hex() or "-"


def answer(line):
    fs = line.split(" ")
    if fs[0] == "clean" and len(fs) == 2:
        p = field(fs[1])
        if p is not None:
            return "OK " + out(posixpath.normpath(p))
    return "n/a"


def main():
    stdin = sys.stdin.buffer
    stdout = sys.stdout
    for raw in stdin:
        line = raw.decode("utf-8", "replace").rstrip("\n").rstrip("\r")
        stdout.write(answer(line) + "\n")
    stdout.flush()


if __name__ == "__main__":
    main()
