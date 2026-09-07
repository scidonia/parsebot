#!/usr/bin/env python3
"""Generate a synthetic TOML document for the parsebot benchmark.

The S8 TOML surface is a minimal, *flat* grammar: integer-valued scalars
(`k = v`), dotted keys (`a.b = v` — `a` becomes an implicit table and `b` is a
flat leaf), tables (`[a]`), and arrays-of-tables (`[[a]]`).  Dotted keys are not
scoped: two dotted keys sharing the same final segment collide, so every leaf
segment must be globally unique.

This generator emits `n` items, each a flat key plus a dotted key with unique
segments, plus a header and a few tables/arrays-of-tables.

Run: python3 gen_toml.py [items] [out.toml]
"""

import sys


def main() -> None:
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
    out = sys.argv[2] if len(sys.argv) > 2 else "bench.toml"
    with open(out, "w") as f:
        f.write("title = 42\n")
        f.write("version = 7\n")
        for i in range(n):
            f.write(f"key{i} = {i % 1000000}\n")
            f.write(f"grp{i}.leaf{i} = {1234567890 + i}\n")
        # a few standalone tables and arrays-of-tables
        for i in range(max(1, n // 100)):
            f.write(f"[table{i}]\n")
            f.write(f"[[arr{i}]]\n")


if __name__ == "__main__":
    main()
