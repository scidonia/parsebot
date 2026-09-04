#!/usr/bin/env python3
"""Generate the synthetic JSON benchmark `large_int.json` used in the slides.

Structure (per the slides): an array of objects with keys
{"id","name","tags","child","flags"} -- integers, booleans, null, and a nested
array/object.  Each object is ~159 bytes, so the slide's object counts land at
the slide's sizes:

    30k objects  -> 4.77 MB
    63k objects  -> 10.0 MB
    158k objects -> 25.2 MB
    316k objects -> 50.3 MB
"""
import json
import sys


def obj(i: int) -> dict:
    return {
        "id": 1234567890 + i,
        "name": "item_name_" + str(1234567890 + i),
        "tags": [i % 997, (i * 7) % 997, (i * 31) % 997],
        "child": {"id": 9876543210 + i, "flags": [True, False]},
        "flags": [True, False, None],
    }


def main() -> None:
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 30000
    out = sys.argv[2] if len(sys.argv) > 2 else "large_int.json"
    with open(out, "w") as f:
        f.write("[")
        for i in range(count):
            if i:
                f.write(",")
            json.dump(obj(i), f)
        f.write("]")


if __name__ == "__main__":
    main()
