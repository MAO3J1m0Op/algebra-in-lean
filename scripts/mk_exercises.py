#!/usr/bin/env python3

import io
import os
import re
import shutil
import typing as t
from collections import deque
from pathlib import Path

REGEX = re.compile(
    r"""/- \s*                              # open comment
        exercise \s+ begin \s*              # begin keyword
        (?: : \s* (?P<replace> .*? ) )?     # optional replacement
        \s* -/                              # close comment

        .*?                                 # contained text to delete
        /- \s*                              # open comment
        exercise \s+ end                    # end keyword
        \s* -/                              # close comment
    """,
    re.IGNORECASE | re.DOTALL | re.VERBOSE,
)


def process(source: t.TextIO, dest: t.TextIO) -> None:
    src = source.read()
    curr = 0
    for m in REGEX.finditer(src):
        _ = dest.write(src[curr : m.start()])
        replace = m.groupdict("sorry")["replace"]
        _ = dest.write(replace)
        curr = m.end() + 1
    _ = dest.write(src[curr:-1])


def run(srcd: Path, dstd: Path) -> None:
    stack = deque((srcd,))
    while stack:
        source: Path = stack.popleft()
        path = source.relative_to(srcd)
        _ = print(path)
        dest = dstd / path

        if source.is_dir():
            stack += source.iterdir()
            mode = source.lstat().st_mode
            dest.mkdir(mode, exist_ok=True)
        else:
            execute(source, dest)
            shutil.copystat(source, dest, follow_symlinks=False)


def execute(source: Path, dest: Path) -> None:
    with source.open("r") as src, io.StringIO() as output:
        process(src, output)
        out = output.getvalue()
    with dest.open("w") as dst:
        _ = dst.write(out)


def main() -> None:
    root = Path(__file__).parent.parent
    os.chdir(root)

    run(root / "AlgebraInLean", root / "Exercises")


if __name__ == "__main__":
    main()
