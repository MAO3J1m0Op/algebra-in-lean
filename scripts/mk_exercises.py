#!/usr/bin/env python3

import os
import re
import shutil
import sys
import typing as t
from pathlib import Path

re_flags = re.IGNORECASE | re.DOTALL
re_start = re.compile(
    r"/-\s*exercise\s+begin\s*(?::\s*(?P<replace>.*?))?\s*-/",
    re_flags,
)
re_end = re.compile(r"/-\s*exercise\s+end\s*-/", re_flags)


def process(source: Path, dest: Path) -> None:
    with source.open("r") as f:
        src = f.read()

    curr = 0
    with dest.open("w") as dst:
        while True:
            end = src.find("/-", curr)
            curr += dst.write(src[curr:end])
            if end == -1:
                break
            curr += comment_start(src, dst, curr)


def comment_start(src: str, dst: t.TextIO, curr: int) -> int:
    start = curr + 2
    end = src.find("-/", start)
    m = re_start.fullmatch(src[start:end])
    if m is None:
        return dst.write(src[curr : end + 2])
    replacement = m.groupdict("sorry")["replace"]
    _ = dst.write(replacement)
    return comment_end(src, end + 2) - curr


def comment_end(src: str, curr: int) -> int:
    while True:
        tmp = src.find("/-", curr) + 2
        curr = src.find("-/", tmp)
        if tmp == -1 or curr == -1:
            raise EOFError
        m = re_end.fullmatch(src[tmp:curr])
        if m is not None:
            return curr + 2


def run(srcd: Path, dstd: Path) -> None:
    stack = [srcd]
    while stack:
        try:
            source: Path = stack.pop()
            path = source.relative_to(srcd)
            _ = sys.stderr.write(f"{path} ...")
            dest = dstd / path

            if source.is_dir():
                stack += source.iterdir()
                mode = source.lstat().st_mode
                dest.mkdir(mode, exist_ok=True)
            else:
                process(source, dest)
                shutil.copystat(source, dest, follow_symlinks=False)
        except Exception:  # noqa: BLE001, PERF203
            _ = sys.stderr.write(" Failed\n")
        else:
            _ = sys.stderr.write(" Done\n")


def main() -> None:
    root = Path(__file__).parent.parent
    os.chdir(root)

    run(root / "AlgebraInLean", root / "Exercises")


if __name__ == "__main__":
    main()
