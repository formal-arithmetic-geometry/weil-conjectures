#!/usr/bin/env python3
"""Use the shared --stage 2 merger with the human's commit policy, side only."""
import os
import sys

os.environ["SHEAF_LEAD"] = "L-only"
import merge_delivery as md

original_git = md.git
TRAILER = "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"


def git(*args, check=True):
    if args and args[0] == "commit":
        args = list(args)
        for j in range(1, len(args)):
            if args[j - 1] == "-m" and not args[j].endswith(TRAILER):
                args[j] += "\n\n" + TRAILER
    return original_git("-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com",
                        *args, check=check)


md.git = git
if __name__ == "__main__":
    raise SystemExit(md.main())
