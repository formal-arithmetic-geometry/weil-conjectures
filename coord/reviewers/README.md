# Reviewer briefs (one copy for both machines)

Copied verbatim on 2026-10-17 from the Codex machine, where the existing Codex reviewers use them:

| file | Codex machine source | used by |
|---|---|---|
| review-brief.md  | ~/weil-launcher-nt/review-brief.md  | stage 1 reader (review.py); cc lane S1 |
| review-brief2.md | ~/weil-launcher-nt/review-brief2.md | stage 2 reader (review_stage2.py); cc lane S2 |
| check-brief2.md  | ~/weil-launcher-nt/check-brief2.md  | read by the stage-2 reader (named in review-brief2.md) |
| review-brief3.md | ~/weil-launcher/review-brief3.md    | stage 3 reader (xreview.py); cc lane S3 |

The cc review service on the server (~/weil-review-svc, README.md there) reads these files from this directory and
only substitutes machine paths (lcompile.py, literature, clones) at run time. Change a review standard here and copy
the file to the Codex machine path above, so that both reviewers keep the same text.
