# Retired blowup module ownership repair (NV maintenance, 2026-10-22)

The stage-2 packet for lem-sfb-cover-nested-cartier-preparation compiled but was
rejected by route_pivot_fails: its required IntegralBlowupProjectiveGeometry
import was assigned to dropped lem-per-integral-blowup-projective-geometry.

Commit f6bf55e2b05 deleted the old module on 2026-10-20 but retained its lean
record (with a deletion note) and reviewed_lean pass. Commit a59c36b4e1d later
landed the same module path for active lem-sfb-integral-blowup-projective-geometry.
The source now declares isIntegral_blowup_and_isProjectiveBundle for that active
node. The old integral_blowup_projectiveBundle declaration no longer exists.
The stage-2 gate builds its dropped-module map from the obsolete lean record;
the derived stage-3 module list also retained the old path.

Remove only lean and reviewed_lean from the retired node, leaving its statement,
proof, split review, and dropped-node exclusion intact. Remove only the matching
module line from coord/route-pivot-dropped-modules.txt, which is documented as
derived from dropped nodes' lean.module records. The active node's declaration
and reviewed record remain the authoritative module ownership. No mathematics,
delivery or review code, or human route-pivot node policy is changed.

Full backups of both edited files are adjacent, with suffix
.maint-NV-20261022.bak; the removed declaration and review also remain in Git.

The next NV worker should retain the saved Lean module, item node, and report;
run deliver2.py NV lem-sfb-cover-nested-cartier-preparation --no-push against
the updated server tip, then deliver normally once the dry run passes. The Q134
stage-1 split is already reviewed; no second split or proof work is needed.
