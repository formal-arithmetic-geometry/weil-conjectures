# Q43 finite-etale-descent repair count reconciliation

The retained stage-1 worker repair was blocked by contradictory coordination data.
The generic released repair note measured a 7680-character proof and demanded two
new nodes. The independent return for be30634e654 (coord/returns/Q43.md, 2026-10-22
07:13 UTC) then identified all three proposed children as duplicates of existing
reviewed statements, directed their removal and allowed a count-waiver request.
The worker removed them and requested that waiver, but no decision was recorded.

tools/preflight_delivery.py:355-397 selects the old quota from the active note's
text. It computes a minimum of two from the original proof length and credits
only one previously landed cited node. Thus zero added nodes plus one credited
node always failed, although the four-step repair and the server DAG/split
checks passed. Retrying the mathematical repair cannot resolve this mismatch.
The Q43 dispatcher recorded 93 failures at maintenance start; failures are
counts, not a dispatch stop condition. No dispatch policy is changed.

This maintenance task grants the requested item-specific zero-new-node count
waiver and replaces the active generic instruction with the concrete C5/D1/D2
repair requirements. The full original record remains under previous, and
count_waiver records the scope and basis. The matching return receives an
addendum so future worker briefs carry the decision. The repair stays released
and its claim/return remains open: this is not mathematical acceptance.

The retained sandbox has a 2385-character assembly (steps 550, 457, 723, 655),
17 citation entries, 14 proof-dependency roots and verbatim returned step 4.
The already performed ownership audit maps the dropped domains node to existing
input models, preservation and comparison nodes; the dropped scalar square to
lem-sp-et-proet-coefficient-compatibility plus lem-coef-finite-direct-image;
and the dropped transpose to lem-coef-site-closed-counit-transport.
The previous raw closure audit follows both statement and proof dependencies
below reviewed nodes and reaches neither this item nor the batch-5 assumptions.
These mechanical facts and the independent return justify resolving the record
without doing the item's mathematics again. A fresh full server dry run remains
required before delivery, and independent review remains required before merge.

No Lean, DAG node, launcher code, preflight code, review service or landing tool
is changed. No compiler or lake build is needed for this record-only repair.
Every existing changed file receives a .maint-Q43-1792759476.bak backup.
