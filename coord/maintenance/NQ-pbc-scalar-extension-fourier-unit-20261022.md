# Scalar-extension maintenance: stale Fourier unit citation, 2026-10-22

Item: prop-weil-pbc-scalar-extension@e2a95534a, stage 1, group NQ.

The retained two-child repair was blocked by the global unit check:
`units: sk-def-ft cites sk-lem-as-properties, which its nodes do not reach`.
This is a data inconsistency outside the worker's authorized item/new-node
files, so repeating the same worker could not repair it.

The N6 definition split was reviewed and landed at
4ce42a1d31c5ee0380c561ccc6fcdb88c9f59d34. Its review explicitly accepts
removing sk-lem-as-properties: the current ordinary-etale definition uses
sk-def-kernel and def-fd-transform, while the removed theorem concerns adic
character-sheaf properties with narrower hypotheses. The inverse character
is defined by substitution, without a tensor-inverse assertion. The unit
record only received its realized fields and retained the older master
statement (including that assertion) and dependency list. The current
main-20261015 source body has already removed the assertion; its frontmatter
still contains the stale citation too.

The repair updates dag/units/sk-def-ft.json to the verbatim main-20261015
source body and source path, and removes the unused sk-lem-as-properties
entry from uses, consistently with the independently reviewed live split.
Its realization, Lean names, chapter and remaining dependency are preserved.
No source snapshot, node statement, proof, Lean module, chapter, launcher,
review service or landing tool is changed. The original unit is backed up as
dag/units/sk-def-ft.json.maint-NQ-pbc-scalar-extension-20261022.bak.

A server-side audit pinned to 62dc32228f3cd58d4abc6ed83b89a01768d44ba4
used the project's own units.check and dependency graph with the actual NQ
packet overlaid using SPLIT_OWNS. Before repair, the base happens to reach
sk-lem-as-properties through prop-weil-pbc-scalar-extension and the unused
lem-sbc-completed-operations-linear-natural-exchange edge. The packet removes
that edge, exposing the stale unit requirement. With the proposed unit
repair the actual Fourier error disappears; no unit or route finding is
introduced on either the base or the packet. Standing unrelated findings
remain; this is not a claim that the whole DAG is clean. The detailed audit
is record-audit.json in the local maintenance directory.

Next worker: refresh main with this repair and rerun the ordinary unmodified
`deliver.py NQ prop-weil-pbc-scalar-extension --no-push`. Retain the current
2944-character assembly, the TWO statement-only unsplit normalization
children, all 40 citation quotations, authentic searches and argument
handoffs. The October 22 repair handoff in coord/returns/NQ.md is active;
the older ND recovery with four children describes a resolved earlier
repair. Do not restore the unused completed-operations edge: that would
reintroduce a cycle. Continue the normal independent-reader delivery path.
The maintenance REPORT.md records the final delivery validation result.
