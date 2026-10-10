Files written:

- `dag/nodes/sec-picard-framework/lem-sc-p1-koszul-resolution.json`: statement split into four proof steps; no Mathlib leaf for the item.
- `dag/nodes/sec-picard-framework/lem-sc-p1-linear-syzygy.json`: statement-only unsplit node; Mathlib search verdict no match.

Attachments: none. The slopmaster2 declaration `AlgebraicGeometry.ProjectiveLine.exists_exact_sigma_twist` is the parent sheaf resolution and has `sorry`; it does not state this graded Koszul resolution.

WANTED: EGA II, Section 2 or Hartshorne II.5, for the graded Koszul/Hilbert syzygy source cited by the blueprint (the local literature checkout does not contain these books).

The item was an unsplit statement whose source note identifies the Koszul resolution on the regular sequence `x_0,x_1`. I retained its statement and added the missing proof route. The only new mathematical dependency is the two-variable linear syzygy node; the polynomial-domain fact already exists as `lem-weil-pbc-polynomial-ring-domain` and is used as a generic tool because this unit has no domain node. The small case `k[x_0,x_1]` with `a=x_1`, `b=-x_0` checks the middle generator, and the zero element checks the left kernel. No source statement error was found.

## Review by G1

I read the item node, its parent `lem-sc-p1-graded-resolution`, the standard grading definition, and the existing polynomial-domain node. The four steps use exactly the displayed shift statement, the integral-domain statement, the new syzygy statement, and then the shift statement again; each citation quote in `citations.json` is copied verbatim from the cited node. Steps 1 and 4 are elementary degree and quotient checks. Step 2 uses the domain hypothesis to cancel `x_0`; Step 3 uses the stated syzygy identity to identify the middle kernel with the image of `(x_1,-x_0)`. I searched the DAG and blueprint for an existing two-variable syzygy or Koszul node and searched Mathlib by LeanSearch, Loogle, and source grep; no duplicate or exact Mathlib theorem was found. I also checked the edge cases `a=b=0` and the generator pair `(x_1,-x_0)`, and verified the source path issue is reported as WANTED rather than silently treated as a local literature citation.
