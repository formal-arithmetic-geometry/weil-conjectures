Files written:
- `dag/nodes/sec-picard-framework/lem-pc-dim-zero-finite-over-field.json`: statement, kind, split proof, Mathlib searches; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-algebraic-dim-zero-affine-finite.json`: unsplit statement node for the algebraic zero-dimensional conclusion; no Mathlib match.

Attachments:
- None. I found no sorry-free declaration in slopmaster2 stating the item exactly.

WANTED:
- None. The cited Stacks source is represented by the repository's citation metadata for Tag 06LH.

What I checked and corrected:
- The item's statement was checked against the Stacks Project online text of Varieties, Tag 06LH (algebraic-scheme-dim-0): a proper scheme over a field is finite type, and a finite-type zero-dimensional scheme is affine and finite. The repository's local Stacks TeX checkout is absent on this machine. The existing definitions cited by the item state properness, dimension, finiteness, and affineness.
- I searched the full DAG and blueprint for the 06LH conclusion and found no existing node; I also searched the Lean source and found no exact declaration. The new node states only that smaller conclusion and remains unsplit.
- Step 1 uses `pqf-lem-proper-basic` for proper implies finite type. Step 2 uses the new 06LH node for affineness and finiteness. Step 3 uses the existing Mathlib-backed `lem-weil-pbc-finite-over-field-affine-finite-dim` for finite-dimensional global sections. These cited statements match the roles assigned to them.
- I tested edge cases conceptually: the empty scheme satisfies the conclusion separately (Tag 06LH states dimension exactly zero); `Spec k` and `Spec(k[e]/(e^2))` are finite affine zero-dimensional examples. No hypothesis was added or dropped.
- Mathlib searches for the new node used LeanSearch, LeanFinder, and source grep; no exact theorem was found. The item search similarly found only general finiteness criteria.

## Review by K1
I read the online Stacks Tag 06LH statement and proof and the parent blueprint sentence in `lem-pc-degree-base-change`. Tag 06LH is the source for the new algebraic zero-dimensional node and for the item's central implication; its proof passes from finite-type affine charts through Artinian rings to a finite disjoint union. I verified that properness contributes finite type through `pqf-lem-proper-basic`, that the new node contributes exactly affineness and finiteness, and that the existing finite-over-field leaf contributes finite-dimensional global sections. I checked each item's hypothesis against the cited statement: the field is the base, properness gives finite type, and the dimension bound is the required zero-dimensional assumption when the scheme is nonempty. I checked the new node's statement independently against the algebraic case of 06LH and found no Mathlib or DAG duplicate. The small cases checked are the empty scheme (handled trivially), `Spec k`, and a finite nonreduced algebra such as `Spec(k[e]/(e^2))`; all satisfy the stated conclusion. I made the hidden proper-to-finite-type step explicit and isolated the 06LH theorem as its own unsplit node. Preflight then required `pqf-lem-proper-basic` to be declared as an off-unit generic tool, which I added to `split_report.tool_uses` before it passed.
