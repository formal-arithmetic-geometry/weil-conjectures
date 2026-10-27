## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-abelian-field-extension.json`: statement, split in five steps; no Mathlib match for the complete item.
- `citations.json`: one verbatim statement quotation for each node used in each step.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The sandbox initially contained only dispatcher markers, with no earlier split, report, citations or search log. The current repository item was copied; its statement and inherited metadata were retained.

## Attachments

No attachment is requested for this item, following the dispatcher's rejection of the earlier attachment. The read clone now contains `AlgebraicGeometry.IsAbelianVariety.pullback` at `lean/WeilConjectures/AlgebraicGeometry/AbelianVariety/Basic.lean:124`, which covers preservation, and `AlgebraicGeometry.topologicalKrullDim_pullback_eq_of_field` at `lean/WeilConjectures/AlgebraicGeometry/FieldBaseChangeDimension.lean:104`, which is already attached to `lem-pc-dim-base-change`. These are source observations, not a renewed ATTACH claim or an assertion about what the server has compiled. No Lean was written or compiled.

## WANTED

None. The Stacks sources used are present locally.

## Faults found and changes

The item had no proof or proof dependencies. Its mathematical statement is correct and is unchanged. Tag 0BFB omits its proof and uses a geometrically integral definition, whereas the project's abelian-variety definition is proper, smooth and connected. I supplied the needed geometric connectedness from the identity section using the existing rational-point criterion, rather than assuming it from the definition. Tag 02FY is a pointwise fibre-dimension result; I used matching affine covers and the existing affine field-extension dimension theorem to prove the global equality in the exact local-ring dimension convention. This avoids silently identifying dimension at a point with the dimension of its local ring.

The current blueprint's direct-image proof (3), the inherited ancestry description, chapter and unit records were read. The scalar-extension lemma is a generic tool in the downstream abelian Tate-module rank calculation. No unit route or unit realization record was changed. `blueprint_refs.py ancestor` reports a null ancestor for this inherited chain; this existing null was retained, with the exact inherited place retained and the proof correspondence recorded in `split_report.blueprint`. Whole-blueprint searches for abelian varieties and field extension and whole-DAG tag/concept searches found the existing tools below, but no other statement of the entire item.

## Unfinished work

None in the stage-1 split. The existing dependencies remain their own items; none was changed or split again.

## Review by Q135

I read Stacks groupoids.tex Tag 0BFB (`lemma-abelian-variety-change-field`), morphisms.tex Tags 01W4 (`lemma-base-change-proper`), 01VB (`lemma-base-change-smooth`) and 02FY (`lemma-dimension-fibre-after-base-change`), varieties.tex Tag 04KV (`lemma-geometrically-connected-if-connected-and-point`), algebra.tex Tag 00P3 (`lemma-dimension-preserved-field-extension`) and properties.tex Tag 04MU (`lemma-dimension`). I also read the affine fibre-product statement in schemes.tex (01JQ) and the existing matching-cover node. There are no new nodes requiring additional sources or searches.

Step 1 uses the statements of `def-sc-group-scheme` and `def-pc-base-change`: the former supplies multiplication, inverse and identity diagrams, and the latter the fibre product and base-changed morphisms, including the induced section. For each K-scheme T, maps into the fibre product are precisely the compatible maps to A and Spec K. The group identities therefore remain identities on every T. This is an elementary universal-property verification, not a hidden group-scheme theorem.

Step 2 uses `def-sc-abelian-variety` for properness and smoothness and both independent clauses of `lem-pc-proper-base-change`. I read their statements: they assert exactly those two properties for the second projection of the fibre product, and impose no condition on the base-change map. They apply to Spec K -> Spec k for an arbitrary field extension.

Step 3 uses `def-sc-abelian-variety` for connectedness, `def-sc-group-scheme` for the k-rational identity section, and `lem-sbc-connected-rational-point-geometrically-connected`. The last node explicitly concludes connectedness after every field extension from connectedness and a section. No perfectness, algebraic closedness, separability or properness assumption is being smuggled into this invocation. Combining this with the established group structure, properness and smoothness proves exactly the first clause.

Step 4 uses `def-weil-proper-morphism`, which explicitly includes finite type in properness, and `lem-pc-dim-base-change-affine-covers`. Its statement explicitly covers every nonempty locally finite type k-scheme, asserts nonemptiness after scalar extension and gives matching covers with finite type coordinate algebras. The original identity section ensures nonemptiness. No curve or dimension-one hypothesis is required.

Step 5 uses only the affine clause of `lem-pc-dim-base-change`, whose statement explicitly gives dim(R tensor_k K) = dim R for each finite type k-algebra R; its curve clause is unused. `lem-pc-dimension-affine-open-cover` explicitly expresses the supremum of local-ring dimensions as the supremum of the dimensions of any affine-cover rings. I checked this against `def-pc-dimension` for both schemes. Replacing each summand by the equal affine dimension is elementary, and proves the second clause. Nothing is borrowed from a dependency's proof. The quotation file records the exact statement of every cited node, separately for each use.

For B1-B10: no new node, new notion, or claimed Mathlib leaf is introduced; the statement remains self-contained with its six existing definition dependencies, TeX is singly escaped after JSON decoding, and sources carry verified tags and labels. Existing search records were preserved. Five new searches were actually run through msearch.py (LeanSearch, Loogle, grep, and two differently phrased LeanFinder requests) and their actual returned names recorded from searches.jsonl. Results are Weierstrass constructions or individual base-change properties, not the complete abelian-variety-and-dimension theorem.

For C1-C8: each non-elementary assertion has an existing node whose statement was opened and read as above; the only elementary step is the explicit group-identity verification. All off-unit statement tools are declared in `split_report.tool_uses` with their roles; no top-level `tool_uses` was added. Proof dependencies are exactly the union of step citations. For D1-D5: no clause is repackaged as a new node, no proof is moved elsewhere, no induction or circular argument is used, and the omitted 0BFB proof is supplied. All steps are under 2000 characters.

For E1-E7: I checked trivial extension K=k, the zero-dimensional trivial abelian variety Spec k, and arbitrary transcendental or inseparable extensions. All arguments remain valid. Connectedness is not asserted to survive arbitrary scalar extension without its rational section; group schemes supply that section. The dimension nodes require finite type, supplied by properness, and nonempty schemes, supplied by the identity sections. Empty affine charts contribute bottom on both sides and do not affect the supremum. There is no disputed statement, extra hypothesis or weakened conclusion.

## Not duplicates

No new nodes were created. In particular the existing rational-point criterion, proper/smooth permanence, matching affine covers, affine dimension equality and affine-cover dimension formula were reused rather than duplicated.
