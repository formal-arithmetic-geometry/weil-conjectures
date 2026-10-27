# Worker report: lem-sp-raw-chart-scalar-counit-pasting

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-raw-chart-scalar-counit-pasting.json`: statement node, split into four steps; no Mathlib match for the whole assertion.
- `citations.json`: every proof-step citation, with the cited statement copied verbatim (the full statement retains the hypotheses and normalization clauses).
- `report.md`: this report. `searches.jsonl` was produced by the required search command.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched `lean/WeilConjectures/` by the exact blueprint id, raw-chart/scalar-counit terminology, and sum-extension/affine-adjunction terminology. The existing etale sum-adjunction and smooth-duality chart declarations do not state the coefficient-change factorization plus the raw composite scalar equation. In particular the chart duality reduction is not an attachment for this item.

## Literature and searches

WANTED: none.

I read the current unit record `sk-lem-sp-reduction`, the chapter record `sec-smooth-purity`, and the Charts paragraph of `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`. That paragraph specifies the actual sum-then-ordered-affine construction. The proof is marked agent-written because this delivery expands the categorical equations omitted there. I read Stacks `sites-cohomology.tex`, Tag 07A4 (`lemma-pullback-tensor-product`) and Tag 0G7E (`lemma-pullback-K-flat`), and `sites-modules.tex`, Tag 03EL (`lemma-tensor-product-pullback`), for the representative construction underlying the reused coherence nodes. No SGA source is used.

Mathlib searches were run only through `msearch.py`, using LeanFinder with two different phrasings, LeanSearch, Loogle and grep. The exact queries and returned summaries are appended to the inherited searches in the item; inherited results are retained. I read `CategoryTheory.Adjunction.comp_counit_app` in `Mathlib/CategoryTheory/Adjunction/Basic.lean:580-582`. It gives the composite counit formula, but not the two scalar equations or the specified right comparison. LeanFinder's second query returned `PullbackShift` constructions; reading their source shows that they change shift-index structures on adjunctions, rather than establishing this coefficient-change identity. LeanSearch's derived-adjunction factorization results likewise concern derived adjunction construction. No result is an exact match or a one-line specialization giving every clause of the item.

Whole-blueprint searches for counits, composite counits, tensor/pullback and right scalar comparisons, and whole-DAG searches for the scalar/counit and tensor-coherence notions, found the reusable nodes cited here. `blueprint_refs.py ancestor` gives `det-sp-reduction-exceptional`, through `lem-sp-chart-counit-scalar-transport`, as already recorded by the item. There is no other imported blueprint node stating this raw-chart assertion, so `same_as` remains empty.

## Corrections and unfinished work

The imported item was statement-only. Its statement, statement dependencies and all maintainer-owned fields are unchanged. There is no statement dispute or departure from the unit route. The proof uses the raw left comparison formed from the given beta and sigma, and does not identify it with a compactification comparison for the composite map. In particular it does not cite its parent `lem-sp-chart-counit-scalar-transport`, which would be circular.

Nothing remains unfinished in this stage-1 split. The reused open lemmas remain their existing DAG items. No Lean was written and no compiler or build tool was run.

## Not duplicates

No new nodes were created. In particular I reused the finite-Tate scalar/pullback square and generic derived monoidal composition comparisons instead of introducing a chart-factorization lemma, and kept the elementary naturality substitutions in the item's proof.

## Review by Q94

I checked the item against delivery-errors B through E, reading the actual cited statements rather than borrowing their proofs. There are no new-node statements or leaves to audit, and no newly asserted mathematical fact was packaged as a node. The hypotheses and categories in the item remain explicit. The cited source tags are Stacks tags with their tex labels, and the blueprint origin is the current snapshot.

For Step 1, `lem-sp-etale-ctf-chart-domain` explicitly states preservation by compact-support functors, coefficient extension, inverse image, finite Tate powers and shifts. It does not by itself identify sum extension with compact supports. I therefore also cited `lem-asd-etale-compact-support-normalization`, whose statement gives exactly that isomorphism for the actual degreewise sum functor. `sk-def-sfb-dc-setting` supplies a compactification with middle scheme still in the standing setting. The normalization assumes Noetherian schemes: finite type over the field verifies this using `lem-weil-pbc-finite-type-over-noetherian` (a field is Noetherian because its only ideals are zero and the unit ideal). All rings are finite torsion, the map is separated etale of finite type, and the input objects are bounded, so those hypotheses apply. This extra normalization is used only for domain preservation, not to change the raw counit.

For Step 2, I read `lem-sfb-ringed-derived-monoidal-comparisons`: it asserts the canonical composition comparison on flat-term K-flat representatives, its monoidality, and structural-ring-compatible geometric 2-isomorphism transport, without flatness assumptions. Apply it to the geometric inverse images and coefficient maps. `lem-sp-finite-tate-balanced-scalar-pullback` gives the named equality for the roots-induced Tate line, as well as the unit and common shifts, with exactly the balanced coefficient formula in this item. Its hypothesis that N is invertible holds since N is a power of ell distinct from the field characteristic; if N is 1 the coefficient rings are zero and the same maps remain defined. `lem-asd-etale-finite-twist-pullback` supplies the tensor and composition compatibility for the ordered Tate powers. `lem-weil-pbc-cochain-pullback-tensor-shift` supplies the normalized shift compatibility, including its sign convention. Combining these stated squares successively, without permuting factors, identifies the direct right comparison with h_B(a_d) after a_e. The displayed tensor calculation records which actual map is being identified; existence of an arbitrary isomorphism would not suffice. The even shift and degree-zero Tate factors introduce no extra permutation sign. This argument uses these already-stated coherence results, not a hidden new comparison lemma.

For Step 3, `lem-sp-etale-sum-counit-scalar` states exactly the equation substituted at J=G_A K, including sigma and the actual sum/evaluation counit. Step 1 verifies J is an allowed finite-Tor input. I checked the naturality square at t=a_d,K with source T_V J and target G_B T_Y K; applying P_B gives the displayed, type-correct rearrangement. Only associativity and functoriality remain after this cited equation, which is why the substitution step is elementary.

For Step 4, `lem-sp-affine-counit-scalar` states the required affine equation for the specified compactification coefficient map and ordered counit. It also explicitly includes d=0. Naturality of that same beta at v_A,J puts the expression in exactly the order needed to apply the equation. The remaining composition is the definition of w_A. This is another elementary substitution of a cited equation, with no compact-support composition theorem tacitly inserted.

I tested d=0 (unit Tate power, zero shift, identity affine adjunction), e equal to the identity, identity coefficient maps, empty U, and a nonflat coefficient quotient such as Z/ell^2 to Z/ell. The formulas reduce respectively to the sum equation, affine equation, identity comparison, zero-source equality, and the same derived-tensor calculation. In the nonflat test no resolution of B of finite length was used: the coherence statements explicitly apply to arbitrary structural ring maps and K-flat models. None of these tests changes the statement. All four proof steps are shorter than 2000 characters; none hides a standalone new lemma. I checked that every cited dependency has no path back to the item. Off-unit generic tools are declared in `split_report.tool_uses` with their purpose; they do not replace the Charts route. Citations are verbatim statement copies in `citations.json`.
