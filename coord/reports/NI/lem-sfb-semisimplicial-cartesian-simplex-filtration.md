# Stage-1 delivery: lem-sfb-semisimplicial-cartesian-simplex-filtration

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-semisimplicial-cartesian-simplex-filtration.json`: statement, split; statement unchanged; eight proof steps; not a Mathlib leaf.
- No new nodes and no new Mathlib leaves. Existing DAG lemmas suffice. The finite label calculations are written in the item rather than made into elementary or duplicate nodes.
- `citations.json`: one entry per step/node citation, copied verbatim from that node's statement.
- `searches.jsonl`: actual msearch.py audit log. The item's inherited four searches were rerun with identical query text, retained, and supplemented with alternate phrasings and another directory search. Temporary preparation scripts are confined to this sandbox.

## Attachments

None. Searched the project source under `lean/WeilConjectures/` both for the exact blueprint tag and for semisimplicial/simplex filtration/Postnikov terminology. There is no project declaration stating all clauses. Ordinary simplex presentations, Godement simplex identities and a comment mentioning Postnikov truncations do not state this theorem. No compiler or Lake command was run.

## Wanted literature

None. The needed Stacks sources are present locally; the injective-map adaptation is explicitly agent-written.

## What was wrong or incomplete

The item was statement-only, with no proof. Its statement is correct and is retained byte-for-byte. A tempting construction using inverse cartesian transitions on an arbitrary representative would be wrong: these inverses exist in derived categories, not necessarily as chain maps. Instead the proof builds the coefficient simplex complex from actual transitions of a representative and compares it with the free-extension terms using the canonical direction. Only after localization are those comparisons inverted.

Stacks 0D9Q is a full-simplex statement, so it cannot simply be invoked for the semisimplicial category. I wrote the injection-only construction and the minimum-vertex contraction explicitly. The printed statement of 0D9Q also types K as an object of D(C_total) where its tensor formula requires an O-module object; our item already correctly types B in D(M). This source typo requires no change to the item.

The current blueprint is `literature/blueprint/latest/` (COMMITS.txt records latest snapshot main-20261023-1620). I read its unit `_section.md` and the direct-images proof. This item is a generic derived-descent prerequisite on the already recorded direct-image route, not a replacement for a unit step. `blueprint_refs.py ancestor` returns a null ancestor for this inherited chain; I retained that null and the existing via list and filled the precise proof realization in split_report. No unit realization fields belong to this non-key supporting node.

## Unfinished work

None for this one-level split. The pre-existing statement dependencies remain independent DAG items; no claim is made that their Lean proofs have been completed.

## Not duplicates

No new nodes were created, hence there are no new/existing pairs to justify. Searches of all imported blueprint statements for `simplex filtration`, `semisimplicial` and `Postnikov`, and all DAG nodes for 0D9B/0D9E/0D9Q, found no duplicate of the item. Existing general lemmas were reused: `lem-kun-complex-colimit-hocolim` for arbitrary ringed sites and `lem-weil-pbc-degreewise-split-derived-triangle` for split sequences. The full-simplex constant-coefficient nodes `lem-trf-total-site-free-module-resolution` and `lem-trf-total-site-simplex-free-resolution` do not themselves state the injection-only varying-ring assertion, and are not misused as if they did.

## Review by NI

I read Stacks spaces-simplicial.tex at 0D9B (lemma-simplicial-resolution-ringed), 0D9E (lemma-derived-cartesian-shriek), and 0D9Q (lemma-modules-postnikov), including their proofs. The common structure is the simplex resolution, identification of the cartesian coefficient terms, finite truncation triangles and telescope. I also read derived.tex at definition-cone, 014I/014Q and 0949 (lemma-colim-hocolim), including 0A5L (lemma-direct-sums). The proof is marked agent-written because the source is full-simplex and the finite injection complex and its contraction are an adaptation. There are no new statement-only nodes whose sources need separate review.

For Step 1 I opened `lem-sfb-semisimplicial-ringed-total-category`: its statement gives the total ring, actual systems with coherent semilinear transitions, and the exact evaluations. This licenses building labelled copies of the component modules with their actual transition maps. The two-vertex deletion cancellation is written out as the reason the horizontal boundary squares to zero; the two endpoints prove augmentation compatibility. `def-weil-abstract-derived-category` provides actual complexes and their localization. Nothing is assumed to be a cartesian chain-level isomorphism.

For Step 2 I opened `lem-sfb-semisimplicial-evaluation-free-adjoint` in full. Its statement gives the precise labelled-summand formula, exactness, the derived adjunction and counit. Thus the canonical comparison is the finite direct sum of the actual transitions, and exact pullback and cartesianness make every component a quasi-isomorphism. The total-category statement explicitly gives exact jointly conservative evaluations, so it detects that comparison as a quasi-isomorphism. This identifies objects in D(M), not just their individual cohomology groups. It is a two-line application of these existing statements, not a new projection-formula node.

Step 3 uses the total-category systems statement for transitions of the explicitly displayed finite-per-component total complex. I checked the total differential sign against the cochain-shift convention in `def-weil-abstract-derived-category`: horizontal b and signed vertical d anticommute. I proved the colimit universal property from stabilization in component m at N >= m, checking a transition to component k at N >= k. This does not assume an unstated assertion that evaluation commutes with arbitrary colimits.

Step 4 writes the contraction itself. For tuples not containing vertex 0, the prepended-vertex boundary is the original tuple plus the signed prepended proper faces, which cancel hb. For tuples containing vertex 0, the only surviving hb term is deletion and reinsertion of that initial vertex. In horizontal degree zero the remaining correction is precisely the vertex-zero projection. The vertical terms cancel because h changes horizontal parity. Hence the total augmentation is an actual homotopy equivalence in each component; the exact conservative evaluations cited really do detect its quasi-isomorphism. This is a direct labelled finite-sum computation, not an invocation of an absent semisimplicial contraction theorem or spectral sequence. It needs no boundedness and its contractions are deliberately only componentwise.

For Step 5 I read the entire statement of the existing Mathlib leaf `lem-weil-pbc-degreewise-split-derived-triangle`. The coordinate inclusions and projections really are splittings in every cochain degree in the total module category. The quotient differential has sign (-1)^(N+1), hence the quotient is the shifted A_(N+1) complex, with no unstated exactness claim. Its statement directly gives the required distinguished triangle. Transporting along the comparisons of Step 2 gives the exact X_(N+1)[N+1] objects required by the item. F_0 is defined to be X_0, rather than only said to be isomorphic to it. The augmentation commutation and counit were checked on the actual summands.

For Step 6 I compared the displayed two-column total differential with the actual cone convention in `def-weil-abstract-derived-category`. It is Cone(b_1), with first map d_0-d_1. The free-adjoint statement supplies exactly the identity-summand adjunct computation: undoing r_0 on the delta_i label gives the inverse derived transition followed by that summand's inclusion. This verifies each q_i in the imported statement, including the order q_0-q_1, rather than using an unspecified map or identifying only a boundary's cohomology class. The triangle's unspecified final map can use the convention's signed cone projection.

For Step 7 I read `lem-kun-complex-colimit-hocolim` in full. It expressly applies to arbitrary unbounded complexes of module sheaves on a site, with no monicity or boundedness requirement, and states both the coproduct and the transported telescope triangle, with the maps from each stage. The small ringed total category in the item's hypotheses is precisely a module-sheaf category to which it applies. The explicit colimit from Step 3 and actual quasi-isomorphism to B from Step 4 therefore give the required triangle and both formulas for s and p. I declared this as a generic off-unit tool use in split_report; it does not replace any part of the unit's geometric route.

For Step 8 the standard shift equivalence in the derived-category statement gives the displayed three Hom bijections. Their composite is restriction along the shifted coprojections. This checks the specific coprojections required by the statement, and needs no extra theorem about preserving coproducts.

I tested the small cases explicitly: for m=0, only p=0 occurs and the augmentation is the identity; for m=1 the edge boundary is [1]-[0] and its cone has the correct q_0-q_1 sign; for p>m every sum is empty; the zero ring and zero complex give zero diagrams; an arbitrarily unbounded constant coefficient complex still has at most m+1 horizontal columns in component m and the same h identity. The final telescope uses a countable index in the given universe, and never requires negative Hom vanishing.

I checked delivery-errors B--E against the actual node and sources. No new nodes means no hollow statement, hidden proof in a new statement, new literature tag collision, or clause relabelling. Each existing citation was opened and its statement, not its proof, is what is used; citations.json records the exact supporting portions. The only non-elementary invocations beyond the item's own supplied category/adjunction are the two existing triangle and telescope results. All other steps give their label, differential, contraction, or universal-property calculations explicitly. No step exceeds 2000 characters (the longest is 1277), and no long step hides a comparison lemma. The statement, statement dependencies, import metadata and existing blueprint ancestry are retained. No SGA source, Lean writing, build, repository write or manual git command is involved.
