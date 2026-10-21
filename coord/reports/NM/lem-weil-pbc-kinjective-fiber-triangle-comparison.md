## Worker report

Files written:
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-kinjective-fiber-triangle-comparison.json`: statement, split into eleven proof steps; statement and hypotheses unchanged; no Mathlib match for the complete item.
- `citations.json`: thirteen exact quotations, one for every node occurrence in a proof step.
- `report.md` and the search command's `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0.

Attachments: none. I searched `lean/WeilConjectures/` for the exact blueprint tag and for K-injectivity, mapping fibres/cones, derived shifts and unit compatibility. There is no declaration stating the entire item. The project's `rightDerivedFunctorIsoKInjectives`, `rightDerivedFunctor.CommShift` and `IsTriangulated` in `CategoryTheory/DerivedCategory/RightDerivedFunctor/Triangulated.lean` supply related constructions, but do not state the specified unit-normalized fibre comparison with all three squares. `AdjunctionShift.lean` concerns a right adjoint with additional adjunction hypotheses. Neither is an exact attachment under the item's hypotheses. No source or Mathlib declaration was taken as a proved attachment merely because its body lacks a visible sorry.

WANTED: none. The required Stacks text and current blueprint are available locally.

What was wrong or incomplete: the item was an unsplit statement. The source label 090X gives K-injective two-out-of-three closure, but does not itself state the unit-normalized shift or connecting-square assertion. The proof now supplies those arguments explicitly, and is marked agent-written: Tag 05SU leaves its shift proof omitted. No statement dispute, hypothesis repair, unit-route departure or Lean signature change was needed. In particular, neither exactness of G nor enough K-injectives in B is assumed. The pre-existing total-derived node is stated for an exact functor out of K(A); the termwise additive construction preserves homotopies, shifts and cone matrices, so Q_B G is exactly of that kind, without exactness on the original abelian categories. Here RG and its universal unit were already fixed by the item's hypothesis.

Unfinished work: none in this one-level split. No Lean was written or compiled.

## Blueprint and searches

Read `dag/chapters/sec-proper-base-change.json`, `dag/units/sk-thm-properbasechange.json` and the current main-20261015 node and proof at `blueprint/sec-proper-base-change/sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.{md,proof.md}`. This item serves its paragraph beginning “Applying Rf_* to the canonical Roos triangle”; the inherited blueprint ancestry passes through direct-image-roos-normalization. The unit and chapter records are unchanged.

Whole-blueprint searches (`tools/blueprint_refs.py search`) for `K-injective`, `derived shift`, `mapping-fibre` and `unit-normalized`, together with searches over all DAG statements, found no blueprint statement equivalent to the complete item. `same_as` stays empty. The existing shift lemma and Hom-bijection leaf are reused. No nodes were created, so there are no new-versus-existing duplicate pairs.

All six searches made in this session used the prescribed msearch.py command; their exact queries and actual results are appended to the item's mathlib_searches and are logged in searches.jsonl. Two distinct LeanFinder phrasings found exact-functor descent and ordinary mappingCone comparisons. I read Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean: its context requires PreservesFiniteLimits and PreservesFiniteColimits, absent here. I read mappingCone.mapTriangleIso at HomotopyCategory/Pretriangulated.lean:441 and its map_δ calculation: these compare termwise cone triangles, and do not state the derived unit normalization or shift extension. Loogle located that ordinary triangle comparison; grep of CategoryTheory/Functor/Derived located the generic Kan-extension unit, not the full theorem. The additional LeanSearch/grep searches for K-injective cones found the definition, isomorphism invariance and injective resolutions; the required special-case closure is instead two explicit null-homotopy component calculations in the proof. All services answered successfully. Earlier searches in the copied item were retained unchanged.

## Not duplicates

No new nodes. The item neither restates an existing blueprint node nor exports any of its clauses to a new node. Existing `lem-weil-pbc-kinjective-shift`, `lem-weil-pbc-kinjective-hom-derived`, `lem-weil-pbc-kinjective-total-derived` and the three cited definition nodes carry the facts used.

## Review by NM

I read the complete sections B–E of coord/delivery-errors.md, the stage-1 brief and stage document, the three levels of SETUP.md, and GOAL.md. I reviewed the local source `literature/stacks-project/derived.tex`: definition-K-injective (070H), lemma-K-injective (070I), lemma-triangle-K-injective (090X), lemma-K-injective-defined (070Y), lemma-enough-K-injectives-implies (070K), and lemma-derived-shift (05SU); tags were checked against tags/tags. The blueprint's comparison paragraph is implemented through the chosen Roos fibre model, rather than by an unspecified TR3 cone completion.

Step 1 uses the actual statement of def-weil-pbc-additive-functor, which asserts preservation of addition. From the biproduct identities I wrote out the induced biproduct isomorphism, preservation of negatives and the homotopy equation. These are finite algebraic identities, not an assertion of exactness.

Steps 2–3 prove just the needed cone closure, rather than hiding it behind a definition. Writing a map from an acyclic N as (a,b), the null-homotopy b=ds+sd leaves a+us as a map to P[-1]. The cited lem-weil-pbc-kinjective-shift explicitly says every integer shift of a K-injective is K-injective, so a+us=-dt+td has the needed solution. The displayed equality for (t,s) checks the first component's minus sign and both component types. The primed argument uses the stated K-injectivity of P'; G(H) uses the explicit preservation hypothesis. This is a pair of two-line consequences of the definition and the existing shift lemma, hence not a new node.

Step 4 uses the computing-object clause of lem-weil-pbc-kinjective-total-derived and the shift lemma; I opened both nodes and checked those statements, including invertibility at I[1]. The formula s_I=eta_I[1] eta_{I[1]}^{-1} gives the required orientation. The unit's naturality at v and v[1] gives the naturality equation by cancellation, with its substitutions written out.

Step 5 cites lem-weil-pbc-kinjective-hom-derived for its actual Hom bijection from the homotopy category to the derived category. It has no requirement that B have enough K-injectives. It therefore lifts every derived morphism between computing representatives; step 1 ensures independence of the chain representative. The localization of def-weil-abstract-derived-category, together with the given resolutions, supplies I_Z and the chosen isomorphism e_Z without assuming equality of objects in an arbitrary localization model. Step 6 checks independence of choices and naturality explicitly by conjugating a derived morphism with e_Z,e_W.

Step 7 uses the same localization statement to invert Qi, and the total-derived node only to invert eta on I and I[1]. It proves normalization even when eta_K is not invertible. I checked the two naturality substitutions in the displayed equation and the uniqueness argument on computing representatives followed by naturality at e_Z.

Step 8 uses the exact cone convention of def-weil-abstract-derived-category, which has final arrow -p, and TR2 in def-weil-triangulated-category. Its inverse rotation therefore has first arrow -(-p)[-1]=r and last arrow +i=b. This checks the potential sign ambiguity instead of changing the statement. Step 9 is the diagonal matrix calculation; its second equality uses exactly the chain-map and conjugacy hypotheses on c. Projections and inclusions give both chain-level squares by their displayed coordinates.

Step 10 cites only the actual invertibility-on-K-injectives clause of the total-derived node, the shift lemma, and the isomorphism-invariance axiom of the triangulated definition. The needed K-injectivity of H and H[1] has already been proved. I expanded all four factors of the connecting square and used eta_H^{-1}[1] sigma_{QH}=eta_{H[1]}^{-1}, then eta-naturality at b. Thus no unnormalized shift, unstated triangulatedness theorem, or noncanonical completion of the third triangle map enters the argument. The triangle is distinguished because it is isomorphic to the actual primed rotated cone triangle. Step 11 writes the exact compatibility v'c=c_tilde G(v), calculates the fibre naturality square, and then uses unit naturality to obtain both localized squares. It uses no new theorem.

For every cited node I opened and read its statement, rather than its proof or definition name alone; citations.json takes verbatim text from those statements. The six proof dependencies are the union of step uses. Shift and derived-category/triangulated definitions are Mathlib tools; the other statements are in the item's unit, so no off-route tool declaration is required. No cyclic reference to direct-image-roos-normalization or to its parent was added. No new unsplit object, literature request, or node needing duplicate or search checks was introduced.

I tested the formulas at P=0, at u=0 (H=P[-1] direct-sum P), at u=identity (contractible fibre), at the zero functor, and at G=identity and c=identity. For u=0 the residual equation becomes precisely a map to P[-1]; for u=identity the same homotopy proof still applies; for identity comparisons theta and all three localized components become the corresponding unit identifications. The formula for arbitrary K never cancels eta_K, and therefore remains valid when G is not exact and eta_K is not invertible. Every proof step is under 1000 characters, and no step above the 2000-character review threshold hides a lemma.

## Validation

The required deliver.py --no-push invocation exited 0 and printed OK (not pushed), preflight passed, at dry-run commit 06de2598578. The server ran the required DAG/split/preflight checks. No compiler or local DAG/preflight tool was run. The dry run had fully exited before the push invocation.
