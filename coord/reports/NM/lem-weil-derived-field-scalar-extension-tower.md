# Worker report: lem-weil-derived-field-scalar-extension-tower

## Files written

- `dag/nodes/sec-smooth-purity/lem-weil-derived-field-scalar-extension-tower.json`: existing statement, split into eight proof steps. No match for the complete assertion in pinned Mathlib.
- `citations.json`: verbatim statement quotations for all fifteen step/node citations.
- `report.md`: this report. The existing `searches.jsonl` records the searches made with the required command; the existing `prepare.py` is an item-local preparation script and was not rerun during recovery.

New nodes: 0. New Mathlib leaves: 0. Five existing dependencies are reused, all already marked Mathlib. The item is not the unit's key statement, so no unit realization file is changed.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint tag and scalar-extension/derived-functor terminology. The project's `WeilConjectures/Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean` supplies generic `CategoryTheory.Functor.mapDerivedCategoryNatIso` and `mapDerivedCategoryCompIso`. These do not state the complete normalized field-tower assertion, with uniqueness, unit laws, four-field coherence, and shift compatibility. A generic ingredient is not an attachment for the whole item. Upstream master is reference material only.

## WANTED

None. The shared repository has the literature manifests but not the materialized source directories. I read the existing sources under `/home/ubuntu/weil-launcher-nt/literature/` read-only.

## What was wrong or missing

The imported statement was retained verbatim. Its proof was absent, and its blueprint `same_as` field was unsearched. The preserved earlier sandbox supplied eight steps and actual Mathlib-search records; recovery audited them and tightened steps 1 and 8. Step 1 now takes the termwise induced functor and its canonical factorization directly from `lem-sf-exact-functor-derived-triangulated`, then proves inversion by naturality and inversion by Q. This avoids hiding a tensor-cohomology lemma in a claim about exactness. Step 8 now writes the fully typed complex-level shift equations, including the composite functor's two shift comparisons.

The search log contains two LeanFinder phrasings, two Loogle queries, and four grep queries, with their exact query texts preserved in the item's `mathlib_searches`. LeanSearch returned Internal Server Error and is recorded as unavailable. Online Loogle advertises newer derived-functor identity/composition APIs, absent from pinned Mathlib's ExactFunctor source. The recovery command additionally searched `mapDerivedCategoryComp|mapDerivedCategoryId|mapDerivedCategoryNat` in `Algebra/Homology/DerivedCategory` and returned zero hits. Those hits therefore do not establish a Mathlib leaf for this item. Pinned Mathlib has general localization descent and module-level scalar-extension coherence; assembling them into this derived statement requires the argument written here.

Whole-blueprint searches for `tower of fields` and `scalar extension`, and the preserved broader searches for localization and composition, found no second blueprint node stating this exact assertion. The related `lem-weil-scalar-extension-composition` concerns rationalized constructible sheaf categories over finite l-adic extensions, rather than ordinary derived categories of arbitrary fields; it does not replace this item. The existing localization universal-property node is reused rather than duplicated. Blueprint ancestry remains `def-weil-ordinary-compact-cohomology` through the two recorded intermediate definitions. The source point-category blueprint displays the finite-stage 2-colimit but does not write out this coherence proof: `proof_origin.by` is therefore `agent`. The chapter and unit route are unchanged; this unit's step list is empty.

## What could not be finished

No mathematical gap remains in this one-level split. No Lean was written, no compiler, Lake, or build was run, and no live project or launcher file was edited. The preceding attempt stopped on a shared fetch lock; this recovery reruns the required no-push delivery check. Pushing remains reserved for the next reader.

## Not duplicates

No new nodes. Identity maps, tensor balancing, differential checks, and pure-tensor associativity are elementary proof steps, not extra nodes. The general localization fact already exists. The finite-dimensional complex scalar-extension definition above this item is not cited in its proof, avoiding a dependency cycle.

## Review by NM

I reopened the item and all five cited statements, the chapter and unit records, the point-coefficient and ordinary/compact-cohomology blueprint files, and Stacks Algebra Tags 00CV (`section-tensor-product`) and 00D0 (`lemma-transitive`), Categories Tag 04VG (`lemma-properties-left-localization`), and Derived Categories Tags 05RU (`definition-unbounded-derived-category`) and 015F (`lemma-right-derived-exact-functor`). The blueprint explains the finite-stage use; the lemma itself works for arbitrary field extensions and unbounded complexes. I did not identify vector-space derived categories with constructible sheaf categories. Stacks 04VG states functor factorization, not the stronger natural-transformation assertion: the latter is explicitly stated in the reused localization node. I read pinned Mathlib `CategoryTheory/Localization/Predicate.lean:278-360` for full faithfulness, transformation descent, and equality detection, and `Algebra/Homology/DerivedCategory/ExactFunctor.lean:35-104` for the canonical factorization and its shift compatibility.

Step 1 uses the field-exactness node for its exact additive functor, the exact-functor-derived node for the induced triangulated functor, and the abstract-derived-category node for Q and its inversion of quasi-isomorphisms. Each statement says what is used. Naturality of alpha explicitly expresses Q(Ef) as a conjugate of T(Qf), so its invertibility is elementary. This repairs the earlier step's unnecessary implicit appeal to preservation of cohomology. Repeated factorizations also justify inversion for every composite needed later.

Steps 2 and 3 use the scalar-extension definition, which states functoriality on pure tensors and the natural tower isomorphism. Step 2 writes the unit map and inverse, checking the balancing relation and differential compatibility. Step 3 supplies the tower map and inverse and checks both naturality and differential compatibility on generators. These are elementary calculations with the stated tensor maps, and need no new lemma nodes.

Steps 4 and 5 use part (2) of the localization universal-property statement, including existence, component formula, invertibility, and uniqueness of descended transformations. In step 4 the target is D(K), and the two factorizations are alpha and the identity. In step 5 the target is D(M), and the composite factorization is beta = alpha_ML,E_LK C followed on its right by T_ML(alpha_LK,C), in ordinary right-to-left composition notation. Thus c_QC = alpha_MK^{-1} Q(a_C) beta_C. I checked every source and target: the unit normalization gives iota_QC alpha_KK^{-1} = Q(u_C), and the tower formula includes all conjugation factors. Step 1 verifies the inversion hypotheses; neither boundedness nor finite dimension is needed.

Steps 6 and 7 use the scalar-extension node and part (3) of the localization node, which actually states equality detection on every Q(C). The unit equations are calculated on ((v tensor lambda) tensor mu), using balancing when the intermediate field equals K. The four-field composites send ((v tensor lambda) tensor mu) tensor nu to v tensor ((lambda mu) nu) and v tensor (lambda (mu nu)). They agree by associativity. The proof records the common triple-alpha source identification and the target alpha, and invokes naturality with respect to the tower chain maps before canceling adjacent inverse factors. Thus the coherence assertion is supported by an explicit tensor calculation and the cited equality theorem, rather than an unexplained transport claim.

Step 8 uses the tensor definition for the explicit maps, the abstract-derived-category node for shifts and Q, the exact-functor node for the canonical induced triangulated functor, and the localization node for descent and equality. For every integer n the termwise shift comparison is degreewise identity, and both differentials are (-1)^n(d tensor 1). I replaced the formerly schematic shift equations with u_{C[n]} = u_C[n] s_KK and s_MK a_{C[n]} = a_C[n] s_ML E_ML(s_LK), naming the source and target of the latter. The displayed alpha/q/gamma equation defines the descended canonical shift comparison. Substitution of the unit/tower descent formulas reduces the desired shift square to the checked chain equation; localization equality detection then proves it on D(K). Being a natural isomorphism between triangulated functors alone would not suffice, and is not used as a justification.

For delivery-errors B--E, no new node conceals hypotheses, duplicates another statement, or restates a clause of the item. Each non-elementary localization operation is cited to the node that states it. All fifteen citation quotations are verbatim parts of the cited statements. The five dependencies are already Mathlib leaves, so there is no off-unit proof-route replacement or return path through this item. Small cases checked were zero complexes, a one-term vector space, either or all field inclusions equalities, shifts n=0 and n=-1, and characteristic two. All formulas are well typed in those cases and impose no finite-extension, finite-dimensionality, boundedness, or characteristic-zero condition. No statement dispute or source correction was necessary.

## Dry run

The recovery command `python3 /home/ubuntu/weil-launcher-nt/deliver.py NM lem-weil-derived-field-scalar-extension-tower --no-push` printed `OK (not pushed) deliver/NM/lem-weil-derived-field-scalar-extension-tower at 4f9293504f: preflight passed`. The former fetch-lock blocker cleared. No delivery was pushed. The same command is run again after recording this result, so the report itself is included in the final checked snapshot.

## Second reading by NM

- Item statement: checked the field-extension, arbitrary-complex, localization, identity, tower, coherence, and shift clauses against the imported blueprint source `def-weil-finite-coefficient-point` (order 1509) and the defining dependency statements; verdict: retained, with no missing hypotheses or weakened conclusion.
- Step 1: checked against `def-weil-abstract-derived-category`, `lem-sf-exact-functor-derived-triangulated`, and `lem-weil-field-scalar-extension-exact`; verdict: the exact termwise functor, induced derived functor, canonical factorization, and inversion of quasi-isomorphisms are all stated or explicitly derived by naturality.
- Step 2: checked against `def-weil-vector-space-scalar-extension` and tensor balancing; verdict: the unit and inverse are explicit degreewise chain maps, natural and differential compatible, and the step is elementary.
- Step 3: checked against `def-weil-vector-space-scalar-extension` and its tower isomorphism; verdict: the map, inverse, chain-map naturality, and differential calculation are explicit on generators, and the step is elementary.
- Step 4: checked against `lem-weil-pbc-localization-universal-property` clauses (1)--(3); verdict: the target, factorizations, normalization, invertibility, and uniqueness of the descended identity comparison are correctly typed and cited.
- Step 5: checked against the same localization statement and the explicit tower map from Step 3; verdict: the composite factorization `beta`, conjugation formula for `c`, and uniqueness/invertibility are correctly typed with all alpha factors present.
- Step 6: checked against the scalar-extension tower statement and localization equality detection; verdict: both unit equations are reduced to the displayed balancing calculation and then equality on localized objects.
- Step 7: checked against the scalar-extension tower statement and localization equality detection; verdict: both four-field composites are evaluated on generators, equal by associativity in the top field, and transferred by the cited natural-transformation extensionality.
- Step 8: checked against the scalar-extension, abstract-derived-category, exact-derived-functor, and localization statements; verdict: degreewise shift comparisons, both composite shift equations, descended alpha comparison, and cancellation argument are fully written and typed for every integer shift.
- New nodes: none; B1--B7 are vacuous, and all five reused dependencies were reopened and found to be existing Mathlib leaves with matching statements.

Changes made in this second reading:

1. No node or citation text required repair after reopening every cited statement and the source records.
2. Added this per-step second-reading record, including the edge cases already tested (zero and one-term complexes, equal fields, shifts `n=0` and `n=-1`, and characteristic two).
3. Confirmed that no new node, duplicate, Mathlib leaf, statement dispute, or source correction is needed; the existing five dependencies and all fifteen citation quotations remain sufficient.
