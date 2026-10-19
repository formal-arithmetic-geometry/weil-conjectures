# Worker report: def-sfb-pull-iso

1. Files written: `dag/nodes/sec-six-functors-basics/def-sfb-pull-iso.json` (definition; existing item becomes a Mathlib leaf using `CategoryTheory.conjugateIsoEquiv`, `Mathlib/CategoryTheory/Adjunction/Mates.lean:425`, and `CategoryTheory.Adjunction.comp`, `Mathlib/CategoryTheory/Adjunction/Basic.lean:567`); `report.md`; `citations.json` (empty); genuine search records in `searches.jsonl`. Zero new nodes; one Mathlib leaf, the item itself.
2. Attachments: none. The repeated project-source search by blueprint id, `pullIso`, `conjugatePullIso`, and the scalar-extension/pullback notion found only `AlgebraicGeometry.ProEtale.sheafExtendScalarsCompUpperStarIso`, `WeilConjectures/SixFunctors/ProEtale/ScalarExtension.lean:68`. Its ordinary commutative ring types and ModuleCat-valued sheaves do not state this comparison for arbitrary condensed rings and internal module objects. Master `CondensedRing.pullIso` is reference material, not evidence of a finished proof.
3. WANTED: none.
4. Fault corrected: the refused landing cited a dependency whose statement had changed after review. I re-read all five current dependency statements, expanded the description of the module functors in `mathlib_match.how`, replaced the stale review summary, and recorded this current citation audit. The item statement itself still agrees verbatim with the current imported item and the main-20261015 source. No mathematical statement correction was required. Earlier exploratory searches and their invalid Loogle pattern remain honestly recorded; the successful exact-name and semantic searches establish the match.
5. Unfinished: no mathematical work within this one-level item. Its construction dependencies retain their own stage-1 work. The repaired sandbox is for the fresh second reader; this worker runs only no-push validation and does not deliver. No Lean writing, compiler, Lake or build is authorized or used. This item is not the key statement of its unit, so it changes no unit realization.

## Return repair: changed dependency

The return asked to rebase onto the current DAG and revalidate `sk-def-sfb-module-pushforward-pullback`. The retained item still cites the same five ids as the current imported item. I read the current dependency in `dag/nodes/sec-proetale-coefficients/`, including its expanded references to the four finite abelian-sheaf functor/monoidal definitions, and compared its clauses with the main-20261015 source `_section.md`. The source's missing aggregate finite-functor reference is resolved by those explicit component references. Its pushforward is still restriction along eta_f after transport of the abelian direct image; its pullback is still extension along alpha_f after transport of the abelian inverse image. Its statement says:

> - the *adjunction* $f^*\dashv f_*$: the lift of the monoidal adjunction
>   $f^*_{\Ab}\dashv f^{\Ab}_*$ to module objects, composed with
>   $\operatorname{Ext}_{\alpha_f}\dashv\operatorname{Res}_{\alpha_f}$, using that
>   $\eta_f$ is the mate of $\alpha_f$;

This supplies precisely the underived adjunction used once for Lambda and once for Lambda_prime. The changed composition-comparison material is not an input to this item. The dependency assumes an arbitrary scheme morphism and a general commutative condensed ring, matching both required instances. I did not substitute its proof, its composition isomorphisms, or an inverse-alpha restriction construction for its stated adjunction.

The standard delivery helper assembles the sandbox's owned fields on the latest `origin/newtargets-dag`; it preserves current maintainer metadata. This is the authorized rebase mechanism, without a worker git command. Besides rebuilding the base, this repair changes the item's Mathlib specialization explanation, search records, split report, and this review. It is not an unchanged re-push.

The following hashes bind the exact UTF-8 `statement` strings read for this repair (SHA-256):

| Dependency | Statement SHA-256 |
|---|---|
| sk-def-sfb-coefficient-change | `78fac03e581bb6decd075e8393959a5badb5b127b682f5ab6e76652014dedf8e` |
| sk-def-sfb-module-pushforward-pullback | `7ec672b5cce795526cc28661ee4050d210ead7607eac1901b3c5f68ab777c833` |
| def-sfb-comap-lower-star-iso | `52806dbd8df2891503cb2213120624ce9905fa0b971a69e08e437fac4239e8c9` |
| sk-def-sfb-change-of-scalars | `fdb3fcbbc703f5c5d391af22cb269ddd037b4b4d33acee8ae24de5f9085ef9e7` |
| def-sfb-conjugate-pull-iso | `7280462f9b1e5d1bf7c9a97886b3c49c9c9eb47982001976205699431ada2be4` |

## Construction and Mathlib decision

Let A_X and A_Y be Ext_{a_X} ⊣ Res_{a_X} and Ext_{a_Y} ⊣ Res_{a_Y}; let B and B_prime be f^*_Lambda ⊣ f_{*,Lambda} and f^*_{Lambda_prime} ⊣ f_{*,Lambda_prime}. In Lean's diagrammatic notation, A_Y.comp B_prime has left adjoint Ext_{a_Y} ⋙ f^*_{Lambda_prime} and right adjoint f_{*,Lambda_prime} ⋙ Res_{a_Y}. B.comp A_X has left adjoint f^*_Lambda ⋙ Ext_{a_X} and right adjoint Res_{a_X} ⋙ f_{*,Lambda}. The supplied `def-sfb-comap-lower-star-iso` is exactly R_1 ≅ R_2 for these two adjunctions. Therefore

`(CategoryTheory.conjugateIsoEquiv (A_Y.comp B_prime) (B.comp A_X)).symm e`

constructs L_2 ≅ L_1, namely Ext_{a_X} ∘ f^*_Lambda ≅ f^*_{Lambda_prime} ∘ Ext_{a_Y}. This defines the specified conjugate, including its arrows and inverse laws, rather than selecting an arbitrary isomorphism with the right type. All specialized category and adjunction data remain the five statement dependencies. The Mathlib construction takes arbitrary categories and adjunctions, so no equivalence with ordinary module-valued sheaves is needed.

I read `Mates.lean:400-435`, especially the declaration at 425 and inverse construction at 430-435, and `Basic.lean:555-579`, with adjunction composition at 567. I also read master `ChangeOfCoefficients.lean:145-165` and `ChangeOfScalarsSquare.lean:200-222`; their nested definition is the same specialization with the same orientation. Master is used only for comparison. Fresh searches in this repair used `msearch.py`: the semantic query returned `conjugateIsoEquiv` and right-adjoint uniqueness comparisons; the exact Loogle query returned `conjugateIsoEquiv` and its four component lemmas; grep returned the two exact declarations and lines above. Their genuine records are copied from the search log into the node. Earlier searches already provide other phrasings and LeanSearch hits.

## Not duplicates

There are no new nodes. I repeated whole-blueprint searches with `tools/blueprint_refs.py search 'Underived (Pull)'` (only this item) and `search 'conjugate'`, plus whole-DAG searches for `pullIso` and the scalar-extension/pullback formula. The encompassing coefficient-comparisons unit has several additional comparisons; the generic conjugation definition is already cited; the derived Pull comparison uses derived functors and has additional exactness hypotheses; the composition comparisons use different functors. None is another statement of this entire specialized definition, so `blueprint.same_as` remains empty. The existing generic conjugation Mathlib leaf is reused, with no new lemma or duplicate clause.

## Review by Q03

For this repair I opened the retained node and all five current cited node statements, the current item source `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-coefficient-comparisons/def-sfb-pull-iso.md`, its chapter and unit records (steps 1 and 2), and the module-functor source `_section.md`. The item has the exact source hypotheses: arbitrary commutative condensed coefficient rings and arbitrary scheme morphism; it defines an underived module-object comparison. The unit's flatness condition belongs to its derived comparisons, and is not used here. The item continues along its unit's formal conjugation route. No SGA source is used and no Stacks lemma is imported by this purely categorical specialization.

`sk-def-sfb-coefficient-change` explicitly supplies a_X and a_Y as ring-object maps and their compatibility squares. The changed `sk-def-sfb-module-pushforward-pullback` supplies the two functors and their underived adjunction, by the verbatim clause quoted above, separately for each commutative condensed ring. `sk-def-sfb-change-of-scalars`, clause 2, defines scalar extension by the tensor coequalizer and states Ext ⊣ Res; these are the underived extension adjunctions, not the derived one in coefficient change. `def-sfb-comap-lower-star-iso` supplies Res_{a_Y} ∘ f_* ≅ f_* ∘ Res_{a_X} on Mod_{Lambda_prime_X}; these are exactly the two composite right adjoints in the displayed construction. `def-sfb-conjugate-pull-iso` says E_1 ∘ U_1 ≅ U_2 ∘ E_2; setting E_1=Ext_{a_X}, E_2=Ext_{a_Y}, U_1=f^*_Lambda, U_2=f^*_{Lambda_prime} gives the item's direction. These facts come from statements, not the cited nodes' proofs. Thus the changed dependency introduces no missing hypothesis or category identification.

I checked B1-B10: no unsplit child, new definition, hidden object, missing definition reference or duplicate is introduced; TeX and the original source are retained; the Mathlib declaration and exact read lines are given; searches are genuine, and the failed exploratory Loogle query is marked invalid. The slopmaster2 candidate remains the wrong coefficient category for an attachment. For C1-C8 and D1-D5, this is a definition with empty proof and proof_deps, so there are no numbered proof steps, hidden proof lemmas or proof citations; `citations.json` is correctly `[]`. The five statement dependencies provide each specialized input. No new edges or nodes were added, no unit route was replaced, and no clause was moved to a new node.

For E1-E7 I checked the source and target of every functor in the two composed adjunctions and the conjugation equivalence. The stated module categories, commutative coefficient rings, coefficient maps and underived adjunctions are exactly the inputs; no properness, flatness, finiteness or exactness is required by conjugation. The construction applies to identity f or a, the zero ring/module and the empty scheme, since arbitrary adjunctions and their units and counits still have the required types; no nonzero, nonempty or faithful-functor premise appears. There are no new statements whose small cases require a separate check. The change made for the return is the explicit current-dependency revalidation and documentation above, together with fresh verified searches; the mathematical definition remains the source's definition.

## Validation

The required server helper checks passed:

- `review_split`: `def-sfb-pull-iso: PASS; 0 new nodes; the item is a Mathlib leaf` (the unit realization advisory concerns the encompassing unit, not this non-key item).
- `check_dag`: `check_dag OK: no finding introduced by the sandbox or on its nodes`.

The final no-push command is `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q03 def-sfb-pull-iso --no-push`; the worker returns READY only after this command prints OK for the repaired sandbox. The current helper accepts the optional trailing `.` (rechecked by the independent second reader against its argument parser). No push is performed. The fresh second reader must reread the repaired current citations before delivery.

## Second reading by Q03

Independent review of the repaired sandbox, 2026-10-17; all five current dependency statement hashes still equal those recorded above. I read delivery-errors B–E, GOAL.md and coord/dag-sync.md. This is a definition delivered as one Mathlib leaf, with zero new nodes and zero proof steps.

- Item statement: PASS against main-20261015 `def-sfb-pull-iso.md`, its unit `_section.md` (formal input and pushforward/pullback steps), and its chapter `_section.md`; arbitrary scheme morphism, arbitrary commutative condensed coefficient map, underived module-object functors, and the specified conjugate all agree. The source has no Stacks tag to check, and this construction uses no SGA source.
- Construction input, coefficient maps: PASS against the current statement of `sk-def-sfb-coefficient-change`; it supplies both ring maps a_X and a_Y, not merely derived functors. Only its ring-map data are used here.
- Construction input, four adjunctions: PASS against the current statements of `sk-def-sfb-module-pushforward-pullback` (explicit adjunction clause, for each coefficient ring) and `sk-def-sfb-change-of-scalars` (clause 2). In particular the changed module pullback is Ext along alpha_f after the abelian inverse image, and the stated adjunction is the one used. No adjunction is inferred from an inverse-alpha replacement.
- Construction input, right-adjoint isomorphism: PASS against `def-sfb-comap-lower-star-iso`; its source is Mod_{Lambda'_X}, its target is Mod_{Lambda_Y}, and it states precisely f_{*,Lambda'} followed by Res_{a_Y} is isomorphic to Res_{a_X} followed by f_{*,Lambda} in diagrammatic notation. No fact is taken from its proof.
- Construction, conjugation: PASS against `def-sfb-conjugate-pull-iso` and pinned Mathlib `Mates.lean:425-435`, with `Basic.lean:567-574`. The adjunction A_Y.comp B_prime has right adjoint f_{*,Lambda'} followed by Res_{a_Y}; B.comp A_X has right adjoint Res_{a_X} followed by f_{*,Lambda}. Thus `.symm e` produces f^*_{Lambda} followed by Ext_{a_X} isomorphic to Ext_{a_Y} followed by f^*_{Lambda'}, exactly the specified direction and canonical conjugate, including the inverse laws. This verifies the recorded one-line specialization rather than only existence of an isomorphism.
- Proof steps and citations: none, correctly; `proof`, `proof_deps` and `citations.json` remain empty. There is no elementary step hiding a lemma and no new node restating an item clause.
- New nodes: none; B1–B7 and the new-node deletion tests have no additional object to check. The existing item retains self-contained hypotheses, five definition dependencies, original source and single-escaped TeX; Mathlib declaration, file and line are verified above.
- Duplicate and finished-Lean search: PASS. I independently searched the whole imported blueprint for `Underived (Pull)` (this item only) and `conjugate`, searched DAG declarations by `pullIso`, and opened the generic conjugation node, derived Pull node and unit statement. The generic construction is already reused; the derived node has different functors and hypotheses. Source searches in slopmaster2 by item id, `pullIso`, `conjugatePullIso` and `sheafExtendScalarsCompUpperStarIso` found only `ScalarExtension.lean:68`; I read it and its ordinary ring/ModuleCat coefficient type does not state the condensed internal-module definition. Master `ChangeOfCoefficients.lean:158-164` and `ChangeOfScalarsSquare.lean:221-222` confirm the formula and direction only; they are not treated as finished proofs.
- Edge cases and hypotheses: PASS for the zero module, zero coefficient ring, discrete field coefficients, identity f, identity a, and the empty scheme. The categorical construction remains typed in each case, and uses no cancellation, faithful functor or nonempty object. A nonflat coefficient map such as discrete Z to F_p is also allowed: the underived adjunctions exist and the conjugate remains invertible. No n occurs. Properness, flatness and finite-type hypotheses are not needed by the two Mathlib declarations.

Changes made and reasons:

- Added this independent second reading and three genuine searches, using broader mate vocabulary, a new Loogle pattern, and the inverse/composition formulas. The semantic search returned general mates, not an exact match; the record says so. Exact Loogle and pinned-source reading verify the match.
- Corrected the obsolete claim that a trailing `.` is rejected: the current authorized delivery helper explicitly filters it out. The worker's sections, mathematical statement, dependency edges and Mathlib construction are retained.
- No mathematical defect or statement dispute was found; no new node, proof step, citation, Lean file or maintainer metadata was introduced.
