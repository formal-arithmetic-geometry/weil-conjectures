# Q21: lem-sfb-derived-composition-adjunction-normalization

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-derived-composition-adjunction-normalization.json`: statement, split into six steps; not a Mathlib leaf. Its statement, statement dependencies, source, created record and blueprint ancestry are unchanged. Inherited searches and Lean candidates are retained and five actually logged searches are appended.
- `citations.json`: 15 entries, one per step/node citation, with exact statement substrings checked against the shared DAG.
- `report.md`: this report. No new nodes, no new Mathlib leaves, no unit edits.

## Attachments

None. I searched the complete `WeilConjectures/` tree for the exact blueprint tag and for derived composition/adjunction terminology, then read `RightDerivedFunctor/CompConjugate.lean`, `Comp.lean`, `Adjunction.lean` and `KInjective.lean`. `CategoryTheory.Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv` proves conjugacy, `CategoryTheory.Functor.rightDerivedFunctorCompIso'` constructs the comparison, and `CategoryTheory.Adjunction.preservesKInjectiveComplexes` proves the preservation assertion. They do not state the complete representative normalization as a theorem. I therefore make no exact attachment or claim about their transitive sorry closure; I retain the inherited candidates as candidates only.

## WANTED

None. The actual Stacks sources needed are present locally.

## What needed repair

The item was statement-only. Its missing argument is the identification of the adjoint-uniqueness comparison with the specified termwise representative, rather than existence of an abstract isomorphism. I supplied this argument explicitly instead of moving either of its clauses into a new node. No statement dispute or correction arose.

The inherited source cites Stacks 0D6E for a general categorical phenomenon although that tag itself concerns ringed topoi. The proof does not apply that theorem outside its hypotheses: it follows its adjoint-uniqueness idea and proves the general exact-left-adjoint normalization using the general Stacks pre-derived Hom formula and existing DAG tools. `proof_origin.by` is `agent` because the representative calculation is assembled here.

Blueprint searches (`blueprint_refs.py search 'K-injective'`, `'conjugate'`, and `'composition preserves'`), whole-DAG concept/tag searches, and inspection of the relevant statements found no blueprint node stating this full normalization. `same_as` remains empty. The generic KI preservation, termwise adjunction, KI Hom computation and pre-derived normalization nodes are reused. No duplicate-check pairs arise because no new node is created.

## Review by Q21

I read `coord/brief-stage1.md`, the entire B–E sections of `coord/delivery-errors.md`, stage 1, the three levels in SETUP, the worker role, GOAL and dag-sync, and the item’s chapter/unit records. I read the main-20261015 ancestor `det-sf-comp-composition-base-change.proof.md` in full, especially (3): the two refinement/base-change composites compared there need proper-direct-image composition to have the specified adjunction normalization. The item is a generic tool serving that sentence and stays on the fixed composition route. It is not the unit's key node, so no realized fields were changed.

For the item’s mathematics I read Stacks `derived.tex`: 0FND (`lemma-pre-derived-adjoint-functors-general`), 0DVC (`lemma-pre-derived-adjoint-functors`), 09T5 (`lemma-derived-adjoint-functors`), 070I (`lemma-K-injective`), 070Y (`lemma-K-injective-defined`), 070K (`lemma-enough-K-injectives-implies`), and 08BJ (`lemma-adjoint-preserve-K-injectives`), as well as `sites-cohomology.tex` 0D6E (`lemma-derived-pushforward-composition`). I read the statements of every node in every uses list, not their names alone. There are no new-node sources to review.

Step 1 uses the literal KI existence assertion of `sk-def-sfb-derived-categories`, the generic preservation theorem `lem-weil-pbc-right-adjoint-preserves-kinjective`, and the KI-isomorphism assertion of `def-sfb-right-derived-functor`. The categories are Grothendieck abelian, the functors additive and each left adjoint exact, exactly as required. Preservation is applied to b first, then a, and also to c; no exactness of the right adjoints is assumed.

Step 2 uses the actual forward/inverse hom formulas and termwise unit/counit of `lem-weil-pbc-termwise-adjunction-homotopy`, the fraction-normalization formula of `lem-pc-pre-derived-adjoint-functors-general`, and the bijection into a KI target of `lem-weil-pbc-kinjective-hom-derived`. I checked the latter is for every abelian category, not only sheaves or bounded complexes. The essentially-constant right diagram is justified by explicitly lifting the inverse of each quasi-isomorphism into J; injectivity checks the left-inverse equation and uniqueness. The left diagram is represented because the exact left adjoint inverts every quasi-isomorphism. Thus the pre-derived lemma is used with its actual hypotheses, and its formula is specialized with both identity representatives, rather than invoking an unnamed normalization theorem. All derived maps into J have homotopy representatives by the cited KI Hom bijection. The inverse direction of the pre-derived formula is the displayed Phi formula.

Step 3 uses the exact-functor clause of `sk-def-sfb-derived-categories`, the real composite adjunction of `def-weil-pbc-composite-adjunction`, and the isomorphism/bijection assertions of `def-weil-pbc-adjunction-conjugate`. I checked the direction: lambda goes from L_b L_a to L_c, so its conjugate goes from RR_c to RR_a RR_b. This defines a natural isomorphism with the specified adjunctions before any representative is claimed.

Step 4 is a direct composition of step 2’s formulas using the explicit composite hom bijection in `def-weil-pbc-composite-adjunction`. I wrote gamma as RR_a(beta_b) after beta_a, rather than silently treating the two derived-functor values as equal. Its second evaluation target C(R_b)I really is KI by step 1. Naturality of the hom bijection accounts for RR_a(beta_b).

Step 5 is the actual comparison argument. It uses the conjugate formula from `def-weil-pbc-adjunction-conjugate` and the termwise counit from `lem-weil-pbc-termwise-adjunction-homotopy`. I checked the type of u: L_b L_a R_c I to I. Transposing it termwise gives C(kappa)_I; transposing its derived class gives kappa^D beta_c. The c-counit identity used in between follows by applying step 2 to the actual counit and using the triangle identity. Comparing with step 4 gives gamma^{-1} kappa^D beta_c = Q(C(kappa)), which includes both resolution identifications. This is a routine chase with the supplied formulas, not an unproved comparison lemma hidden behind 'transport'.

Step 6 uses the canonical resolution comparisons in `def-sfb-right-derived-functor`, the hom-bijection meaning of conjugation in `def-weil-pbc-adjunction-conjugate`, and the actual composite unit/counit in `def-weil-pbc-composite-adjunction`. Naturality gives an explicit formula for every resolution K to I. Taking identity maps in the hom bijections gives the two written unit/counit equations; I checked the source/target of each composite. Hence no arbitrary adjunction on isomorphic functors enters.

For B–E I checked self-contained objects and notation, preserved the statement, and added neither a definition nor a clause-restating node. All non-elementary inputs have existing cited statements; all 15 citation quotes are literal substrings. The generic off-unit termwise and pre-derived adjunction tools are declared in `split_report.tool_uses`. The other statement tools are closed or Mathlib leaves, and the remaining inputs are definitions. I checked dependencies for circularity before writing; the server checks are recorded below. Every step is under 2000 characters (725, 1335, 643, 753, 1090, 1038), and I checked each comparison argument for a hidden independent lemma. The small steps composing existing Hom formulas remain in the proof.

Edge cases: if any category is zero, all maps reduce to the unique maps and the KI condition holds. If all three adjunctions are identities and lambda is multiplication by 2 in the Grothendieck abelian category of rational vector spaces, its conjugate and the displayed derived representative are both multiplication by 2, whereas the inverse comparison is multiplication by 1/2; this detects an incorrect identity-normalization or inverse convention. With identities and lambda the identity, both beta/gamma comparisons cancel to the identity, with no dependence on a chosen resolution. Arbitrarily unbounded complexes are allowed throughout: all targets used to compute maps are KI, and no bounded-below resolution theorem or extra monoidal structure is used.

Searches are only the prescribed msearch commands. I read their returned hits and the relevant Mathlib `CategoryTheory/Functor/Derived/Adjunction.lean` formulas at lines 96–154. Those construct a derived adjunction and its unit/counit equations, with extra derived-composite hypotheses to verify; they do not state this composition/conjugation and KI representative claim as a one-line specialization. A second semantic phrasing returns the same general formulas. The logged grep has no hits. Inherited searches are retained verbatim; the five new records reproduce actual tool/query text and results. No Lean was written and no compiler, Lake, build, local check_dag, review_split or preflight command was run. No SGA route is used.

## Unfinished work

None in this one-level split. No new frontier nodes were needed.

## Validation

The first required server dry run exited 0 with `OK (not pushed)` and preflight passed at temporary commit `72f68c16a6`. After making the citation excerpts step-specific and improving the scalar edge-case explanation, I run the required final dry run again before pushing.
