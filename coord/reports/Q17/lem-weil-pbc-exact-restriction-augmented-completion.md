## Worker report

Item: lem-weil-pbc-exact-restriction-augmented-completion. Group: Q17. Stage 2,
2026-10-23 UTC. The delivery states
`CategoryTheory.ExactRestrictionAugmentedCompletion.exists_exactRestrictionAugmentedCompletion`
in `Sheaf.CategoryTheory.ExactRestrictionAugmentedCompletion`. Its sole postponed proof
is `sorry`. The item changes only in `lean`; there are no new nodes, dependency repairs,
or statement corrections.

The source read was `literature/stacks-project/sites-cohomology.tex`, Section
`section-derived-limits` (0940) and `lemma-Rf-commutes-with-Rlim` (0A07), together with
all nine steps of this node's reviewed agent-written augmentation refinement. The strict
right-derived limit is a functor on the derived category of strict towers, not an
arbitrarily selected object satisfying a Roos triangle. The module docstring records this
distinction. The helpers are aliases, existing-instance constructions, a canonical
ordinary comparison and unit, and the predicate spelling out the normalized maps of the
already recorded augmented-unit theorem. They introduce no independent mathematical notion.

Hypotheses, with both occurrences included where applicable:

| Node hypothesis | Lean rendering |
| --- | --- |
| Abelian categories A and B | Separate `Type uA`, `Type uB`, `Category.{vA}`, `Category.{vB}`, and `Abelian` binders. |
| Grothendieck: small colimits, exact filtered colimits, generator | `IsGrothendieckAbelian.{vA} A` and `IsGrothendieckAbelian.{vB} B`. Mathlib uses AB5 and a separator and supplies small colimits; choosing each actual hom universe adds no local-smallness restriction. |
| Unbounded derived categories, including strict towers | Four independent `HasDerivedCategory` binders, at `wA`, `wB`, `wTA`, `wTB`. `DerivedCategory.Q` is localization at cochain quasi-isomorphisms. |
| Countable inverse limits | `HasLimitsOfShape ℕᵒᵖ A` and `HasLimitsOfShape ℕᵒᵖ B`. Index n represents the node's n+1. |
| K-injective resolutions in A, B and their strict tower categories | `hIA`, `hIB`, `hITA`, `hITB`, each asserting a map `j : K ⟶ I` with `I.IsKInjective ∧ QuasiIso j`. No termwise injectivity or monomorphism assumption is inserted. |
| Additive exact adjunction E left adjoint to U | `E`, `U`, both `Additive`, both `PreservesFiniteLimits` and `PreservesFiniteColimits`, and specified `a : E ⊣ U`. |
| Levelwise U on strict towers | `towerMap U` is exactly `(Functor.whiskeringRight ℕᵒᵖ B A).obj U`. Its finite-limit and finite-colimit instances are existing pointwise instances. |
| Ordinary tower limits L_A, L_B | `complexLimit A`, `complexLimit B` apply Mathlib `lim` degreewise. `limitAdditive` is the existing theorem deriving additivity from binary-product preservation. |
| Supplied universal total right derived functors and comparisons | `RLA`, `RLB`, `δA`, `δB`, with `IsLeftKanExtension` (ordinary-to-derived comparison direction). The full universal property, rather than just a triangle property, is retained. |
| Additive cochain-to-strict-tower-complex functors | Quantified `TA`, `TB`, with separate `Additive` binders. |
| T respects homotopies | `hTA`, `hTB` quantify every pair of parallel cochain maps and take `Nonempty (Homotopy f g)` to `Nonempty (Homotopy (T.map f) (T.map g))`. No selected homotopy data are assumed. |
| Augmentations from constant towers | `ηA : complexConstant A ⟶ TA`, `ηB : complexConstant B ⟶ TB`. |
| Universal total left derived presentations with counits | `LTA`, `LTB`, `εA`, `εB` with `IsRightKanExtension`, exactly the universal left-derived counit convention used by the dependency. |
| Resolving classes cover every complex by an incoming quasi-isomorphism | `PA`, `PB` and `hPA`, `hPB`, with `j : P ⟶ K`, membership and `QuasiIso j`. Neither closure nor fullness of either class is assumed. |
| Counits invertible on the respective classes | `hεA`, `hεB`, each conditional on membership in its class. Invertibility on all complexes is not assumed. |
| U preserves resolving classes | `hUP : ∀ P, PB P → PA ((U.mapHomologicalComplex (.up ℤ)).obj P)`. |
| Ordinary theta natural isomorphism | `θ : TB ⋙ (towerMap U).mapHomologicalComplex (.up ℤ) ≅ U.mapHomologicalComplex (.up ℤ) ⋙ TA`. Lean composition reads left to right. |
| Theta commutes with augmentation, identifying the two constant towers | `hη`: apply levelwise U to `ηB`, then `θ.hom`; the other side is `ηA` preceded by the inverse of `NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ U) (.up ℤ)`. This is Mathlib's identity-component canonical identification, not an extra map. |

Conclusions, clause by clause:

1. `∃ γ : RLB ⋙ U.mapDerivedCategory ≅ (towerMap U).mapDerivedCategory ⋙ RLA`
   is the node's natural isomorphism gamma for every derived strict tower. It is obtained
   before quantifying TA and TB, so does not require augmented tower data.
2. The first conjunct normalizes gamma on **every** strict tower complex X:
   `D(U)(δB_X) ≫ γ_(QX)` equals the exact factor `φU.hom`, then the localized
   `ordinaryLimitIso a`, then `δA`, then `RLA(φUt.inv)`. The factors are precisely
   `mapDerivedCategoryFactors`, with all otherwise suppressed identifications displayed.
   `ordinaryLimitIso a` is constructed from `preservesLimitNatIso U` using the supplied
   ordinary adjunction. Its degree-k projections are fixed by
   `preservesLimitIso_hom_π`; it is not an arbitrary supplied limit isomorphism.
3. The next conjunct says that every gamma' with this same normalization equals gamma.
   This expresses canonicity and independence of the K-injective resolution used to
   construct it. Together with arbitrary supplied universal RL presentations, it states
   the result for every choice of universal derived pair.
4. For every augmented tower datum satisfying the quantified hypotheses, there is
   `ρ : LTB ⋙ D(U^T) ≅ D(U) ⋙ LTA`.
5. Its first conjunct is exactly the counit equation on PB. On the left, rho is followed
   by LTA of `φU.hom` and then `εA_UP`. On the right, `D(U^T)(εB_P)` is followed by
   `φUt.hom` and `Q(θ_P)`. All maps therefore have identical endpoints.
6. Every rho' satisfying that equation on PB equals rho. Thus the isomorphism is unique
   with the node's resolving-class normalization, not merely some natural isomorphism.
7. The final conjunct quantifies the maps tA, vA, tB, vB characterized by the dependency.
   `NormalizedUnit` spells out BOTH equations from
   `exists_augmentedDerivedTowerUnit`: `t_(QP) ≫ ε_P = α_P ≫ Q(η_P)` and
   `v_(QP) ≫ RL(α_P) = Q(ν_P) ≫ δ_(ΔP)`, at every complex P. Here alpha is the
   exact constant functor's `mapDerivedCategoryFactors`, beta is exactly epsilon,
   gamma in the dependency is exactly delta, and nu is `ordinaryUnit` constructed
   by mapping `constLimAdj.unit` degreewise. The dependency asserts existence and
   uniqueness of these pairs, so quantifying all pairs with these equations is the
   node's 'let c be the normalized maps', with no extra assumption or vacuous choice.
8. At every `M : DerivedCategory B`, the last equality is
   `D(U)(cB_M) ≫ γ_(LTB M) ≫ RLA(ρ_M) = cA_(D(U) M)`.
   Both c's are written literally as `v ≫ Functor.whiskerRight t RL`, rather than
   supplied as arbitrary maps or as units of a derived constant/limit adjunction.
9. Resolution independence is encoded by the universal comparisons, gamma/rho uniqueness,
   and validity for all normalized t/v pairs, arbitrary resolving classes and arbitrary
   universal derived presentations. No `HasExactProducts`, AB4-star, product-exactness,
   boundedness, or derived constant/limit adjunction hypothesis is present.

Dependency declarations read and reused:

- def-sp-abelian: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`; the functor-category Abelian instance is
  `Mathlib.CategoryTheory.Abelian.FunctorCategory`.
- def-weil-abstract-derived-category: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- def-pur-kinjective-complex: `CochainComplex.IsKInjective`,
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`. This generic Mathlib notion
  applies directly to all four abelian categories, rather than requiring sheaf objects.
- def-weil-inverse-system: `CategoryTheory.Functor.ofOpSequence` and
  `CategoryTheory.NatTrans.ofOpSequence`, `Mathlib.CategoryTheory.Functor.OfSequence`;
  the actual tower category is their `ℕᵒᵖ ⥤ C`.
- def-weil-derived-limit: `CategoryTheory.IsDerivedLimit` and `IsDerivedLimitTriangle`,
  `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`. This is the Roos-triangle
  property, explicitly not substituted for the supplied universal RL and comparison.
- lem-weil-pbc-augmented-derived-tower-unit:
  `CategoryTheory.exists_augmentedDerivedTowerUnit` and `towerAugmentation_ordinaryUnit`,
  `Sheaf.CategoryTheory.AugmentedDerivedTowerUnit`. The helper predicate is just its two
  displayed characterization equations, with its prescribed tower specialization.
- Proof imports: `CategoryTheory.Adjunction.preservesKInjectiveComplexes`,
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`;
  `CategoryTheory.Functor.mapDerivedCategory` and `mapDerivedCategoryFactors`,
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`;
  `CategoryTheory.exists_rightDerived_of_enough_isKInjective`,
  `Sheaf.CategoryTheory.KInjectiveTotalDerived`;
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`;
  `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`,
  `Sheaf.SixFunctors.OpenTensorNormalizationData`;
  `CategoryTheory.Localization.lift` and `natTrans_ext`,
  `Mathlib.CategoryTheory.Localization.Predicate`.

The existing exact-derived-adjunction helper has specialized universe binders. It is
imported as proof context only: the statement neither calls it nor imposes its universe
equalities. The fully general exact functor factorizations used in the statement have
independent source and target universes. There is no need to repair that proof helper
merely to state this node.

Edge checks before writing and during audit:

- U = identity and theta = identity recover identical normalized maps.
- TA = TB = zero with zero augmentations yields zero t and c; the final equality is zero
  on both sides, and rho is the unique normalized zero-object isomorphism.
- The zero complex and zero abelian category are included; no nonzero or nonempty class
  assumption beyond incoming resolutions is inserted.
- No epsilon or constant-tower delta component is cancelled outside a resolving class.
- No assumption on fullness or closure of PA/PB is present.
- Every complex, including unbounded and nonresolving complexes, appears in gamma's
  normalization and in both equations of NormalizedUnit. The final M is arbitrary.
- Four independent derived hom universes and independent object/hom universes for A/B
  compile. The tower category is strict functors, not a tower in the bare derived category.
- Constant functor commutation is an identity-component natural isomorphism; treating it
  as definitional equality was caught by the compiler and repaired explicitly.

Searches made using the required msearch.py wrapper:

- leanfinder: `An exact right adjoint preserves derived inverse limits of strict towers
  and the augmented derived completion unit`. Eight hits: Adjunction.derivedε,
  Adjunction.derived'_unit, Adjunction.derivedε_fac_app, Adjunction.derived_unit,
  Adjunction.derivedη, Adjunction.derived'_counit, Adjunction.derived_counit,
  Adjunction.derivedη_fac_app. These concern derived adjunctions, not the simultaneous
  left/right derived tower comparison with the augmentation normalization.
- loogle: `"IsRightKanExtension", "mapDerivedCategory"`: 0 hits.
- grep: `augmentedDerived|completionUnit|derivedLimitRestriction`: 0 Mathlib hits.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for these names and the item id:
  found `exists_augmentedDerivedTowerUnit` (used) and many specialized completion units.
  Read `ConstantCompletionEquivalence.derivedLimitRestriction` in full: it assumes
  a particular noetherian coefficient-ring completion and proves only the limit square;
  it does not state this abstract augmented-completion theorem. Its private flat-scalar
  specialization is likewise not the assigned statement.
- Direct rg of `dag/lean_names_upstream.json`, Mathlib, `lean/WeilConjectures`, and
  `lean/Sheaf` for the proposed full namespace and theorem name: no match.

The first complete server compile passed for both sandbox and actual module names in
3.3 s and 3.5 s. The final dry run and delivery results are appended below.

## Second reading by Q17

A separate self-audit reopened the node, complete module, the augmented-unit dependency,
and the signatures of all exact localization factors. The dispatcher prohibits starting
other agents, and this section does not claim an independent worker reading. The assigned
maintainer supplies the independent delivery review.

The audit matched every hypothesis and conclusion using the tables above. It found and
fixed the direction of the exact-derived comparison factors in the gamma equation:
`φU.hom` must be first and `RLA(φUt.inv)` last. It also replaced an attempted definitional
identification of constant towers by Mathlib's explicit `compConstIso`, mapped to
complexes. The resulting hη has the same source and target on both sides. Rho's equation
uses `LTA(φU.hom)` on the left and `φUt.hom` on the right. The final equation has exactly
source `D(U) M` and target `RLA(LTA(D(U) M))`. No normalization is required to be an
isomorphism at a nonresolving complex.

The audit also checked that gamma exists before any tower augmentation is supplied;
that t/v are characterized separately, as in the existing lemma; and that countable
product exactness has not entered through any binder. The helpers have real definitions
and existing-instance terms. Only the main named theorem has `sorry`, and its docstring
contains all nine proof steps with their DAG sources. No node fault or disputed statement
was found.

Validation: `deliver2.py Q17 lem-weil-pbc-exact-restriction-augmented-completion
--no-push` printed `OK (dry run): commit 3aa68bea3ef passes the preflight and
compiles; nothing pushed`. The final source, including all direct dependency imports,
compiled under both the sandbox name and its actual library module name. The current
blueprint source `main-20261015/.../def-weil-pbc-completed-pullback.md` was also opened:
its final sentence identifies the comparison from ordinary pullback with the completion
map, as required by this node's ancestor route.
