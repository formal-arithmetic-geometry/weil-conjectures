/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import WeilConjectures.TraceFormula.Statement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import WeilConjectures.TraceFormula.CompactCohomology

/-!
# The model compact-support comparison and the proper unit

Source: `WeilConjectures/TraceFormula/CompactCohomology.lean`,
`weilLowerShriekFrobeniusComparison`, `weilCompactCohomology`, and
`WeilBoundedConstructible.globalOperator`; blueprint `sec-zeta-weil`,
`sk-thm-rationality` (blueprint: lem-zl-model-compact-comparison-unit).

All functors below are the actual bounded constructible internal-module functors over
`Profinite.padicAlgClRingObj ℓ`. The proper comparison and composition isomorphisms are
those of the chosen-compactification construction, including its independence comparisons.
The helpers only name the arrows occurring in the statement; their data are explicit.
The comparison for the trivial square is identified with the published `compactPullback`;
its naturality and the global-operator formula then follow from the existing functor API.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The proper-unit natural transformation on compact supports, with factors in the order
unit, inverse proper comparison, inverse composition comparison, and `h ≫ a_X = a_X`.
Source: `TraceFormula/CompactCohomology.lean`, the four final factors of
`weilLowerShriekFrobeniusComparison`
(blueprint: lem-zl-model-compact-comparison-unit). -/
noncomputable def compactSupportProperUnit (h : X ⟶ X) [IsProper h.left] :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight
      (boundedConstructibleUpperStarLowerStarAdjunction
        (Profinite.padicAlgClRingObj ℓ) ℓ h).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (Functor.whiskerRight
          (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ h).inv _ ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ h (toPoint X)).inv ≫
        (eqToIso (congrArg
          (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ)
          (comp_toPoint h))).hom)

private theorem compactSupportProperUnit_eq_compactPullback (h : X ⟶ X)
    [IsProper h.left] : compactSupportProperUnit ℓ h = compactPullback ℓ h := by
  ext M
  simp only [compactSupportProperUnit, compactPullback_app,
    boundedConstructibleLowerShriekCompToPoint_hom_app, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app, Category.id_comp]

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] [algClosure : IsAlgClosure k₀ k]
  {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)}
  [LocallyOfFiniteType f₀] [qcModel : QuasiCompact f₀] [sepModel : IsSeparated f₀]
  {π : X.left ⟶ X₀} {Φ : X ⟶ X}

/-- The proper unit for the actual `r`-th model-Frobenius iterate. Finiteness is supplied
by the published model-Frobenius theorem, rather than imposed as an extra hypothesis.
Source: `TraceFormula/CompactCohomology.lean`, `IsModelFrobenius.isFinite` and the proper-unit
recipe (blueprint: lem-zl-model-compact-comparison-unit). -/
noncomputable def modelCompactProperUnit (hΦ : IsModelFrobenius Φ f₀ π) (r : ℕ) :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (frobeniusIterate Φ r) ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) :=
  letI := hΦ.isFinite r
  compactSupportProperUnit ℓ (frobeniusIterate Φ r)

/-- The specified model comparison with the canonical identity pullback on `Spec k`
removed by precomposition with its inverse, including the right unitor.
Source: `TraceFormula/CompactCohomology.lean`, `weilLowerShriekFrobeniusComparison`
(blueprint: lem-zl-model-compact-comparison-unit). -/
noncomputable def modelCompactComparisonWithoutIdentity
    (hΦ : IsModelFrobenius Φ f₀ π) (r : ℕ) :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (frobeniusIterate Φ r) ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) :=
  letI := hΦ.isFinite r
  letI := hΦ.isUniversalHomeomorphism r
  (Functor.isoWhiskerLeft _
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)) ≪≫
    Functor.rightUnitor _).inv ≫
      (weilLowerShriekFrobeniusComparison ℓ (frobeniusIterate Φ r)
        (𝟙 (point k)) (toPoint X) (isPullback_toPoint X) (frobeniusIterate Φ r)
        (Category.comp_id _) (comp_toPoint _)).hom

/-- The actual `globalOperator` of an arbitrary Weil object for the `r`-th model iterate,
viewed as its first iterate. Only finiteness and universal homeomorphism instances are
installed; the operator is the published implementation, with its carrier casts.
Source: `TraceFormula/CompactCohomology.lean`, `WeilBoundedConstructible.globalOperator`
(blueprint: lem-zl-model-compact-comparison-unit). -/
noncomputable def modelCompactGlobalOperator (hΦ : IsModelFrobenius Φ f₀ π) (r : ℕ)
    (K : WeilBoundedConstructible ℓ (frobeniusIterate Φ r)) :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier ⟶
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier :=
  letI : IsFinite (frobeniusIterate (frobeniusIterate Φ r) 1).left :=
    (frobeniusIterate_one (frobeniusIterate Φ r)) ▸ hΦ.isFinite r
  letI : IsUniversalHomeomorphism (frobeniusIterate (frobeniusIterate Φ r) 1).left :=
    (frobeniusIterate_one (frobeniusIterate Φ r)) ▸ hΦ.isUniversalHomeomorphism r
  K.globalOperator 1

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
include algClosure qcModel sepModel in
/-- The specified comparison is the proper-unit map, naturally in the coefficient complex,
and the actual global operator is this unit followed by compact pushforward of the Weil map.
Source: `TraceFormula/CompactCohomology.lean`, `weilLowerShriekFrobeniusComparison`,
`weilCompactCohomology`, and `WeilBoundedConstructible.globalOperator`
(blueprint: lem-zl-model-compact-comparison-unit).

Proof:
1. Use the actual module-object categories and the restricted pullback/direct-image
adjunction of `sk-def-sfb-dc-restricted-functors`. The functor P is the chosen-compactification
lower shriek of `sk-def-sfb-dc-lower-shriek`. `compactSupportProperUnit` names precisely
P applied to the unit, the inverse proper comparison, inverse composition, and equality map.
2. The published `IsModelFrobenius.isFinite` and
`IsModelFrobenius.isUniversalHomeomorphism` supply all iterate instances. Finiteness
gives properness by `lem-weil-pbc-finite-proper`. The iterates are over the base,
giving `comp_toPoint`.
3. Apply the published identity-removal theorem for the trivial-square specialization
of `weilLowerShriekFrobeniusComparison`, giving `compactPullback`. Its explicit formula
is the four-factor proper unit, with the same chosen-compactification comparisons.
4. Naturality is the naturality of the proper-unit natural transformation. Use
`WeilBoundedConstructible.globalOperator_eq` to remove the carrier casts. The first
iterated structure is `frobeniusCoefficientIterate_one`, namely the original structure
with its domain cast. Rewrite the first iterate and cancel that cast. No trace, duality,
Galois action, or adic comparison is used.
-/
theorem modelCompactComparison_eq_properUnit
    (hΦ : IsModelFrobenius Φ f₀ π) (r : ℕ) (hr : 1 ≤ r) :
    modelCompactComparisonWithoutIdentity ℓ hΦ r = modelCompactProperUnit ℓ hΦ r ∧
      (∀ (M N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (v : M ⟶ N),
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map v ≫
            (modelCompactProperUnit ℓ hΦ r).app N =
          (modelCompactProperUnit ℓ hΦ r).app M ≫
            (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
                (frobeniusIterate Φ r)).map v)) ∧
      (∀ K : WeilBoundedConstructible ℓ (frobeniusIterate Φ r),
        modelCompactGlobalOperator ℓ hΦ r K =
          (modelCompactProperUnit ℓ hΦ r).app K.carrier ≫
            (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
              K.str.hom) := by
  have : IsFinite (frobeniusIterate Φ r).left := hΦ.isFinite r
  have : IsUniversalHomeomorphism (frobeniusIterate Φ r).left :=
    hΦ.isUniversalHomeomorphism r
  have hproper : modelCompactProperUnit ℓ hΦ r = compactPullback ℓ (frobeniusIterate Φ r) :=
    compactSupportProperUnit_eq_compactPullback ℓ _
  refine ⟨?_, ?_, ?_⟩
  · rw [hproper]
    apply NatTrans.ext
    funext M
    simpa only [modelCompactComparisonWithoutIdentity, NatTrans.comp_app,
      Iso.trans_inv, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
      Functor.rightUnitor_inv_app, Category.id_comp] using
      boundedConstructibleUpperStarId_inv_app_comp_weilLowerShriekFrobeniusComparison_hom_app
        ℓ (frobeniusIterate Φ r) M
  · intro M N v
    exact (modelCompactProperUnit ℓ hΦ r).naturality v
  · intro K
    have : IsFinite (frobeniusIterate (frobeniusIterate Φ r) 1).left :=
      (frobeniusIterate_one (frobeniusIterate Φ r)) ▸ hΦ.isFinite r
    have : IsUniversalHomeomorphism (frobeniusIterate (frobeniusIterate Φ r) 1).left :=
      (frobeniusIterate_one (frobeniusIterate Φ r)) ▸ hΦ.isUniversalHomeomorphism r
    rw [hproper, modelCompactGlobalOperator, WeilBoundedConstructible.globalOperator_eq,
      WeilBoundedConstructible.iterateStr_hom_eq_frobeniusCoefficientIterate,
      frobeniusCoefficientIterate_one]
    simp only [eqToHom_refl, Category.id_comp]
    have hc := compactPullback_app_congr ℓ
      (frobeniusIterate_one (frobeniusIterate Φ r)) K.carrier
    simp only [eqToHom_refl, CategoryTheory.Functor.map_id] at hc
    have hc' := (CategoryTheory.Category.comp_id _).symm.trans hc
    exact congrArg (· ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
        K.str.hom) hc'

end AlgebraicGeometry.ProEtale.CondensedRing
