/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
public import WeilConjectures.SmoothPurity.CurrentExceptionalAdjointAdmissibility
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExchangeProjection
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage
import all WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackBoundedConstructible
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeDirectImageConstructibility
import all WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportConstructibility
import WeilConjectures.AlgebraicGeometry.Open.OpenExtensionFiniteTor
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImageSupplement
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compact.CompactSupportRefinementBaseChange
import all WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Finiteness
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifFiniteTor
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import all WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import all WeilConjectures.AlgebraicGeometry.SfAffineChartPresentation.PurityAffineChartBounds
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMorphismDualizable
import Mathlib.Lean.Meta.CongrTheorems

/-! # Adjunctions of the constructible six-functor datum

Source: latest blueprint, part-six-operations/sec-smooth-base-change/sec-sbc-uniform/
sk-thm-sbc-coefficients/fix-prop-adjunctions.md, clauses (1)--(4), and its proof
(blueprint: fix-prop-adjunctions).

Finite coefficients use the intrinsic ordinary constant-ring module derived category.
Higher coefficients use native condensed module objects. The full-subcategory lifts
below retain the ambient objects and all their morphisms. Exceptional adjunctions are
asserted on the constructible categories only.

## Main statements

- `finiteOrdinary` and `finiteExceptional`: finite-stage restrictions.
- `higherAdjunctions`: native ordinary and exceptional restrictions, including Dctf.
- `compositionAndRefinement`, `higherOrdinaryComposition`: the normalized pasting laws.
- `higherCanonicalOrdinaryComposition`, `finiteCanonicalOrdinaryComposition`: the corrected
  ordinary unit and counit (Wei Yang #1441, items 30--31) under the published compositors.
- `finiteCanonicalRefinements`, `finiteConstructibleAdjunctions`, `higherCanonicalRefinements`:
  refinement compatibility through the canonical compactification comparisons.
- `finiteOrdinaryExchange`, `higherOrdinaryExchange`: the actual ordinary exchanges.
- `compactExchangeConjugate`, `higherCompactExchangeRestriction`: whole-adjoint exchange.

The formal clauses use the existing `Adjunction.comp`, `conjugateEquiv`,
`conjugateIsoEquiv` and `mateEquiv`: the composition and refinement comparisons are
conjugates between whole adjoints. In particular invertibility is asserted only for
this conjugation, and never for arbitrary square mates.
-/

open Lean Meta in
/-- Build congruence certificates before comparing large derived-category instances.
The hidden arguments differ by proof irrelevance and by the published push/pull aliases.
Checking the entire specialization by conversion unfolds the derived constructions.
This elaborator helper constructs ordinary equality proofs, checked by the kernel. -/
private meta def ordinaryExchangeCongr : Nat → MVarId → MetaM Unit
  | 0, _ => throwError "syntactic congruence exhausted its depth"
  | n + 1, g => g.withContext do
    let (_, g) ← g.intros
    g.withContext do
      let g ← g.eqOfHEq
      let target ← instantiateMVars (← g.getType)
      let some (lt, lhs, rt, rhs) := target.heq?
        | throwError "not a heterogeneous equality: {target}"
      let lhs := lhs.consumeMData
      let rhs := rhs.consumeMData
      if lhs == rhs then
        g.assign (← mkHEqRefl lhs)
      else if (← isProp lt) && (← isProp rt) then
        g.assign (← mkAppM ``proof_irrel_heq #[lhs, rhs])
      else if lhs.isApp && rhs.isApp && lhs.getAppNumArgs == rhs.getAppNumArgs &&
          (← withReducible <| isDefEq lhs.getAppFn rhs.getAppFn) then
        let f := lhs.getAppFn
        let la := lhs.getAppArgs
        let ra := rhs.getAppArgs
        let info ← getFunInfoNArgs f la.size
        let fixed := la.zipWith (· == ·) ra
        let thm ← mkRichHCongr (← inferType f) info
          (fixedFun := true) (fixedParams := fixed) (forceHEq := true)
        let gs ← withReducible <| g.apply (thm.proof.beta #[f])
          { synthAssignedInstances := false }
        for g' in gs do
          ordinaryExchangeCongr n g'
      else
        unless ← isDefEq lhs rhs do
          throwError "nonconvertible leaf: {lhs} / {rhs}"
        g.assign (← mkHEqRefl lhs)

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false

universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.ConstructibleDatumAdjunctions

private theorem realization_constructible_iff
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    [Finite (Padic.coefficientExtensionRing l E n)]
    (T : Scheme.{u})
    (K : DerivedCategory (Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))))) :
    intrinsicFiniteTorsionConstructible l E n hn T
        ((sfIntrinsicDerivedEquivalence T (Padic.coefficientExtensionRing l E n)).functor.obj K) ↔
      ProEtale.DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) T K := by
  let A := Padic.coefficientExtensionRing l E n
  let : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let F := ProEtale.finiteCoefficientIntrinsicRealization T A
  have : F.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact T A).1
  have hc (i : ℤ) :
      IsConstructibleProEtaleModuleSheaf T A
        ((DerivedCategory.homologyFunctor _ i).obj (F.mapDerivedCategory.obj K)) ↔
      ProEtale.IsConstructible (ULift.{u + 1, u} A)
        ((DerivedCategory.homologyFunctor _ i).obj K) := by
    let e := (F.mapDerivedCategoryHomologyFunctorIso i).app K
    exact ⟨fun h ↦ (intrinsicRealization_constructible_iff T A _).mp
      (intrinsicConstructible_of_iso T A e.symm h),
      fun h ↦ intrinsicConstructible_of_iso T A e
        ((intrinsicRealization_constructible_iff T A _).mpr h)⟩
  constructor
  · rintro ⟨hb, hconstructible⟩
    have hbk : DerivedCategory.TStructure.t.bounded K :=
      F.bounded_of_bounded_mapDerivedCategory_obj ((bounded_iff_finite_support _).mpr hb)
    exact ProEtale.DerivedCategory.boundedConstructible_of_homology _ hbk
      (fun i ↦ ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj _
        ((hc i).mp (hconstructible i)))
  · intro h
    have hi := ProEtale.DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic
      _ h
    exact ⟨(bounded_iff_finite_support _).mp (F.bounded_mapDerivedCategory_obj hi.1),
      fun i ↦ (hc i).mpr (hi.2 i)⟩

open AlgebraicGeometry.ProEtale.CondensedRing

/-- Reduce isomorphic native coefficients to the three standard families. The base-coefficient
identification realizes Z_l and Q_l as the degree-one integral and field cases. -/
private theorem native_induction
    (ℓ : ℕ) [Fact ℓ.Prime]
    (P : (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) →
      [MonObj Λ] → [IsCommMonObj Λ] → Prop)
    (hiso : ∀ {Λ Λ'} [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ'],
      (Mon.mk Λ ≅ Mon.mk Λ') → P Λ' → P Λ)
    (hq : P (Profinite.padicAlgClRingObj ℓ))
    (he : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      P (Profinite.continuousMapRingObj E.1))
    (ho : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      P (Profinite.padicIntegersRingObj ℓ E.1))
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsNativeExceptionalCoefficient ℓ Λ) : P Λ := by
  rcases hΛ with h | h | ⟨E, h | h⟩ | h
  · obtain ⟨e⟩ := h
    obtain ⟨_, _, _, _, _, _, _, _, q, z, _⟩ :=
      Profinite.base_coefficient_condensed_identification.{u} ℓ
    exact hiso (e ≪≫ z) (ho ⟨⊥, inferInstance⟩)
  · obtain ⟨e⟩ := h
    obtain ⟨_, _, _, _, _, _, _, _, q, z, _⟩ :=
      Profinite.base_coefficient_condensed_identification.{u} ℓ
    exact hiso (e ≪≫ q) (he ⟨⊥, inferInstance⟩)
  · obtain ⟨e⟩ := h
    exact hiso e (ho E)
  · obtain ⟨e⟩ := h
    exact hiso e (he E)
  · obtain ⟨e⟩ := h
    exact hiso e hq

/-- Transport the adic constructibility comparison through the coefficient isomorphism.
Source: fix-prop-adjunctions, Step 1, and the adic predicate comparison. -/
private theorem native_module_comparison
    (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u})
    [CompactSpace T] [IsLocallyNoetherian T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsNativeExceptionalCoefficient ℓ Λ) :
    ∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T),
      IsConstructibleModuleObject (condensedRingObj Λ T) M ↔
        IsConstantModelConstructible Λ T M := by
  apply native_induction ℓ
    (fun Λ _ _ ↦ ∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T), IsConstructibleModuleObject (condensedRingObj Λ T) M ↔
        IsConstantModelConstructible Λ T M) ?_ ?_ ?_ ?_ Λ hΛ
  · intro Λ Λ' _ _ _ _ e h
    exact comparison_transport e.symm T h
  · exact (adicConstructibilityPredicateComparison ℓ T _ .algebraicClosure).1
  · intro E
    let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
    let : NormedAlgebra ℚ_[ℓ] E.1 := ⟨fun c x ↦ by
      change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
        ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
        PadicAlgCl.norm_extends]⟩
    exact (adicConstructibilityPredicateComparison ℓ T _ (.continuous E.1)).1
  · intro E
    exact (adicConstructibilityPredicateComparison ℓ T _ (.integral E.1)).1

/-- Apply the module comparison in each cohomological degree; boundedness is unchanged.
Source: fix-prop-adjunctions, Steps 1--2. -/
private theorem native_bc_comparison
    (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u})
    [CompactSpace T] [IsLocallyNoetherian T]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsNativeExceptionalCoefficient ℓ Λ) :
    boundedConstructible (condensedRingObj Λ T) = constantModelBoundedConstructible Λ T := by
  funext K
  apply propext
  exact and_congr Iff.rfl
    (forall_congr' fun n ↦ native_module_comparison ℓ T Λ hΛ _)

/-- Exact scalar restriction preserves boundedness and transports constructible homology.
Source: fix-prop-adjunctions, Step 1, coefficient identification. -/
private theorem intrinsic_bc_coefficient
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)))
    (hK : boundedConstructible (condensedRingObj Λ T) K) :
    boundedConstructible (condensedRingObj Λ' T)
      ((shriekCoefficientTransport e T).obj K) := by
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  let φ := (upperStarFromPoint T).map e.inv.hom
  have : IsIso φ := inferInstance
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) φ
  refine ⟨F.bounded_mapDerivedCategory_obj hK.1, ?_⟩
  intro n
  exact _root_.constructible_of_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K)
    (_root_.constructible_comap φ (hK.2 n))

/-- Transport standard pushforward preservation through the canonical scalar comparison
and cancel inverse scalar equivalences. Source: fix-prop-adjunctions, Step 1. -/
private theorem native_pushforward
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsNativeExceptionalCoefficient ℓ Λ) :
    PreservesBoundedConstructiblePushforwards Λ k := by
  refine native_induction ℓ
    (fun Λ _ _ ↦ PreservesBoundedConstructiblePushforwards Λ k) ?_ ?_ ?_ ?_ Λ hΛ
  · intro Λ Λ' _ _ _ _ e H X Y _ _ _ _ _ _ f K
    have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
    letI (T : Scheme.{u}) : IsIso (coefficientMap e.inv.hom T) :=
      inferInstanceAs (IsIso ((upperStarFromPoint T).map e.inv.hom))
    letI (T : Scheme.{u}) :
        PreservesFiniteLimits (Mod.extendScalars (coefficientMap e.inv.hom T)) :=
      preservesFiniteLimits_of_natIso
        (Mod.extendScalarsIsoComapInv (coefficientMap e.inv.hom T)).symm
    let V := shriekCoefficientTransport e.symm Y.left
    let d := derivedComapLowerStarIso e.inv.hom f.left
    have h := intrinsic_bc_coefficient e.symm Y.left _
      (H f ⟨_, intrinsic_bc_coefficient e X.left K.obj K.property⟩)
    let i := V.mapIso (d.symm.app K.obj) ≪≫
      (transportCompIso e Y.left).app
        ((lowerStar Λ f.left).rightDerivedFunctor.obj K.obj)
    exact (boundedConstructible (condensedRingObj Λ Y.left)).prop_of_iso i h
  · intro X Y _ _ _ _ _ _ f K
    exact boundedConstructible_rightDerivedLowerStar_obj ℓ f K
  · intro E X Y _ _ _ _ _ _ f K
    exact ContinuousMapRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E f K
  · intro E X Y _ _ _ _ _ _ f K
    exact PadicIntegersRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E f K

/-- Restrict an adjunction across equal object properties. Reflect the left comparison
through the fully faithful inclusion; the inverse inclusion gives the right square.
Source: fix-prop-adjunctions, Steps 1--2; Adjunction.restrictFullyFaithful. -/
private def restrict_equal_adjunction
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {P P' : ObjectProperty C} {Q Q' : ObjectProperty D}
    (hP : P = P') (hQ : Q = Q')
    {F : P'.FullSubcategory ⥤ Q'.FullSubcategory}
    {G : Q'.FullSubcategory ⥤ P'.FullSubcategory} (a : F ⊣ G)
    (L : P.FullSubcategory ⥤ Q.FullSubcategory) (A : C ⥤ D)
    (eF : F ⋙ Q'.ι ≅ P'.ι ⋙ A) (eL : L ⋙ Q.ι ≅ P.ι ⋙ A) :
    L ⊣ ObjectProperty.ιOfLE (le_of_eq hQ) ⋙ G ⋙
      ObjectProperty.ιOfLE (ge_of_eq hP) := by
  let JX := ObjectProperty.ιOfLE (le_of_eq hP)
  let JY := ObjectProperty.ιOfLE (le_of_eq hQ)
  let IX := ObjectProperty.ιOfLE (ge_of_eq hP)
  let W := (ObjectProperty.fullyFaithfulι Q').whiskeringRight P.FullSubcategory
  let e : JX ⋙ F ≅ L ⋙ JY :=
    W.preimageIso (Functor.isoWhiskerLeft JX eF ≪≫ eL.symm)
  let t : JY ⋙ G ≅ (JY ⋙ G ⋙ IX) ⋙ JX :=
    NatIso.ofComponents (fun K ↦ Iso.refl _) (by
      intros
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl)
  exact a.restrictFullyFaithful (ObjectProperty.fullyFaithfulιOfLE _)
    (ObjectProperty.fullyFaithfulιOfLE _) e t

/-- Restrict the existence theorem's compactification comparison along the constructible
inclusion. The left functor retains its published compact-support object and arrow maps.
Source: fix-prop-adjunctions, Step 2, and sk-thm-existence (3)--(4). -/
private theorem native_support_ambient
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hcd : BaseFieldFiniteCD ℓ k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (hΛ : IsNativeExceptionalCoefficient ℓ Λ)
    (c : Compactification f.left) :
    Nonempty (nativeConstructibleLowerShriek Λ ℓ k hcd f hΛ ⋙
        (constantModelBoundedConstructible Λ Y.left).ι ≅
      (constantModelBoundedConstructible Λ X.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ c) := by
  classical
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have eX := (localizingClosure_ctf_equals_bc ℓ X.left Λ hΛ).1.2.2.1
  obtain ⟨hx, hy, hSX, hSY, h, sx, sy, H⟩ :=
    exceptionalInverseImage_exists Λ ℓ k hcd f (nativeCoefficient_admissible Λ ℓ hΛ)
  letI := hx
  letI := hy
  letI := sx
  letI := sy
  obtain ⟨_, _, _, _, _, hc, _, _⟩ := H
  have iX : constantModelBoundedConstructible Λ X.left ≤
      localizingClosureProEtale Λ X.left := by rwa [eX] at hSX
  obtain ⟨e⟩ := hc c
  exact ⟨Functor.isoWhiskerLeft (ObjectProperty.ιOfLE iX) e⟩

section OrdinaryExchange

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory CondensedRing.derivedUpperStarLowerStarAdjunction
  CondensedRing.pullbackSquareComparison Adjunction.exchangeRight Adjunction.homEquiv

/-- Inverse transposition of the exchange mate. Source: fix-prop-adjunctions,
proof Step 4 (blueprint: fix-prop-adjunctions). Apply the forward Hom equivalence;
its unit formula agrees with the defining exchange formula by functoriality. -/
private theorem ordinary_exchange_transpose
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    {L : B ⥤ A} {R : A ⥤ B} {L' : B' ⥤ A'} {R' : A' ⥤ B'}
    {G : B ⥤ B'} {G' : A ⥤ A'}
    (a : L ⊣ R) (a' : L' ⊣ R') (theta : G ⋙ L' ≅ L ⋙ G') (K : A) :
    ((a'.homEquiv ((R ⋙ G).obj K) (G'.obj K)).symm
      ((Adjunction.exchangeRight a a' theta).app K)) =
      theta.hom.app (R.obj K) ≫ G'.map (a.counit.app K) := by
  change ((a'.homEquiv (G.obj (R.obj K)) (G'.obj K)).symm
    ((Adjunction.exchangeRight a a' theta).app K)) = _
  rw [Equiv.symm_apply_eq, Adjunction.exchangeRight_app,
    Adjunction.homEquiv_unit, Functor.map_comp]

set_option maxHeartbeats 400000 in
-- The explicit instance congruences avoid expanding the native derived constructions.
/-- The specified ordinary condensed exchange is transposed by the stated counit
formula. It is asserted for all ambient inputs, so in particular for the bounded
constructible inputs in (1). No isomorphism assertion is made for square mates.
Source: fix-prop-adjunctions (4), proof Step 4
(blueprint: fix-prop-adjunctions).

Proof: unfold baseChangeMap, whose square comparison is the normalized composite
of pullback compositors. Inverse transpose under the f'-adjunction cancels its unit
and counit by the triangle equation, leaving theta at Rf_*K followed by g'^*epsilon_f.
The same equality restricts along the fully faithful constructible inclusions. -/
theorem higherOrdinaryExchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (K : CompactificationReindexing.D Λ X) :
    ((CondensedRing.derivedUpperStarLowerStarAdjunction.{u} Λ f').homEquiv _ _).symm
        ((CondensedRing.baseChangeMap.{u} Λ sq.toCommSq).app K) =
      (CondensedRing.pullbackSquareComparison.{u} Λ sq.toCommSq).hom.app
          ((moduleObjectDerivedPushforward Λ f).obj K) ≫
        (moduleObjectDerivedPullback Λ g').map
          ((CondensedRing.derivedUpperStarLowerStarAdjunction.{u} Λ f).counit.app K) := by
  set_option backward.defeqAttrib.useBackward false in
    dsimp only [CondensedRing.baseChangeMap]
    have h := ordinary_exchange_transpose
      (CondensedRing.derivedUpperStarLowerStarAdjunction.{u} Λ f)
      (CondensedRing.derivedUpperStarLowerStarAdjunction.{u} Λ f')
      (CondensedRing.pullbackSquareComparison.{u} Λ sq.toCommSq) K
    refine Eq.mp ?_ h
    run_tac ordinaryExchangeCongr 80 (← Lean.Elab.Tactic.getMainGoal)

end OrdinaryExchange

/-- The higher compact-support exchange on the full constructible categories is the
unique restriction of the actual proper/open compactification exchange. The inclusion
comparisons q1,q2 identify its two composite functors with their ambient composites;
no independently supplied base-change transformation is an input. Its conjugate is
between the whole right adjoints, and is invertible exactly when this exchange is.
Source: fix-prop-adjunctions (4), proof Step 4
(blueprint: fix-prop-adjunctions).

Proof: whiskering by the target fully faithful inclusion is fully faithful. Pull back
the specified ambient squareExchange along it and the two inclusion comparisons.
This uniquely determines the natural transformation. Apply conjugateEquiv to its
composite adjunctions and use compactExchangeConjugate. The mate-pasting and comparison
identities are mateEquiv_vcomp, mateEquiv_hcomp, mateEquiv_conjugateEquiv_vcomp and
conjugateEquiv_mateEquiv_vcomp. Apply them to the actual proper/open exchanges;
compactSupportRefinement_baseChange supplies their actual refinement equality.
At finite coefficients the same formal argument uses the finite origin exchange
and its refinement equality, fix-lem-exchanges (4). -/
theorem higherCompactExchangeRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {c : Compactification f} {c' : Compactification f'}
    {w : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : CompactificationReindexing.Square c c' w v)
    {F1 F2 : ProEtale.BoundedConstructible (condensedRingObj Λ X) ⥤
      ProEtale.BoundedConstructible (condensedRingObj Λ Y')}
    {R1 R2 : ProEtale.BoundedConstructible (condensedRingObj Λ Y') ⥤
      ProEtale.BoundedConstructible (condensedRingObj Λ X)}
    (a1 : F1 ⊣ R1) (a2 : F2 ⊣ R2)
    (q1 : F1 ⋙ (boundedConstructible (condensedRingObj Λ Y')).ι ≅
      (boundedConstructible (condensedRingObj Λ X)).ι ⋙
        (CompactificationReindexing.F Λ c ⋙ CompactificationReindexing.P Λ v))
    (q2 : F2 ⋙ (boundedConstructible (condensedRingObj Λ Y')).ι ≅
      (boundedConstructible (condensedRingObj Λ X)).ι ⋙
        (CompactificationReindexing.P Λ w ⋙ CompactificationReindexing.F Λ c')) :
    ∃! e : F1 ⟶ F2,
      Functor.whiskerRight e (boundedConstructible (condensedRingObj Λ Y')).ι =
        q1.hom ≫ Functor.whiskerLeft (boundedConstructible (condensedRingObj Λ X)).ι
          (CompactificationReindexing.squareExchange Λ sq) ≫ q2.inv ∧
      (∀ N, (conjugateEquiv a2 a1 e).app N =
        a1.unit.app (R2.obj N) ≫ R1.map (e.app (R2.obj N)) ≫
          R1.map (a2.counit.app N)) ∧
      (IsIso e ↔ IsIso (conjugateEquiv a2 a1 e)) := by
  let W := (ObjectProperty.fullyFaithfulι
    (boundedConstructible (condensedRingObj Λ Y'))).whiskeringRight
      (ProEtale.BoundedConstructible (condensedRingObj Λ X))
  let m := q1.hom ≫ Functor.whiskerLeft (boundedConstructible (condensedRingObj Λ X)).ι
    (CompactificationReindexing.squareExchange Λ sq) ≫ q2.inv
  refine ⟨W.preimage m, ⟨W.map_preimage m, ?_, ?_⟩, ?_⟩
  · intro N
    exact conjugateEquiv_apply_app a2 a1 _ N
  · constructor
    · intro he
      letI := he
      exact conjugateEquiv_iso a2 a1 (W.preimage m)
    · intro he
      letI := he
      exact conjugateEquiv_of_iso a2 a1 (W.preimage m)
  · intro e he
    exact W.map_injective (he.1.trans (W.map_preimage m).symm)

section OrdinaryComposition

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (H : PreservesBoundedConstructiblePushforwards Λ k)
  {X Y Z : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Restriction of the published direct-image compositor, through the fully faithful
constructible inclusions. This uses rightDerivedLowerStarComp itself.
Source: clause (3), lem-weil-derived-direct-image-composition
(blueprint: fix-prop-adjunctions). -/
def higherCanonicalDirectImageComp :
    boundedConstructibleLowerStarOfPreserves Λ H (f ≫ g) ≅
      boundedConstructibleLowerStarOfPreserves Λ H f ⋙
        boundedConstructibleLowerStarOfPreserves Λ H g :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (boundedConstructibleLowerStarOfPreservesCompatibility Λ H (f ≫ g) ≪≫
      Functor.isoWhiskerLeft _ (rightDerivedLowerStarComp Λ f.left g.left).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (boundedConstructibleLowerStarOfPreservesCompatibility Λ H f).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (boundedConstructibleLowerStarOfPreservesCompatibility Λ H g).symm ≪≫
      (Functor.associator _ _ _).symm)

private theorem restricted_unit_hom
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ Y.left)) :
    ((boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves
      (Λ := Λ) (ℓ := ℓ) (H := H) (f := f)).unit.app K).hom =
      (derivedUpperStarLowerStarAdjunction Λ f.left).unit.app K.obj := by
  simpa [boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves,
    boundedConstructibleUpperStarCompatibility,
    boundedConstructibleLowerStarOfPreservesCompatibility, ObjectProperty.liftCompιIso,
    CategoryTheory.Functor.map_id]
    using Adjunction.map_restrictFullyFaithful_unit_app
      (derivedUpperStarLowerStarAdjunction Λ f.left)
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm
      (boundedConstructibleLowerStarOfPreservesCompatibility Λ H f).symm K

private theorem restricted_counit_hom
    (N : ProEtale.BoundedConstructible (condensedRingObj Λ X.left)) :
    ((boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves
      (Λ := Λ) (ℓ := ℓ) (H := H) (f := f)).counit.app N).hom =
      (derivedUpperStarLowerStarAdjunction Λ f.left).counit.app N.obj := by
  have h := Adjunction.map_restrictFullyFaithful_counit_app
      (derivedUpperStarLowerStarAdjunction Λ f.left)
      (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
      (boundedConstructibleUpperStarCompatibility Λ ℓ f).symm
      (boundedConstructibleLowerStarOfPreservesCompatibility Λ H f).symm N
  simp only [boundedConstructibleUpperStarCompatibility,
    boundedConstructibleLowerStarOfPreservesCompatibility, ObjectProperty.liftCompιIso,
    Iso.symm_inv, Iso.refl_hom, NatTrans.id_app] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  erw [Category.id_comp] at h
  simpa only [ObjectProperty.ι_obj, ObjectProperty.ι_map,
    boundedConstructibleUpperStarLowerStarAdjunctionOfPreserves,
    boundedConstructibleUpperStarCompatibility,
    boundedConstructibleLowerStarOfPreservesCompatibility, ObjectProperty.liftCompιIso] using h

set_option maxHeartbeats 1000000 in
-- The proof compares the published restricted compositor with its ambient conjugate.
end OrdinaryComposition


/-- Finite refinement compatibility for every finite commutative coefficient ring whose
exponent is invertible on the base. The specified etale compactification comparison,
not FullCD or existence of an ambient adjoint, normalizes this relative adjunction.
Source: clause (2), proof Step 2, Wei Yang #1441 items 30--31
(blueprint: fix-prop-adjunctions).

Proof: use the etale adjunction and its canonical compactification comparisons. The
canonical site comparison is fully faithful on bounded-below etale-origin complexes.
Transport the Hom bijections along the fixed compact-support comparison at c, and
then along fixedCompactSupportOriginIso for every other compactification. Naturality,
identity and cocycle follow from those of the etale comparisons. The normalization
and comparison_homEquiv equations retain these actual maps. Restriction to the full
constructible subcategories and then Dctf preserves these bijections; transposing
identities gives the unit and counit and both triangles. Adjoint uniqueness gives
compatibility of both maps with refinement. No DVR quotient hypothesis is used. -/
theorem finiteCanonicalRefinements
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    [HasInvertibleExponent A (Spec (.of k))]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hf : f ≫ aY = aX) (c : Compactification f) :
    letI : HasCompactification f := c.hasCompactification
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
    Nonempty (ComparisonClassAdjunction A f c
      (Etale.rightDerivedUpperShriek A f)
      ((Etale.rightDerivedUpperShriekAdjunction A f).ofNatIsoLeft
        (Etale.rightDerivedLowerShriekIso A c).symm)
      (ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X)
      _root_.DerivedCategory.TStructure.t.plus) := by
  letI : HasCompactification f := c.hasCompactification
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  letI : HasInvertibleExponent A Y := .of_hom aY
  obtain ⟨z⟩ := ProEtale.nonempty_fixedComparisonClassAdjunction_of_boundedBelow A c
    (Etale.rightDerivedUpperShriek A f)
    ((Etale.rightDerivedUpperShriekAdjunction A f).ofNatIsoLeft
      (Etale.rightDerivedLowerShriekIso A c).symm)
    (fun L hL ↦ Etale.plus_rightDerivedUpperShriek_obj A f _
      (ProEtale.plus_rightDerivedFunctor_comparisonLowerStar_obj hL))
  exact ⟨{
    boundedBelow := z.boundedBelow
    homEquiv := z.homEquiv
    homEquiv_normalized := z.homEquiv_normalized
    naturality_left := z.naturality_left
    naturality_right := z.naturality_right
    comparison := z.comparison
    comparison_normalized := z.comparison_normalized
    comparison_refl := z.comparison_refl
    comparison_trans := z.comparison_trans
    comparison_homEquiv := z.comparison_homEquiv }⟩

end WeilConjectures.ConstructibleDatumAdjunctions
