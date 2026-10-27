/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.Paper.CompactSupportRepresentativeIndependence
import all Sheaf.Paper.CompactSupportReductionTower
import all Sheaf.Paper.CompactSupportCoefficientTransition
import all Sheaf.Paper.CoefficientSequenceRoosModel
import Sheaf.Paper.NormalizedDVRRoosFiniteReduction
import Sheaf.Paper.CompactSupportQuotientCocycle
import Sheaf.Paper.FiniteCompactSupportScalarComparison
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Normalized compact-support finite action

Source: blueprint order 1494, coherent strict-tower realization and rationalization
(blueprint: def-weil-compact-support-finite-action).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.proofsInPublic true

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open TensorProduct Opposite
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients

attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  coefficientSequenceEvaluation coefficientSequenceTransition constantSheaf
  Padic.coefficientExtensionIdeal compactSupportOrdinaryCoefficientTransition

open CategoryTheory.Pretriangulated in
private theorem roos_unique
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {T : ℕ → C} [HasProduct T] (t : ∀ n, T (n + 1) ⟶ T n)
    {M N : C} (p : M ⟶ ∏ᶜ T) (q : N ⟶ ∏ᶜ T)
    (δ : ∏ᶜ T ⟶ M⟦(1 : ℤ)⟧) (ε : ∏ᶜ T ⟶ N⟦(1 : ℤ)⟧)
    (hp : IsDerivedLimitTriangle t M p δ) (hq : IsDerivedLimitTriangle t N q ε) :
    ∃ e : M ≅ N, e.hom ≫ q = p := by
  let A := Triangle.mk p (towerTransitionEndomorphism t) δ
  let B := Triangle.mk q (towerTransitionEndomorphism t) ε
  let e := Pretriangulated.isoTriangleOfIso₁₂ A.rotate B.rotate
    (Pretriangulated.rot_of_distTriang A hp)
    (Pretriangulated.rot_of_distTriang B hq) (Iso.refl _) (Iso.refl _) (by simp [A, B])
  let d : A ≅ B :=
    (rotCompInvRot.app A) ≪≫ (Pretriangulated.invRotate C).mapIso e ≪≫
      (rotCompInvRot.app B).symm
  refine ⟨Triangle.π₁.mapIso d, ?_⟩
  have hd : d.hom.hom₂ = 𝟙 _ := by
    change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp
  simpa only [Functor.mapIso_hom, Triangle.π₁_map, hd, Category.comp_id, A, B,
    Triangle.mk_mor₁] using
    d.hom.comm₁.symm

open CategoryTheory.Pretriangulated in
private theorem roos_transport {C : Type*} [Category C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] {X Y : ℕ → C}
    (f : ∀ n, X (n + 1) ⟶ X n) (g : ∀ n, Y (n + 1) ⟶ Y n)
    {K L : C} (e : K ≅ L) (a : ∀ n, X n ≅ Y n)
    (p : ∀ n, K ⟶ X n) (q : ∀ n, L ⟶ Y n)
    (ht : ∀ n, f n ≫ (a n).hom = (a (n + 1)).hom ≫ g n)
    (hp : ∀ n, p n ≫ (a n).hom = e.hom ≫ q n)
    (h : ∃ hprod : HasProduct X, letI := hprod
      ∃ δ : (∏ᶜ X) ⟶ K⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle f K (Pi.lift p) δ) :
    ∃ hprod : HasProduct Y, letI := hprod
      ∃ δ : (∏ᶜ Y) ⟶ L⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle g L (Pi.lift q) δ := by
  obtain ⟨hprod, δ, hδ⟩ := h
  let := hprod
  let : HasProduct Y :=
    hasProduct_of_equiv_of_iso X Y (Equiv.refl ℕ) (fun n ↦ (a n).symm)
  let A : (∏ᶜ X) ≅ (∏ᶜ Y) :=
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc]
      inv_hom_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc] }
  refine ⟨inferInstance, A.inv ≫ δ ≫ (shiftFunctor C (1 : ℤ)).map e.hom, ?_⟩
  apply isomorphic_distinguished _ hδ _
  refine Triangle.isoMk _ _ e.symm A.symm A.symm ?_ ?_ ?_
  · change Pi.lift q ≫ A.inv = e.inv ≫ Pi.lift p
    apply Pi.hom_ext
    intro n
    simp only [A, Category.assoc, Limits.Pi.map_π, Pi.lift_π_assoc, Pi.lift_π]
    apply (cancel_mono (a n).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using (congrArg (fun k ↦ e.inv ≫ k) (hp n)).symm
  · exact (towerTransitionEndomorphism_natural_backward g f
      (fun n ↦ (a n).inv) (fun n ↦ by
        apply (cancel_mono (a n).hom).1
        simpa [Category.assoc] using
          congrArg (fun k ↦ (a (n + 1)).inv ≫ k) (ht n))).symm
  · change (A.inv ≫ δ ≫ (shiftFunctor C (1 : ℤ)).map e.hom) ≫
      (shiftFunctor C (1 : ℤ)).map e.inv = A.inv ≫ δ
    simp [Category.assoc, ← Functor.map_comp]


private theorem derivedTransition_congr
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : A ⥤ C) (R R' : C ⥤ B)
    [F.Additive] [G.Additive] [R.Additive] [R'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    (h : R = R') (τ : F ⟶ G ⋙ R) (τ' : F ⟶ G ⋙ R')
    (hτ : τ ≫ Functor.whiskerLeft G (eqToHom h) = τ') :
    CategoryTheory.derivedTransition F G R τ ≫
      Functor.whiskerLeft G.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso (eqToIso h)).hom =
      CategoryTheory.derivedTransition F G R' τ' := by
  subst R'
  simp only [eqToHom_refl, Functor.whiskerLeft_id', Category.comp_id] at hτ
  subst τ'
  change _ ≫ Functor.whiskerLeft G.mapDerivedCategory
    (Functor.mapDerivedCategoryNatIso (Iso.refl R)).hom = _
  rw [Functor.mapDerivedCategoryNatIso_refl, Functor.whiskerLeft_id', Category.comp_id]

section TowerHelpers
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private instance directQuotient_limits (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    PreservesFiniteLimits (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteLimits W _

private instance directQuotient_colimits (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    PreservesFiniteColimits (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)) :=
  proEtaleCoefficientRestrictScalars_preservesFiniteColimits W _

private def finiteRestrictionIso (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRRes l E W h ≅
      (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory :=
  by
    let : PreservesFiniteLimits (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)) :=
      proEtaleCoefficientRestrictScalars_preservesFiniteLimits W _
    let : PreservesFiniteColimits (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)) :=
      proEtaleCoefficientRestrictScalars_preservesFiniteColimits W _
    exact Functor.mapDerivedCategoryNatIso (eqToIso (compactSupportModuleRes_eq l E W h))

private theorem ordinaryTransition_app_eq (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (M : coefficientSequenceModules.{u, u} l E W) :
    (coefficientSequenceTransition.{u, u} l E W h).app M ≫
      eqToHom (congrArg
        (fun F : normalizedDVRModules l E W n ⥤ normalizedDVRModules l E W m ↦
          F.obj ((coefficientSequenceEvaluation.{u, u} l E W n).obj M))
        (compactSupportModuleRes_eq l E W h)) =
      (compactSupportOrdinaryCoefficientTransition l E W h).app M := by
  simpa only [eqToHom_refl, Category.id_comp] using
    moduleHom_eq_of_heq rfl
      (congrArg (fun F : normalizedDVRModules l E W n ⥤ normalizedDVRModules l E W m ↦
        F.obj ((coefficientSequenceEvaluation.{u, u} l E W n).obj M))
          (compactSupportModuleRes_eq l E W h))
      ((coefficientSequenceTransition.{u, u} l E W h).app M)
      ((compactSupportOrdinaryCoefficientTransition l E W h).app M)
      (fun V ↦ (transition_heq l E W M h V).trans
        (compactSupportOrdinaryCoefficientTransition_sections l E W h M V).symm)

private theorem derivedTransition_direct (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    coefficientSequenceDerivedTransition.{u, u} l E W h ≫
      Functor.whiskerLeft (coefficientSequenceDerivedEvaluation.{u, u} l E W n)
        (finiteRestrictionIso l E W h).hom =
      compactSupportCoefficientTransition l E W h := by
  let : PreservesFiniteLimits (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)) :=
    proEtaleCoefficientRestrictScalars_preservesFiniteLimits W _
  let : PreservesFiniteColimits (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)) :=
    proEtaleCoefficientRestrictScalars_preservesFiniteColimits W _
  have H := derivedTransition_congr
    (coefficientSequenceEvaluation.{u, u} l E W m) (coefficientSequenceEvaluation.{u, u} l E W n)
    (normalizedDVRModuleRes l E W h)
    (proEtaleCoefficientRestrictScalars W (compactSupportLevelQuotient l E m n h))
    (compactSupportModuleRes_eq l E W h)
    (coefficientSequenceTransition.{u, u} l E W h)
    (compactSupportOrdinaryCoefficientTransition l E W h) (by
      apply NatTrans.ext
      funext M
      simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app] using
        ordinaryTransition_app_eq l E W h M)
  unfold CategoryTheory.derivedTransition at H
  exact H

private theorem adjacentRestrictionComp (W : Scheme.{u}) (j : ℕ) :
    compactSupportRestrictionComp l E W (j + 1) j j.le_succ =
      sfCompactSupportDerivedRestrictionComp l E W j := by
  rfl

private theorem adjacentReductionMap (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E W)) (j : ℕ) :
    compactSupportReductionMap l E W (j + 1) j j.le_succ K =
      sfCompactSupportReductionTransition l E W K j := by
  rfl

private theorem adjacentQuotient (j : ℕ) :
    compactSupportLevelQuotient l E (j + 1) j j.le_succ =
      Padic.coefficientExtensionTransition l E (j + 1) := by
  rfl

private theorem finiteConstructible_iso (W : Scheme.{u}) (n : ℕ)
    {A B : proEtaleDerivedCategory W (Padic.coefficientExtensionRing l E (n + 1))}
    (e : A ≅ B)
    (h : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W A) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W B := by
  constructor
  · apply h.1.subset
    intro i hi
    exact fun hz ↦ hi (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm)
  · intro i
    have hc := h.2 i
    rw [proEtaleModuleRestriction_constructible_iff] at hc ⊢
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction W (Padic.coefficientExtensionRing l E (n + 1))).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e)) hc

private theorem constantTowerTransition_eq (W : Scheme.{u})
    (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRTowerTransition l E W D hl h =
      pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W) m n h := by
  rfl

end TowerHelpers

private theorem scalarExtension_laws
    {R : Type*} [CommRing R] {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (p : R) (F : C ⥤ D) [F.Additive] [F.Linear R] :
    (∀ K : C, (F.mapLinearMap R).baseChange (Localization.Away p)
      ((1 : Localization.Away p) ⊗ₜ[R] 𝟙 K) = (1 : Localization.Away p) ⊗ₜ[R] 𝟙 (F.obj K)) ∧
    (∀ (K L M : C) (a : Localization.Away p ⊗[R] (K ⟶ L))
        (b : Localization.Away p ⊗[R] (L ⟶ M)),
      (F.mapLinearMap R).baseChange (Localization.Away p)
        (ScalarLocalization.composition R C p K L M b a) =
      ScalarLocalization.composition R D p (F.obj K) (F.obj L) (F.obj M)
        ((F.mapLinearMap R).baseChange (Localization.Away p) b)
        ((F.mapLinearMap R).baseChange (Localization.Away p) a)) := by
  constructor
  · intro K
    change (1 : Localization.Away p) ⊗ₜ[R] F.map (𝟙 K) = _
    rw [F.map_id]
  · intro K L M a b
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul b g =>
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul a h =>
        rw [ScalarLocalization.composition_tmul]
        change (b * a) ⊗ₜ[R] F.map (h ≫ g) =
          ScalarLocalization.composition R D p (F.obj K) (F.obj L) (F.obj M)
            (b ⊗ₜ[R] F.map g) (a ⊗ₜ[R] F.map h)
        rw [ScalarLocalization.composition_tmul, F.map_comp]
      | add a a' ha ha' => simp [map_add, ha, ha']
    | add b b' hb hb' => simp [map_add, hb, hb']

section FiniteAction
variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- The exact integral-functor predicate of the already recorded strict-tower realization.
The predicate retains the chosen tower, derived limit and projection normalizations.
Naming the predicate keeps the large proof-normalized realization out of later types.
Source: blueprint order 1494, proof steps 1--4
(blueprint: def-weil-compact-support-finite-action). -/
def SfCompactSupportFiniteRealizationSpec
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    (sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y) → Prop :=
  (fun {P : (sfIntegralConstructibleCategory l E X ⥤
      sfIntegralConstructibleCategory l E Y) → Prop} (_h : ∃ F, P F) ↦ P)
    ((exists_compactSupportRepresentativeComparison l
      E K₀ hl X Y f c).choose_spec.choose_spec.2.2.choose_spec.choose_spec
        |>.2.2.choose_spec.2)

/-- The integral realization package with its exact recorded predicate.
Source: blueprint order 1494, proof steps 1--4
(blueprint: def-weil-compact-support-finite-action).
Proof: project the integral-functor conjunct after the specified tower, evaluation,
right-derived limit, unit and Roos projections in
exists_compactSupportRepresentativeComparison. Unfold the named predicate; it is
exactly the predicate in that conjunct, with no added choice or normalization. -/
theorem sfCompactSupportFiniteRealization (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    ∃ F, SfCompactSupportFiniteRealizationSpec l K₀ hl c E F := by
    run_tac Lean.Elab.Tactic.withMainContext do
      let l ← Lean.Elab.Term.elabTerm (Lean.mkIdent `l) none
      let E ← Lean.Elab.Term.elabTerm (Lean.mkIdent `E) none
      let K₀ ← Lean.Elab.Term.elabTerm (Lean.mkIdent `K₀) none
      let hl ← Lean.Elab.Term.elabTerm (Lean.mkIdent `hl) none
      let X ← Lean.Elab.Term.elabTerm (Lean.mkIdent `X) none
      let Y ← Lean.Elab.Term.elabTerm (Lean.mkIdent `Y) none
      let f ← Lean.Elab.Term.elabTerm (Lean.mkIdent `f) none
      let c ← Lean.Elab.Term.elabTerm (Lean.mkIdent `c) none
      let h ← Lean.Meta.mkAppM ``exists_compactSupportRepresentativeComparison
        #[l, E, K₀, hl, X, Y, f, c]
      let mut h := h
      let mut ty ← Lean.Meta.inferType h
      for kind in [true, true, false, false, true, true, false, false, true, false] do
        ty ← Lean.Meta.whnf ty
        let args := ty.getAppArgs
        if kind then
          unless ty.isAppOfArity ``Exists 2 do
            throwError "expected existential"
          let levels := [← Lean.Meta.getLevel args[0]!]
          let witness := Lean.mkAppN (Lean.mkConst ``Exists.choose levels) #[args[0]!, args[1]!, h]
          h := Lean.mkAppN (Lean.mkConst ``Exists.choose_spec levels) #[args[0]!, args[1]!, h]
          ty := args[1]!.beta #[witness]
        else
          unless ty.isAppOfArity ``And 2 do
            throwError "expected conjunction"
          h := Lean.mkAppN (Lean.mkConst ``And.right) #[args[0]!, args[1]!, h]
          ty := args[1]!
      ty ← Lean.Meta.whnf ty
      unless ty.isAppOfArity ``Exists 2 do
        throwError "expected existential, got {ty}"
      (← Lean.Elab.Tactic.getMainGoal).assign h


/-- The already normalized integral compact-support functor, retaining its coherent
strict-tower construction and the fixed projections of sfCompactSupportTerm.
Source: blueprint order 1494, proof steps 1--4
(blueprint: def-weil-compact-support-finite-action). -/
@[irreducible] def sfCompactSupportFiniteIntegralFunctor
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y :=
  (sfCompactSupportFiniteRealization l K₀ hl c E).choose

/-- Linearity of the fixed integral realization.
Source: blueprint order 1494, proof steps 3--4
(blueprint: def-weil-compact-support-finite-action).
Proof: project the additive and integral-linear conjuncts for the chosen integral
functor in sfCompactSupportFiniteRealization. -/
theorem sfCompactSupportFiniteIntegralFunctor_linear (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    (sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).Additive ∧
      (sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).Linear
        (Padic.coefficientExtensionIntegers l
          E) := by
  unfold sfCompactSupportFiniteIntegralFunctor
  have h := (sfCompactSupportFiniteRealization l K₀ hl c E).choose_spec
  exact ⟨h.1, h.2.1⟩

/-- The actual tensor extension of the fixed integral Hom map.
Source: blueprint order 1494, proof step 4
(blueprint: def-weil-compact-support-finite-action). -/
def sfCompactSupportFiniteHomMap (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K L : sfRationalConstructibleCategory l E X) :
    (K ⟶ L) →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer l
      E)]
      ((⟨(sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K.obj⟩ :
        sfRationalConstructibleCategory l E Y) ⟶
        (⟨(sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj L.obj⟩ :
          sfRationalConstructibleCategory l E Y)) :=
  letI := (sfCompactSupportFiniteIntegralFunctor_linear l K₀ hl c E).1
  letI := (sfCompactSupportFiniteIntegralFunctor_linear l K₀ hl c E).2
  ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).mapLinearMap
    (Padic.coefficientExtensionIntegers l
      E)).baseChange
        (Localization.Away (Padic.coefficientExtensionUniformizer l
          E))

/-- The tensor Hom map preserves identities and composition.
Source: blueprint order 1494, proof step 4
(blueprint: def-weil-compact-support-finite-action).
Proof: on pure tensors, baseChange sends a tensor v to a tensor F(v). Apply the
integral functor laws and the prescribed tensor-composition formula. Extend by
additivity in both variables, since pure tensors generate the localized Hom modules. -/
theorem sfCompactSupportFiniteHomMap_laws (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    (∀ K : sfRationalConstructibleCategory l E X,
      sfCompactSupportFiniteHomMap l K₀ hl c E K K (𝟙 K) =
        𝟙 (⟨(sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K.obj⟩ :
          sfRationalConstructibleCategory l E Y)) ∧
    (∀ (K L N : sfRationalConstructibleCategory l E X) (a : K ⟶ L) (b : L ⟶ N),
      sfCompactSupportFiniteHomMap l K₀ hl c E K N (a ≫ b) =
        sfCompactSupportFiniteHomMap l K₀ hl c E K L a ≫
          sfCompactSupportFiniteHomMap l K₀ hl c E L N b) := by
  let := (sfCompactSupportFiniteIntegralFunctor_linear l K₀ hl c E).1
  let := (sfCompactSupportFiniteIntegralFunctor_linear l K₀ hl c E).2
  exact scalarExtension_laws (Padic.coefficientExtensionUniformizer l E)
    (sfCompactSupportFiniteIntegralFunctor l K₀ hl c E) |>.imp
      (fun h K ↦ h K.obj) (fun h K L N a b ↦ h K.obj L.obj N.obj a b)

/-- The raw Hom scalar extension of the fixed integral action. Objects and all
morphisms are constructed explicitly; on pure tensors the map is a tensor F(v).
Source: blueprint order 1494, proof step 4
(blueprint: def-weil-compact-support-finite-action). -/
def sfCompactSupportFiniteFunctor (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y where
  obj K := ⟨(sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K.obj⟩
  map {K L} a := sfCompactSupportFiniteHomMap l K₀ hl c E K L a
  map_id K := (sfCompactSupportFiniteHomMap_laws l K₀ hl c E).1 K
  map_comp a b := (sfCompactSupportFiniteHomMap_laws l K₀ hl c E).2 _ _ _ a b

/-- The value equality retained in the fixed integral realization.
Source: blueprint order 1494, integral realization clause
(blueprint: def-weil-compact-support-finite-action).
Proof: project the object-normalization conjunct of the already recorded
exists_compactSupportRepresentativeComparison package used in the definition. -/
theorem sfCompactSupportFiniteIntegralFunctor_obj
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E X) :
    (sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K =
      sfIntegralCompactSupportValue l E K₀ hl c K := by
  unfold sfCompactSupportFiniteIntegralFunctor
  exact (sfCompactSupportFiniteRealization l K₀ hl c E).choose_spec.2.2.1 K

private theorem compactSupportSystem_normalized
    (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (K : sfIntegralConstructibleCategory l E X)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) :
    IsNormalizedCoefficientSequence.{u, u} l E Y
      ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.i ⋙
        ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.g).obj (S.reduction.obj K.obj)) := by
  classical
  let N : coefficientSequenceDerived.{u, u} l E Y :=
    (ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.i ⋙
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g).obj (S.reduction.obj K.obj)
  let F (n : ℕ) := sfIntrinsicCompactSupport c
    (Padic.coefficientExtensionRing l E (n + 1))
  let L (n : ℕ) := (scalarReductionDerivedExtension l E X n).obj K.obj
  let e (n : ℕ) : (coefficientSequenceDerivedEvaluation.{u, u} l E Y n).obj N ≅
      (F n).obj (L n) :=
    (compactSupportSystemEvaluation l E c n).app (S.reduction.obj K.obj) ≪≫
      (F n).mapIso ((S.reductionEvaluation n).app K.obj)
  obtain ⟨a, b, hab, hK⟩ := K.property.2
  intro m n h P
  let Rx := pbcDerivedRestrict (compactSupportLevelSheafQuotient l E X m n h)
  let Ry := pbcDerivedRestrict (compactSupportLevelSheafQuotient l E Y m n h)
  let ax := pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E X m n h)
  let ay := pbcDerivedScalarAdjunction (compactSupportLevelSheafQuotient l E Y m n h)
  let β := (ax.homEquiv _ _).symm (compactSupportReductionMap l E X m n h K.obj)
  have hβ : IsIso β := (compactSupport_quotient_cocycle l E K₀ hl c K.obj).1 m n h |>.1
  let := hβ
  have hred : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X
      ((pbcDerivedExtend (compactSupportLevelSheafQuotient l E X m n h)).obj (L m)) :=
    finiteConstructible_iso l E X n (asIso β).symm (hK n).1
  let τ := (F m).map (compactSupportReductionMap l E X m n h K.obj) ≫
    (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app (L n)
  let q := (ay.homEquiv _ _).symm τ
  let z := (ay.homEquiv _ _).symm ((F m).map (ax.unit.app (L m)) ≫
    (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
      ((pbcDerivedExtend (compactSupportLevelSheafQuotient l E X m n h)).obj (L m)))
  have hz : IsIso z := finiteCompactSupportScalarComparison l E K₀ hl
    (m + 1) (Nat.succ_pos m) (n + 1) (Nat.succ_pos n) (Nat.add_le_add_right h 1)
    f c (L m) (hK m).1 hred
  let := hz
  have hτ : τ = ((F m).map (ax.unit.app (L m)) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
        ((pbcDerivedExtend (compactSupportLevelSheafQuotient l E X m n h)).obj (L m))) ≫
      Ry.map ((F n).map β) := by
    have hn := (sfCompactSupportRestriction c
      (compactSupportLevelQuotient l E m n h)).hom.naturality β
    change (F m).map (Rx.map β) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app (L n) =
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
        ((pbcDerivedExtend (compactSupportLevelSheafQuotient l E X m n h)).obj (L m)) ≫
        Ry.map ((F n).map β) at hn
    change (F m).map (compactSupportReductionMap l E X m n h K.obj) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
        (L n) = _
    rw [Category.assoc, ← hn, ← Category.assoc, ← (F m).map_comp]
    exact congrArg (fun d ↦ (F m).map d ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app (L n))
      ((compactSupport_quotient_cocycle l E K₀ hl c K.obj).1 m n h).2
  have hqeq : q = z ≫ (F n).map β :=
    (congrArg ((ay.homEquiv _ _).symm) hτ).trans
      (ay.homEquiv_naturality_right_symm _ _)
  have hq : IsIso q := by rw [hqeq]; infer_instance
  let := hq
  have ht : (compactSupportCoefficientTransition l E Y h).app N ≫ Ry.map (e n).hom =
      (e m).hom ≫ τ := by
    have hg := compactSupportNativeSystemTransition l E c h (S.reduction.obj K.obj)
    have hd := compactSupportReductionTransition l E X S.toCoefficientDerivedSystemReduction
      h K.obj
    have H := compactSupportFiniteSquare (F m) (F n) Rx Ry
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom
      _ _ _ _ _ _ _ hg hd
    simpa only [N, τ, L, coefficientFiniteDerivedExtension, e, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom,
      Functor.map_comp, Category.assoc] using H
  let qN := (ay.homEquiv _ _).symm ((compactSupportCoefficientTransition l E Y h).app N)
  have hqN : qN ≫ (e n).hom =
      (pbcDerivedExtend (compactSupportLevelSheafQuotient l E Y m n h)).map (e m).hom ≫ q := by
    calc
      qN ≫ (e n).hom = (ay.homEquiv _ _).symm
          ((compactSupportCoefficientTransition l E Y h).app N ≫ Ry.map (e n).hom) :=
        (ay.homEquiv_naturality_right_symm _ _).symm
      _ = (ay.homEquiv _ _).symm ((e m).hom ≫ τ) := congrArg _ ht
      _ = (pbcDerivedExtend (compactSupportLevelSheafQuotient l E Y m n h)).map
          (e m).hom ≫ q := ay.homEquiv_naturality_left_symm _ _
  have : IsIso (qN ≫ (e n).hom) := by rw [hqN]; infer_instance
  have : IsIso qN := IsIso.of_isIso_comp_right qN (e n).hom
  have hb : Function.Bijective (fun g :
      (coefficientSequenceDerivedEvaluation.{u, u} l E Y n).obj N ⟶ P ↦
      (compactSupportCoefficientTransition l E Y h).app N ≫ Ry.map g) := by
    have hb := ((ay.homEquiv _ P).bijective).comp
      ((isIso_iff_coyoneda_map_bijective qN).mp inferInstance P)
    simpa only [Function.comp_def, qN, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply] using hb
  let ε := finiteRestrictionIso l E Y h
  have he : (fun g : (coefficientSequenceDerivedEvaluation.{u, u} l E Y n).obj N ⟶ P ↦
      (compactSupportCoefficientTransition l E Y h).app N ≫ Ry.map g) =
      (fun z ↦ z ≫ ε.hom.app P) ∘
        (fun g ↦ (coefficientSequenceDerivedTransition.{u, u} l E Y h).app N ≫
          (normalizedDVRRes l E Y h).map g) := by
    funext g
    have hn := ε.hom.naturality g
    dsimp only [Function.comp_apply]
    rw [Category.assoc, hn, ← Category.assoc]
    exact congrArg (fun d ↦ d ≫ Ry.map g) (NatTrans.congr_app
      (derivedTransition_direct l E Y h) N).symm
  rw [he] at hb
  exact Function.Bijective.of_comp_left (f := fun z ↦ z ≫ ε.hom.app P) hb
    (fun a b hab ↦ (cancel_mono (ε.hom.app P)).mp hab)

/-- The canonical n-th reduction comparison is the tensor/restriction adjoint of
the fixed n-th projection in the definition of sfIntegralCompactSupportValue.
Source: blueprint definition order 1490 and lem-fix-operation-reduction
(blueprint: def-weil-compact-support-finite-action). -/
def sfCompactSupportChosenReduction (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E X)
    (n : ℕ) :
    (scalarReductionDerivedExtension l E
      Y n).obj (sfIntegralCompactSupportValue l
        E K₀ hl c K).obj ⟶
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l
      E (n + 1)) c).obj
        ((scalarReductionDerivedExtension l E X n).obj K.obj) := by
  letI : HasCountableProducts (DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
    integralOperationsDerivedCountableProducts l E Y
  let h := (exists_isDerivedLimit_and_iso
    (sfCompactSupportTerm l E c K.obj) (sfCompactSupportTransition l E c K.obj)).1
  let hM : IsDerivedLimit (sfCompactSupportTransition l E c K.obj) (Classical.choose h) :=
    Classical.choose_spec h
  exact ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _).symm
    (Classical.choose hM ≫ Pi.π (sfCompactSupportTerm l E c K.obj) n)

/-- The specified projection adjunct is invertible, without an extra Tor or
finite-base-field assumption.
Source: definition order 1490; lem-fix-operation-reduction, compact-support paragraph
(blueprint: def-weil-compact-support-finite-action).
Proof: the source is the chosen derived limit of the actual compact-support tower.
Proper direct image commutes with the perfect two-term quotient tensor, and open
extension is exact and commutes with that tensor. These are the normalized unit/counit
mates. Their reduction cocycle identifies the displayed adjunct with the finite-level
comparison. The proper/open coefficient-change theorem makes it invertible. -/
theorem sfCompactSupportChosenReduction_isIso (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E X)
    (n : ℕ) : IsIso (sfCompactSupportChosenReduction l K₀ hl c E K n) := by
  classical
  let := integralOperationsDerivedCountableProducts l E Y
  obtain ⟨S, hS⟩ := coefficientDerivedSystemEvaluationCalculus.{u, u} l E X
  let N : coefficientSequenceDerived.{u, u} l E Y :=
    (ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.i ⋙
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g).obj (S.reduction.obj K.obj)
  have hN : IsNormalizedCoefficientSequence.{u, u} l E Y N :=
    compactSupportSystem_normalized l c K₀ hl E K S
  let F (j : ℕ) := sfIntrinsicCompactSupport c
    (Padic.coefficientExtensionRing l E (j + 1))
  let e (j : ℕ) : (coefficientSequenceDerivedEvaluation.{u, u} l E Y j).obj N ≅
      (F j).obj ((scalarReductionDerivedExtension l E X j).obj K.obj) :=
    (compactSupportSystemEvaluation l E c j).app (S.reduction.obj K.obj) ≪≫
      (F j).mapIso ((S.reductionEvaluation j).app K.obj)
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let D : FiniteFieldDatum.{0} := {
    p := p, a := 1, q := p, prime := hp, exponent_pos := le_refl 1,
    cardinality_eq := (pow_one p).symm, k₀ := ZMod p,
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }
  have hlp : l ≠ D.p := by change l ≠ p; omega
  let adj := (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
  have hq : IsIso ((adj.homEquiv _ _).symm
      ((coefficientSequenceProjection l E Y n).app N)) := by
    obtain ⟨T, ε, hprod, δ, hδ⟩ := coefficientSequence_roosModel l E Y D hlp N hN
    let := hprod
    have hi := normalizedDVRRoos_finite_reduction l E Y D hlp T _ _ δ hδ n adj
    have heq : (adj.homEquiv _ _).symm
        ((Pi.lift (fun j : ℕ ↦ (coefficientSequenceProjection l E Y j).app N ≫
          (normalizedDVRResCompleted l E Y D hlp j).map (ε j).inv ≫
          (T.evaluationIso j).inv)) ≫ Pi.π _ n ≫ (T.evaluationIso n).hom) =
        (adj.homEquiv _ _).symm ((coefficientSequenceProjection l E Y n).app N) ≫
          (ε n).inv := by
      simp only [Pi.lift_π_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact adj.homEquiv_naturality_right_symm _ _
    have : IsIso ((adj.homEquiv _ _).symm
        ((coefficientSequenceProjection l E Y n).app N) ≫ (ε n).inv) := by
      rw [← heq]
      exact hi
    exact IsIso.of_isIso_comp_right _ (ε n).inv
  let := hq
  let Q := (coefficientSequenceDerivedRestriction l E Y).obj N
  let L := (coefficientSequenceLimit l E Y).obj N
  let a (j : ℕ) : (coefficientConstantTowerEvaluation l E Y j).obj Q ≅
      sfCompactSupportTerm l E c K.obj j :=
    (coefficientRestrictedEvaluationIso l E Y j).app N ≪≫
      (scalarReductionDerivedRestriction l E Y j).mapIso (e j)
  let q (j : ℕ) : L ⟶ sfCompactSupportTerm l E c K.obj j :=
    (coefficientSequenceProjection l E Y j).app N ≫
      (scalarReductionDerivedRestriction l E Y j).map (e j).hom
  have ht (j : ℕ) :
      (normalizedDVRTowerTransition l E Y D hlp j.le_succ).app Q ≫ (a j).hom =
      (a (j + 1)).hom ≫ sfCompactSupportTransition l E c K.obj j := by
    let r (W : Scheme.{u}) := (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E (j + 1) j j.le_succ)).mapDerivedCategory
    let ε (i : ℕ) := (compactSupportSystemEvaluation l E c i).hom.app (S.reduction.obj K.obj)
    let ρ (i : ℕ) := (S.reductionEvaluation i).hom.app K.obj
    have H := compactSupportFiniteSquare (F (j + 1)) (F j) (r X) (r Y)
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E (j + 1) j j.le_succ)).hom
      _ _ _ _ _ _ _
      (compactSupportNativeSystemTransition l E c j.le_succ (S.reduction.obj K.obj))
      (compactSupportReductionTransition l E X S.toCoefficientDerivedSystemReduction
        j.le_succ K.obj)
    have H' := compactSupportCompletedSquare (r Y)
      (scalarReductionDerivedRestriction l E Y (j + 1))
      (scalarReductionDerivedRestriction l E Y j)
      (compactSupportRestrictionComp l E Y (j + 1) j j.le_succ).hom
      ((compactSupportCoefficientTransition l E Y j.le_succ).app N)
      (ε (j + 1)) (ε j) ((F (j + 1)).map (ρ (j + 1))) ((F j).map (ρ j))
      ((F (j + 1)).map (compactSupportReductionMap l E X (j + 1) j j.le_succ K.obj))
      ((sfCompactSupportRestriction c
        (compactSupportLevelQuotient l E (j + 1) j j.le_succ)).hom.app
          ((scalarReductionDerivedExtension l E X j).obj K.obj))
      ((pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y)
        (j + 1) j j.le_succ).app Q)
      ((coefficientRestrictedEvaluationIso l E Y (j + 1)).hom.app N)
      ((coefficientRestrictedEvaluationIso l E Y j).hom.app N)
      (compactSupportCoefficientTransition_restricted l E Y j.le_succ N) H
    rw [constantTowerTransition_eq l E Y D hlp j.le_succ]
    simpa only [a, e, ε, ρ, sfCompactSupportTransition, sfCompactSupportTerm,
      Nat.succ_eq_add_one, adjacentReductionMap, adjacentRestrictionComp, adjacentQuotient,
      compactSupportLevelQuotient, Padic.coefficientExtensionTransition,
      coefficientFiniteDerivedExtension, sfIntrinsicCompactSupport,
      sfAmbientCompactSupportCandidate, F,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc] using H'
  obtain ⟨hprod, δ, hδ⟩ := coefficientConstantTower_roos l E Y D hlp Q
  let := hprod
  obtain ⟨hprod', δ', hδ'⟩ := roos_transport
    (fun j ↦ (normalizedDVRTowerTransition l E Y D hlp j.le_succ).app Q)
    (sfCompactSupportTransition l E c K.obj) (Iso.refl L) a
    (fun j ↦ (coefficientConstantTowerProjection l E Y j).app Q) q ht
    (fun j ↦ by simp [q, a, Q, coefficientSequenceProjection, Category.assoc])
    ⟨hprod, δ, hδ⟩
  let := hprod'
  let h := (exists_isDerivedLimit_and_iso
    (sfCompactSupportTerm l E c K.obj) (sfCompactSupportTransition l E c K.obj)).1
  let M := Classical.choose h
  let hM : IsDerivedLimit (sfCompactSupportTransition l E c K.obj) M :=
    Classical.choose_spec h
  obtain ⟨ε, hε⟩ := roos_unique (sfCompactSupportTransition l E c K.obj)
    (Classical.choose hM) (Pi.lift q) (Classical.choose (Classical.choose_spec hM)) δ'
    (Classical.choose_spec (Classical.choose_spec hM)) hδ'
  have heq : (adj.homEquiv _ _).symm
      (Classical.choose hM ≫ Pi.π (sfCompactSupportTerm l E c K.obj) n) =
      (scalarReductionDerivedExtension l E Y n).map ε.hom ≫
        (adj.homEquiv _ _).symm ((coefficientSequenceProjection l E Y n).app N) ≫
        (e n).hom := by
    rw [← hε, Category.assoc, Pi.lift_π]
    exact (adj.homEquiv_naturality_left_symm _ _).trans
      (congrArg (fun z ↦ (scalarReductionDerivedExtension l E Y n).map ε.hom ≫ z)
        (adj.homEquiv_naturality_right_symm _ _))
  change IsIso ((adj.homEquiv _ _).symm
    (Classical.choose hM ≫ Pi.π (sfCompactSupportTerm l E c K.obj) n))
  rw [heq]
  infer_instance

/-- Reduction of the fixed integral functor, using its actual value equality and
the uniquely specified projection adjunct, rather than a freely chosen isomorphism.
Source: definition order 1490; lem-fix-operation-reduction
(blueprint: def-weil-compact-support-finite-action). -/
def sfCompactSupportFiniteReductionIso (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E X)
    (n : ℕ) :
    (scalarReductionDerivedExtension l E
      Y n).obj ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj ≅
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l
      E (n + 1)) c).obj
        ((scalarReductionDerivedExtension l E X n).obj K.obj) :=
  (scalarReductionDerivedExtension l E Y n).mapIso
      ((sfIntegralConstructible l E Y).ι.mapIso
        (eqToIso (sfCompactSupportFiniteIntegralFunctor_obj l K₀ hl c E K))) ≪≫
    @asIso _ _ _ _ (sfCompactSupportChosenReduction l K₀ hl c E K n)
      (sfCompactSupportChosenReduction_isIso l K₀ hl c E K n)


end FiniteAction
end WeilConjectures
