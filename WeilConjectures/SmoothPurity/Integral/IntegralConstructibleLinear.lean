/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleTriangulated
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Integral constructible categories are linear over the valuation ring

The section maps are specified by every finite quotient projection; their naturality
includes restriction from the terminal object, hence the map from constant global
sections. Sheaf-level scalar multiplication and linearity of the localization specify
the resulting action on derived morphisms, including morphisms created by localization.
The constructible subcategory carries precisely the inherited linear structure.
-/

@[expose] public section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe d u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

section CoefficientProof

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

private theorem coefficient_scalar_ext (U : Y.ProEtᵒᵖ)
    {x y : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U}
    (h : ∀ n : ℕ,
      ((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E Y)
        (op n)).hom.app U) x =
      ((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E Y)
        (op n)).hom.app U) y) : x = y := by
  let h₁ := CategoryTheory.Limits.isLimitOfPreserves
    (sheafToPresheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) RingCat)
    (CategoryTheory.Limits.limit.isLimit (integralCoefficientSheafSystem l E Y))
  let h₂ := CategoryTheory.Limits.isLimitOfPreserves ((evaluation _ _).obj U) h₁
  apply Concrete.isLimit_ext _ h₂
  intro n
  exact h n.unop

private theorem coefficient_scalar_naturality {U V : Y.ProEtᵒᵖ} (f : U ⟶ V)
    (a : Padic.coefficientExtensionIntegers l E) :
    (completedIntegralCoefficientSheafUnrestricted l E Y).obj.map f
      (integralScalarConstant l E Y U a) = integralScalarConstant l E Y V a := by
  apply coefficient_scalar_ext l E Y V
  intro n
  have hn := congrArg (fun k ↦ k.hom (integralScalarConstant l E Y U a))
    ((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E Y)
      (op n)).hom.naturality f)
  change ((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E Y)
      (op n)).hom.app V)
      ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map f
        (integralScalarConstant l E Y U a)) =
      (integralCoefficientSheaf l E Y n).obj.map f
        (((CategoryTheory.Limits.limit.π (integralCoefficientSheafSystem l E Y)
          (op n)).hom.app U) (integralScalarConstant l E Y U a)) at hn
  rw [hn]
  erw [(integralScalarConstant_existsUnique l E Y U a).exists.choose_spec n,
    (integralScalarConstant_existsUnique l E Y V a).exists.choose_spec n]
  exact (congrArg
    (fun k ↦ k.hom
      (ULift.up ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) a)))
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj
        (CommRingCat.of
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).naturality f)).symm

private noncomputable abbrev coefficient_finiteConstantMap (n : ℕ) (U : Y.ProEtᵒᵖ) :=
  ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
    ((Functor.const Y.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app U).hom

private noncomputable def coefficient_scalarSections : Padic.coefficientExtensionIntegers l E →+*
    RingCat.sectionsSubring
      ((completedIntegralCommRingSheafUnrestricted l E Y).obj ⋙
        forget₂ CommRingCat.{max u (u + 1)} RingCat.{max u (u + 1)}) where
  toFun a := ⟨fun U ↦ integralScalarConstant l E Y U a,
    fun f ↦ coefficient_scalar_naturality l E Y f a⟩
  map_one' := by
    apply Subtype.ext
    funext U
    apply coefficient_scalar_ext l E Y U
    intro n
    erw [(integralScalarConstant_existsUnique l E Y U 1).exists.choose_spec n]
    simp only [integralScalarFiniteConstant, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj, OneMemClass.coe_one, Pi.one_apply, map_one]
    exact map_one (coefficient_finiteConstantMap l E Y n U)
  map_mul' a b := by
    apply Subtype.ext
    funext U
    apply coefficient_scalar_ext l E Y U
    intro n
    change _ = (CategoryTheory.Limits.limit.π
      (integralCoefficientSheafSystem l E Y) (op n)).hom.app U
        (integralScalarConstant l E Y U a * integralScalarConstant l E Y U b)
    rw [map_mul]
    erw [(integralScalarConstant_existsUnique l E Y U (a * b)).exists.choose_spec n,
      (integralScalarConstant_existsUnique l E Y U a).exists.choose_spec n,
      (integralScalarConstant_existsUnique l E Y U b).exists.choose_spec n]
    simp only [integralScalarFiniteConstant, map_mul]
    exact map_mul (coefficient_finiteConstantMap l E Y n U) _ _
  map_zero' := by
    apply Subtype.ext
    funext U
    apply coefficient_scalar_ext l E Y U
    intro n
    erw [(integralScalarConstant_existsUnique l E Y U 0).exists.choose_spec n]
    simp only [integralScalarFiniteConstant, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj, ZeroMemClass.coe_zero, Pi.zero_apply, map_zero]
    exact map_zero (coefficient_finiteConstantMap l E Y n U)
  map_add' a b := by
    apply Subtype.ext
    funext U
    apply coefficient_scalar_ext l E Y U
    intro n
    change _ = (CategoryTheory.Limits.limit.π
      (integralCoefficientSheafSystem l E Y) (op n)).hom.app U
        (integralScalarConstant l E Y U a + integralScalarConstant l E Y U b)
    rw [map_add]
    erw [(integralScalarConstant_existsUnique l E Y U (a + b)).exists.choose_spec n,
      (integralScalarConstant_existsUnique l E Y U a).exists.choose_spec n,
      (integralScalarConstant_existsUnique l E Y U b).exists.choose_spec n]
    simp only [integralScalarFiniteConstant, map_add]
    exact map_add (coefficient_finiteConstantMap l E Y n U) _ _

@[instance_reducible]
private noncomputable def coefficientModuleLinear :
    Linear (Padic.coefficientExtensionIntegers l E) (integralTowerModules l E Y) := by
  letI : Linear
      (RingCat.sectionsSubring ((completedIntegralCommRingSheafUnrestricted l E Y).obj ⋙
        forget₂ CommRingCat RingCat)) (integralTowerModules l E Y) :=
    SheafOfModules.homLinear (completedIntegralCommRingSheafUnrestricted l E Y).obj
      (completedIntegralCoefficientSheafUnrestricted l E Y).property
  exact
    { homModule := fun M N ↦ Module.compHom (M ⟶ N) (coefficient_scalarSections l E Y)
      smul_comp := fun M N P a f g ↦
        Linear.smul_comp M N P (coefficient_scalarSections l E Y a) f g
      comp_smul := fun M N P f a g ↦
        Linear.comp_smul M N P f (coefficient_scalarSections l E Y a) g }

attribute [local instance] coefficientModuleLinear

private theorem coefficientChain_eq (a : Padic.coefficientExtensionIntegers l E) :
    integralScalarChainAction l E Y a =
      (Linear.toCatCenter (Padic.coefficientExtensionIntegers l E)
        (CochainComplex (integralTowerModules l E Y) ℤ) a).asHom := by
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro i
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (integralScalarChainAction_existsUnique l E Y a).exists.choose_spec P i U x

private theorem coefficientDerived_eq (a : Padic.coefficientExtensionIntegers l E) :
    integralScalarDerivedAction l E Y a =
      (CatCenter.localization
        (Linear.toCatCenter (Padic.coefficientExtensionIntegers l E)
          (CochainComplex (integralTowerModules l E Y) ℤ) a)
        DerivedCategory.Q
        (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ))).asHom := by
  unfold integralScalarDerivedAction
  rw [(existsUnique_eq (a' := _)).exists.choose_spec]
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ))
  intro P
  have h := NatTrans.congr_app
    ((Localization.fullyFaithfulWhiskeringLeft
      (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
      (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ))
      (DerivedCategory (integralTowerModules l E Y))).map_preimage
        (X := 𝟭 _) (Y := 𝟭 _)
        (Functor.whiskerRight (integralScalarChainAction l E Y a) DerivedCategory.Q)) P
  change ((Localization.fullyFaithfulWhiskeringLeft
      (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
      (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ))
      (DerivedCategory (integralTowerModules l E Y))).preimage (X := 𝟭 _) (Y := 𝟭 _)
        (Functor.whiskerRight (integralScalarChainAction l E Y a) DerivedCategory.Q)).app
      (DerivedCategory.Q.obj P) =
    DerivedCategory.Q.map ((integralScalarChainAction l E Y a).app P) at h
  change _ = (CatCenter.localization _ DerivedCategory.Q _).app (DerivedCategory.Q.obj P)
  rw [CatCenter.localization_app]
  exact h.trans (congrArg (fun k ↦ DerivedCategory.Q.map (k.app P))
    (coefficientChain_eq l E Y a))

private theorem coefficientLinear_ext
    {R : Type*} [Ring R] {C : Type*} [Category* C] [Preadditive C]
    (s t : Linear R C)
    (h : ∀ (A B : C) (a : R) (f : A ⟶ B),
      (letI := s; a • f) = (letI := t; a • f)) : s = t := by
  cases s with
  | mk s sm sc =>
    cases t with
    | mk t tm tc =>
      have heq : s = t := by
        funext A B
        exact Module.ext' _ _ (fun a f ↦ h A B a f)
      cases heq
      rfl

@[instance_reducible]
private noncomputable def coefficientDerivedLinear :=
  Localization.linear (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ))

private theorem coefficientDerivedShift_linear (n : ℤ) :
    letI := coefficientDerivedLinear l E Y
    (shiftFunctor (DerivedCategory (integralTowerModules l E Y)) n).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  let := coefficientDerivedLinear l E Y
  let := Localization.functor_linear (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ))
  exact Shift.linear_of_localization (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)) n

end CoefficientProof

end WeilConjectures

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- The coefficient action is the unique linear structure whose scalar maps are
multiplication by the actual constant sections of the completed coefficient sheaf. -/
theorem integralCoefficientLinear_existsUnique :
    ∃! s : Linear (Padic.coefficientExtensionIntegers l E)
        (DerivedCategory (integralTowerModules l E Y)),
      (fun [linearInst : Linear (Padic.coefficientExtensionIntegers l E)
          (DerivedCategory (integralTowerModules l E Y))] ↦
        ∀ (a : Padic.coefficientExtensionIntegers l E)
          (K K' : DerivedCategory (integralTowerModules l E Y)) (f : K ⟶ K'),
          a • f = (integralScalarDerivedAction l E Y a).app K ≫ f) (linearInst := s) := by
  let s := coefficientDerivedLinear l E Y
  have hs : (fun [_linearInst : Linear (Padic.coefficientExtensionIntegers l E)
      (DerivedCategory (integralTowerModules l E Y))] ↦
      ∀ (a : Padic.coefficientExtensionIntegers l E)
        (K K' : DerivedCategory (integralTowerModules l E Y)) (f : K ⟶ K'),
        a • f = (integralScalarDerivedAction l E Y a).app K ≫ f) (_linearInst := s) := by
    intro a K K' f
    rw [coefficientDerived_eq]
    rfl
  refine ⟨s, hs, ?_⟩
  intro t ht
  exact coefficientLinear_ext t s (fun K K' a f ↦ (ht a K K' f).trans (hs a K K' f).symm)

/-- The canonical constant-section linear structure, fixed by its scalar formula. -/
noncomputable instance integralCoefficientLinear :
    Linear (Padic.coefficientExtensionIntegers l E)
      (DerivedCategory (integralTowerModules l E Y)) :=
  (integralCoefficientLinear_existsUnique l E Y).exists.choose

/-- Shift is linear for the canonical constant-section action. -/
theorem integralCoefficientShift_linear (n : ℤ) :
    (shiftFunctor (DerivedCategory (integralTowerModules l E Y)) n).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  have hs : integralCoefficientLinear l E Y = coefficientDerivedLinear l E Y := by
    apply coefficientLinear_ext
    intro K K' a f
    rw [(integralCoefficientLinear_existsUnique l E Y).exists.choose_spec]
    rw [coefficientDerived_eq]
    rfl
  rw [hs]
  exact coefficientDerivedShift_linear l E Y n

/-- Linearity of the integral constructible full subcategory is inherited by fullness. -/
noncomputable instance integralConstructibleLinear (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) :
    Linear (Padic.coefficientExtensionIntegers l E)
      (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :=
  letI : Linear (Padic.coefficientExtensionIntegers l E)
      (completedIntegralDerivedCategory l E Y D hl) := integralCoefficientLinear l E Y
  Linear.fullSubcategory (boundedConstructibleDerivedCompleteIntegral D l hl E Y)

/-- Isomorphism closure supplies the inherited integral triangulation. -/
noncomputable instance integralConstructibleClosedIso (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) :
    (boundedConstructibleDerivedCompleteIntegral D l hl E Y).IsClosedUnderIsomorphisms :=
  (boundedConstructibleDerivedCompleteIntegral_isTriangulated D l hl E Y).1

/-- Triangulated closure, specialized from the recorded integral triangulation theorem. -/
noncomputable instance integralConstructibleTriangulated (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) :
    (boundedConstructibleDerivedCompleteIntegral D l hl E Y).IsTriangulated :=
  (boundedConstructibleDerivedCompleteIntegral_isTriangulated D l hl E Y).2

/-- The inherited shift of the integral full subcategory is linear. -/
theorem integralConstructibleShift_linear (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p) (n : ℤ) :
    (shiftFunctor (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) n).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  let : Linear (Padic.coefficientExtensionIntegers l E)
      (completedIntegralDerivedCategory l E Y D hl) := integralCoefficientLinear l E Y
  let P := boundedConstructibleDerivedCompleteIntegral D l hl E Y
  let R := Padic.coefficientExtensionIntegers l E
  let : (shiftFunctor (completedIntegralDerivedCategory l E Y D hl) n).Linear R :=
    integralCoefficientShift_linear l E Y n
  let : (shiftFunctor P.FullSubcategory n ⋙ P.ι).Linear R :=
    Functor.linear_of_iso R (P.ι.commShiftIso n).symm
  constructor
  intro X Z f a
  apply P.ι.map_injective
  rw [P.ι.map_smul]
  exact (shiftFunctor P.FullSubcategory n ⋙ P.ι).map_smul a f

end WeilConjectures
