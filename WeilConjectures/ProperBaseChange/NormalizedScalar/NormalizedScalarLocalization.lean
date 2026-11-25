/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationLift
import Mathlib.RingTheory.Localization.Module

/-! # Linear normalized descent through Verdier rationalization

A triangulated functor `H : C ⥤ D` from an `R`-linear category to an `A`-linear one, with
`A` a localization of `R` and `H` compatible with scalars, factors through the Verdier
rationalization of `C` by an `A`-linear triangulated functor.

## Main definitions and results

- `WeilConjectures.NormalizedScalar.lift_linear`: the Verdier lift is `A`-linear.
- `WeilConjectures.NormalizedScalar.ForwardFunctorData`: the data of such a factorization.
- `WeilConjectures.NormalizedScalar.forward_exists`: such a factorization exists.

## Implementation details

The factorization is the existing triangulated Verdier lift; no equivalence is assumed. Its
`A`-linearity comes from `R`-linearity by extending scalars along the localization on each
Hom module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w w' v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures.NormalizedScalar

variable {R : Type w} [CommRing R] (M : Submonoid R)
  (A : Type w') [CommRing A] [Algebra R A] [IsLocalization M A]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C] [IsTriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear A D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The Verdier lift of `H` through the rationalization is linear over the localized
coefficient ring `A`. -/
theorem lift_linear (H : C ⥤ D) [H.CommShift ℤ] [H.IsTriangulated]
    (hH : ∀ (r : R) (X : C), H.map (r • 𝟙 X) = algebraMap R A r • 𝟙 (H.obj X)) :
    (CategoryTheory.Rationalization.lift M A H hH).Linear A := by
  let : Linear R D :=
    { homModule := fun X Y ↦ Module.compHom (X ⟶ Y) (algebraMap R A)
      smul_comp := fun X Y Z r f g ↦ Linear.smul_comp X Y Z (algebraMap R A r) f g
      comp_smul := fun X Y Z f r g ↦ Linear.comp_smul X Y Z f (algebraMap R A r) g }
  have (X Y : D) : IsScalarTower R A (X ⟶ Y) :=
    ⟨by
      intro r a f
      change (r • a) • f = (algebraMap R A r) • (a • f)
      rw [Algebra.smul_def, mul_smul]⟩
  let J := CategoryTheory.Rationalization.lift M A H hH
  have : J.Linear R := (CategoryTheory.Functor.linear_iff R J).2 fun X r ↦ by
    rw [CategoryTheory.Rationalization.lift_map_smul_id]
    exact algebraMap_smul A r (𝟙 (J.obj X))
  have (X Y : CategoryTheory.Rationalization M C) : IsScalarTower R A (X ⟶ Y) := by
    constructor
    intro r a f
    rw [Algebra.smul_def, mul_smul,
      CategoryTheory.Rationalization.algebraMap_smul]
  exact ⟨fun {X Y} f a ↦
    ((J.mapLinearMap R).extendScalarsOfIsLocalization M A).map_smul a f⟩

/-- An additive linear triangulated forward lift with a shift-compatible comparison
and its scalar naturality equation. -/
def ForwardFunctorData (H : C ⥤ D) [H.CommShift ℤ] : Prop :=
  ∃ (J : CategoryTheory.Rationalization M C ⥤ D) (_ : J.Additive)
    (_ : J.Linear A) (_ : J.CommShift ℤ)
    (e : CategoryTheory.Rationalization.Q M C ⋙ J ≅ H),
    NatTrans.CommShift e.hom ℤ ∧ J.IsTriangulated ∧
    ∀ (X Y : C) (f : X ⟶ Y) (a : A),
      J.map (a • (CategoryTheory.Rationalization.Q M C).map f) ≫ e.hom.app Y =
        e.hom.app X ≫ (a • H.map f)

/-- A normalized forward functor through the ordinary Verdier rationalization: an additive,
`A`-linear, triangulated functor `J` with a shift-compatible isomorphism `Q ⋙ J ≅ H` that is
natural with respect to `A`-scalar multiples of morphisms. -/
theorem forward_exists (H : C ⥤ D) [H.CommShift ℤ] [H.IsTriangulated]
    (hH : ∀ (r : R) (X : C), H.map (r • 𝟙 X) = algebraMap R A r • 𝟙 (H.obj X)) :
    ∃ (J : CategoryTheory.Rationalization M C ⥤ D) (_ : J.Additive)
      (_ : J.Linear A) (_ : J.CommShift ℤ)
      (e : CategoryTheory.Rationalization.Q M C ⋙ J ≅ H),
      NatTrans.CommShift e.hom ℤ ∧ J.IsTriangulated ∧
      ∀ (X Y : C) (f : X ⟶ Y) (a : A),
        J.map (a • (CategoryTheory.Rationalization.Q M C).map f) ≫ e.hom.app Y =
          e.hom.app X ≫ (a • H.map f) := by
  let J := CategoryTheory.Rationalization.lift M A H hH
  have : J.Linear A := lift_linear M A H hH
  refine ⟨J, inferInstance, inferInstance, inferInstance,
    CategoryTheory.Rationalization.liftFac M A H hH, inferInstance, inferInstance, ?_⟩
  intro X Y f a
  rw [J.map_smul]
  simpa only [CategoryTheory.Functor.comp_map, Linear.smul_comp, Linear.comp_smul] using
    congrArg (fun g ↦ a • g)
      ((CategoryTheory.Rationalization.liftFac M A H hH).hom.naturality f)

end WeilConjectures.NormalizedScalar
