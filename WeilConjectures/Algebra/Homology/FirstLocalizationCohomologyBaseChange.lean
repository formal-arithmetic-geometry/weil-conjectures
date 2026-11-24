/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.Localization.Basic
import WeilConjectures.Algebra.Homology.LocalizationModelKernel
import WeilConjectures.Algebra.Homology.LocalizationModelDenominators
import Mathlib.RingTheory.Localization.BaseChange

/-! # Cohomology under localization of the first coefficient ring

## References

* Stacks Project, Tag 06Y6 (More on Algebra)
* Stacks Project, Tag 0DJ8
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A Aq B D : Type u)
  [CommRing R] [CommRing A] [CommRing Aq] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra A Aq] [Algebra R Aq]
  [IsScalarTower R A Aq]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- Cohomology localizes over the tensor coefficient ring, before further extension to D. -/
theorem exists_firstLocalization_cohomology_baseChange
    (S : Submonoid A) [IsLocalization S Aq] (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (uQ : (restrict R A).obj Q ⟶ (restrict R Aq).obj ((extend A Aq).obj Q))
    (huQ : ∀ (j : ℤ) (x : Q.X j), uQ.f j x = (1 : Aq) ⊗ₜ[A,algebraMap A Aq] x) :
    letI := L.universal
    letI := K.universal
    let ζ := Functor.leftDerivedNatIso L.derived K.derived L.counit K.counit
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) (Iso.refl _)
    ∃ e : (ModuleCat.extendScalars
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A Aq)
          (AlgHom.id R B)).toRingHom).obj (L.cohomology i) ≅ K.cohomology i,
      ∀ x : L.cohomology i,
        e.hom ((1 : Aq ⊗[R] B) ⊗ₜ[A ⊗[R] B,
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A Aq)
            (AlgHom.id R B)).toRingHom] x) =
        ((L.cohomologyIso i).hom ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
            (L.derived.map (DerivedCategory.Qh.map
              ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map uQ)) ≫
              ζ.hom.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                  ((restrict R Aq).obj ((extend A Aq).obj Q))))) ≫
          (K.cohomologyIso i).inv) x := by
  let φ := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A Aq)
    (AlgHom.id R B)).toRingHom
  let : Algebra (A ⊗[R] B) (Aq ⊗[R] B) := φ.toAlgebra
  have ht : IsScalarTower A (A ⊗[R] B) (Aq ⊗[R] B) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    simp [φ]
  let := ht
  let T := Algebra.algebraMapSubmonoid (A ⊗[R] B) S
  have hloc : IsLocalization T (Aq ⊗[R] B) := by
    apply IsLocalization.tensorProduct_tensorProduct R B S Aq
    ext b
    rw [RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
    simp [φ]
  let := hloc
  let N := (ModuleCat.restrictScalars φ).obj (K.cohomology i)
  let : Module (Aq ⊗[R] B) N :=
    inferInstanceAs (Module (Aq ⊗[R] B) (K.cohomology i))
  let : IsScalarTower (A ⊗[R] B) (Aq ⊗[R] B) N :=
    ⟨fun a b x ↦ mul_smul (φ a) b x⟩
  let c := localizationModelMap R A Aq B D i Q L K uQ
  let f : L.cohomology i →ₗ[A ⊗[R] B] N :=
    { toFun := c
      map_add' := c.hom.map_add
      map_smul' := fun a x ↦ localizationModelMap_smul R A Aq B D i Q L K uQ huQ a x }
  have hf : IsLocalizedModule T f := by
    refine ⟨?_, ?_, ?_⟩
    · intro s
      simpa only [AlgHom.commutes] using
        (IsLocalization.map_units (Aq ⊗[R] B) s).map
        (Algebra.lsmul (A ⊗[R] B) (A := Aq ⊗[R] B) (A ⊗[R] B) N)
    · intro y
      obtain ⟨x, s, hs⟩ :=
        localizationModelMap_denominators R A Aq B D S i Q L K uQ huQ y
      refine ⟨⟨x, ⟨algebraMap A (A ⊗[R] B) s, ?_⟩⟩, ?_⟩
      · exact ⟨s, s.property, rfl⟩
      · simpa [f, c, N, φ, Algebra.TensorProduct.map_tmul] using hs
    · intro x y hxy
      have hz : c (x - y) = 0 := by
        rw [map_sub, show c x = c y from hxy, sub_self]
      obtain ⟨s, hs⟩ := localizationModelMap_kernel R A Aq B D S i Q L K uQ huQ
        (x - y) hz
      refine ⟨⟨algebraMap A (A ⊗[R] B) s, ?_⟩, ?_⟩
      · exact ⟨s, s.property, rfl⟩
      · exact sub_eq_zero.mp (by simpa [Submonoid.smul_def, smul_sub] using hs)
  let := hf
  let e := (IsLocalizedModule.isBaseChange T (Aq ⊗[R] B) f).equiv
  refine ⟨e.toModuleIso, ?_⟩
  intro x
  change e ((1 : Aq ⊗[R] B) ⊗ₜ[A ⊗[R] B] x) = c x
  simp only [e, IsBaseChange.equiv_tmul, one_smul]
  rfl

end RingTensorCohomology
