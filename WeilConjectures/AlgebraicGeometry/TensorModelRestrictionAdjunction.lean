/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorAugmentation
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.AlgebraicGeometry.TensorModelRestrictionComparisons
import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom

/-! # Tensor-model adjunction and restriction

## References

* [Stacks Project, Tag 08DJ](https://stacks.math.columbia.edu/tag/08DJ)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
-/

@[expose] public section

set_option autoImplicit false
universe uX wD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem tensorHom_precomp
    {D : Type*} [Category D] [MonoidalCategory D]
    (H : Dᵒᵖ × D ⥤ D)
    (e : ∀ K L E, (K ⟶ H.obj (op L, E)) ≃ (K ⊗ L ⟶ E))
    (hn : ∀ K K' L L' E E' (a : K' ⟶ K) (b : L' ⟶ L) (c : E ⟶ E')
      (f : K ⟶ H.obj (op L, E)),
      e K' L' E' (a ≫ f ≫ H.map (b.op, c)) = (a ⊗ₘ b) ≫ e K L E f ≫ c)
    (K K' L E : D) (a : K' ⟶ K) (f : K ⟶ H.obj (op L, E)) :
    e K' L E (a ≫ f) = (a ⊗ₘ 𝟙 L) ≫ e K L E f := by
  have h := hn K K' L L E E a (𝟙 L) (𝟙 E) f
  have hid : H.map ((𝟙 L).op, 𝟙 E) = 𝟙 (H.obj (op L, E)) :=
    H.map_id (op L, E)
  simpa only [hid, Category.comp_id] using h

private theorem transport_tensor_adjunction
    {I C D : Type*} [Category I] [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (Q : I ⥤ C) (B : I → C) (b : ∀ {i j : I}, (i ⟶ j) → (B i ⟶ B j))
    (R : C ⥤ D) (A : C) (H : C → C) (HU : C → D)
    (eX : ∀ i E, (Q.obj i ⟶ H E) ≃ (Q.obj i ⊗ A ⟶ E))
    (eU : ∀ K E, (K ⟶ HU E) ≃ (K ⊗ R.obj A ⟶ R.obj E))
    (hn : ∀ K K' E (a : K' ⟶ K) (f : K ⟶ HU E),
      eU K' E (a ≫ f) = (a ⊗ₘ 𝟙 (R.obj A)) ≫ eU K E f)
    (c : ∀ i, B i ≅ Q.obj i ⊗ A)
    (d : ∀ i, R.obj (B i) ≅ R.obj (Q.obj i) ⊗ R.obj A)
    (h : ∀ E, R.obj (H E) ≅ HU E)
    (hd : ∀ i j (u : i ⟶ j), R.map (b u) ≫ (d j).hom =
      (d i).hom ≫ (R.map (Q.map u) ⊗ₘ 𝟙 (R.obj A)))
    (hh : ∀ i E (f : Q.obj i ⟶ H E),
      (d i).hom ≫ eU (R.obj (Q.obj i)) E (R.map f ≫ (h E).hom) =
        R.map ((c i).hom ≫ eX i E f)) :
    ∃ (t : ∀ i E, (Q.obj i ⟶ H E) ≃ (B i ⟶ E))
      (r : ∀ i E, (R.obj (Q.obj i) ⟶ R.obj (H E)) ≃ (R.obj (B i) ⟶ R.obj E)),
      (∀ i E (f : Q.obj i ⟶ H E), r i E (R.map f) = R.map (t i E f)) ∧
      (∀ i j E (u : i ⟶ j) (f : R.obj (Q.obj j) ⟶ R.obj (H E)),
        r i E (R.map (Q.map u) ≫ f) = R.map (b u) ≫ r j E f) := by
  let t := fun i E ↦ (eX i E).trans (Iso.homCongr (c i).symm (Iso.refl E))
  let r := fun i E ↦ (Iso.homCongr (Iso.refl (R.obj (Q.obj i))) (h E)).trans
    ((eU (R.obj (Q.obj i)) E).trans (Iso.homCongr (d i).symm (Iso.refl (R.obj E))))
  refine ⟨t, r, ?_, ?_⟩
  · intro i E f
    simpa [t, r, Iso.homCongr] using hh i E f
  · intro i j E u f
    simp only [r, Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv,
      Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id, Category.assoc]
    rw [hn, ← Category.assoc, ← hd i j u]
    simp only [Category.assoc]

set_option linter.style.haveILetI false in
set_option maxHeartbeats 1000000 in
-- Canonical representative coherence requires substantial elaboration.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 512 in
/-- The adjunction on a fixed K-flat first model gives global and restricted
transposition families. They commute with restriction and are natural in the
second complex, without any K-flatness requirement on that complex. -/
theorem exists_tensorModel_restriction_adjunction
    (X : Scheme.{uX}) (U : X.Opens)
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (A : schemeDerivedCategory X)
    (P : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (eA : DerivedCategory.Q.obj P ≅ A) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    let H := fun E ↦ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf).obj (op A, E)
    let B := fun J ↦ DerivedCategory.Q.obj
      (CochainComplex.mapBifunctor P J (curriedTensor _))
    ∃ (t : ∀ J E, (DerivedCategory.Q.obj J ⟶ H E) ≃ (B J ⟶ E))
      (r : ∀ J E, (R.obj (DerivedCategory.Q.obj J) ⟶ R.obj (H E)) ≃
        (R.obj (B J) ⟶ R.obj E)),
      (∀ J E (ξ : DerivedCategory.Q.obj J ⟶ H E),
        r J E (R.map ξ) = R.map (t J E ξ)) ∧
      (∀ J J' E (u : J ⟶ J')
        (s : R.obj (DerivedCategory.Q.obj J') ⟶ R.obj (H E)),
        r J E (R.map (DerivedCategory.Q.map u) ≫ s) =
          R.map (DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _)
              (ComplexShape.up ℤ))) ≫ r J' E s) := by
  classical
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := (SheafOfModules.tensorClosed X.sheaf).1.some
  let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
    Equivalence.functor
      (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
      (Modules.overEquiv U)).mapDerivedCategory
  obtain ⟨c, d, h, hd, hh⟩ := exists_tensorModel_restriction_comparisons X U A P hP eA
  letI := schemeDerivedTensorMonoidal X
  letI := schemeDerivedTensorMonoidal U.toScheme
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    refine transport_tensor_adjunction DerivedCategory.Q _
      (fun u ↦ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _) (.up ℤ)))
      R A _ _ (fun J E ↦ schemeDerivedTensorHomEquiv X (DerivedCategory.Q.obj J) A E)
      (fun K E ↦ schemeDerivedTensorHomEquiv U.toScheme K (R.obj A) (R.obj E))
      ?_ c d h hd hh
    intro K K' E a f
    exact tensorHom_precomp
      (derivedInternalHom (Opens.grothendieckTopology U.toScheme.toRingedSpace)
        U.toScheme.toRingedSpace.sheaf)
      (schemeDerivedTensorHomEquiv U.toScheme)
      (Classical.choose_spec (exists_canonicalDerivedTensorHom U.toScheme)).1
      K K' (R.obj A) (R.obj E) a f

end AlgebraicGeometry.Scheme
