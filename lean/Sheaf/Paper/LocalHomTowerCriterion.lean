/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.CategoryTheory.LocalCoefficientLocalization
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Paper.LocalCoefficientFreeDerivedHomProduct
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction

/-!
# Localization internal Hom and the multiplication tower

Source: Stacks Project, algebraization.tex, Tag 0997, lemma-hom-from-Af,
equivalence of (1) and (3) (blueprint: lem-weil-pbc-local-hom-tower-criterion).
-/

@[expose] public section

universe u w wSlice

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Internal RHom from the coefficient localization vanishes exactly when a derived limit
of the multiplication tower vanishes, on the slice site.

Source: Stacks Project, algebraization.tex, Tag 0997, lemma-hom-from-Af,
equivalence of (1) and (3) (blueprint: lem-weil-pbc-local-hom-tower-criterion).

Proof:
1. The canonical telescope of countable free unit modules presents the localization
   as a short exact sequence. Apply the single-complex functor and pass to its
   distinguished triangle in the derived category.
2. Contravariant derived internal Hom into the restricted complex preserves the
   opposite distinguished triangle. Its first vertex vanishes exactly when its
   second arrow is invertible.
3. The free-module comparison identifies the second arrow, by conjugation, with
   `1 - shift` on the product of the multiplication tower.
4. In the distinguished triangle supplied by the given derived-limit witness,
   its first vertex also vanishes exactly when that same arrow is invertible.
Thus no uniqueness or existence theorem for derived limits is needed. -/
theorem localHom_zero_iff_multiplicationTower_zero
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U))
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (localCoefficientRings R))]
    [HasDerivedCategory.{wSlice} (ringedSiteModules.{u} ((localCoefficientRings R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u} (localCoefficientRings R)))
    [HasProduct (fun _ : ℕ ↦ (localCoefficientDerivedRestriction R U).obj K)]
    (T : DerivedCategory (ringedSiteModules.{u} ((localCoefficientRings R).over U)))
    (_hT : IsDerivedLimit
      (K := fun _ : ℕ ↦ (localCoefficientDerivedRestriction R U).obj K)
      (fun _ ↦ (localSectionDerivedMultiplication R U f).app K) T) :
    IsZero ((derivedInternalHom (J.over U) (R.over U)).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj (localCoefficientLocalization R U f)),
        (localCoefficientDerivedRestriction R U).obj K)) ↔ IsZero T := by
  let A := ringedSiteModules.{u} ((localCoefficientRings R).over U)
  let := @Pretriangulated.Opposite.instHasShiftOppositeInt
  let := @Pretriangulated.Opposite.instOpposite
  let L := (localCoefficientDerivedRestriction R U).obj K
  let H := (Functor.curry.obj (derivedInternalHom (J.over U) (R.over U))).flip.obj L
  obtain ⟨hshift, htri⟩ := (ringedInternalHom_exact (J.over U) (R.over U)).2 L
  let _ := hshift
  let _ := htri
  let S := (localCoefficientTelescope R U f).map (CochainComplex.singleFunctor A 0)
  have : PreservesFiniteLimits (CochainComplex.singleFunctor A 0) := by
    change PreservesFiniteLimits (HomologicalComplex.single A (.up ℤ) 0)
    infer_instance
  have : PreservesFiniteColimits (CochainComplex.singleFunctor A 0) := by
    change PreservesFiniteColimits (HomologicalComplex.single A (.up ℤ) 0)
    infer_instance
  have hS : S.ShortExact := (localCoefficientTelescope_shortExact R U f).map_of_exact _
  let Δ := DerivedCategory.triangleOfSES hS
  have hΔ := DerivedCategory.triangleOfSES_distinguished hS
  let Δop := (Pretriangulated.triangleOpEquivalence _).functor.obj (op Δ)
  have hΔop := Pretriangulated.op_distinguished Δ hΔ
  have hH := H.map_distinguished Δop hΔop
  have hzero := (H.mapTriangle.obj Δop).isZero₁_iff_isIso₂ hH
  change IsZero ((derivedInternalHom (J.over U) (R.over U)).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj (localCoefficientLocalization R U f)),
        L)) ↔ IsIso (H.map ((DerivedCategory.singleFunctor A 0).map
          (localCoefficientTelescopeMap R U f)).op) at hzero
  obtain ⟨e, he⟩ := localCoefficientFreeDerivedHom_product J R U f K
  have hconj : H.map ((DerivedCategory.singleFunctor A 0).map
      (localCoefficientTelescopeMap R U f)).op =
      e.hom ≫ towerTransitionEndomorphism
        (fun _ ↦ (localSectionDerivedMultiplication R U f).app K) ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using he
  obtain ⟨p, δ, hT⟩ := _hT
  have hzeroT := (Pretriangulated.Triangle.mk p
    (towerTransitionEndomorphism
      (fun _ ↦ (localSectionDerivedMultiplication R U f).app K)) δ).isZero₁_iff_isIso₂ hT
  have hiso : IsIso (H.map ((DerivedCategory.singleFunctor A 0).map
      (localCoefficientTelescopeMap R U f)).op) ↔
      IsIso (towerTransitionEndomorphism (K := fun _ : ℕ ↦ L)
        (fun _ ↦ (localSectionDerivedMultiplication R U f).app K)) := by
    rw [hconj]
    simp only [isIso_comp_left_iff, isIso_comp_right_iff]
  exact hzero.trans (hiso.trans hzeroT.symm)

end CategoryTheory
