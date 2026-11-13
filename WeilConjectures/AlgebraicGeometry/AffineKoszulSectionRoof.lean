/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedTensorAugmentation
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.AffineKoszulSectionColimit
import WeilConjectures.Algebra.Homology.KFlatResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Limits.Types.Colimits
import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Koszul representatives of sections on an affine open

## References

* Stacks Project, Tags 08DC, 08DD and 08EH
-/

@[expose] public section

set_option autoImplicit false

universe uX wD

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- Realize a derived augmentation by a chain map after a K-flat replacement (Stacks, Tag 06YS). -/
private theorem kflat_augmentation_realization
    (X : Scheme.{uX})
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    (P : schemeDerivedCategory X)
    (T : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (a : P ⟶ DerivedCategory.Q.obj T) :
    ∃ J : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ,
      CochainComplex.IsKFlatTensor (R := X.sheaf) J ∧
      ∃ (c : DerivedCategory.Q.obj J ≅ P) (u : J ⟶ T),
        DerivedCategory.Q.map u = c.hom ≫ a := by
  let C := SheafOfModules.{uX} (moduleRings X.toRingedSpace)
  let Q := DerivedCategory.Q (C := C)
  let P₀ := Q.objPreimage P
  let c₀ : Q.obj P₀ ≅ P := Q.objObjPreimageIso P
  obtain ⟨K, t, ht, b, hb⟩ := DerivedCategory.right_fac (c₀.hom ≫ a)
  let := ht
  obtain ⟨J, q, hJ, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) K
  let : QuasiIso q := hq
  let c : Q.obj J ≅ P := asIso (Q.map q) ≪≫ asIso (Q.map t) ≪≫ c₀
  refine ⟨J, hJ, c, q ≫ b, ?_⟩
  dsimp only [c, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, Category.assoc, hb]
  dsimp only [Q]
  simp only [Functor.map_comp, IsIso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 600000 in
-- Comparing chosen restriction functors and their localization instances needs extra heartbeats.
/-- A section of an arbitrary quasi-coherent derived object on a compact open of an affine scheme
is represented by a map from a K-flat perfect complex with a chain augmentation.
There is no perfect source, tensor product, or lifted morphism in this statement
(Stacks, Tags 08DC, 08DD, 08EH and 06YD). -/
theorem affine_koszul_section_roof
    (X : Scheme.{uX}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory X) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    let T := HomologicalComplex.tensorUnit
      (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
    let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    ∀ s : R.obj (DerivedCategory.Q.obj T) ⟶ R.obj E.obj,
      ∃ J : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ,
        CochainComplex.IsKFlatTensor (R := X.sheaf) J ∧ IsPerfect X (DerivedCategory.Q.obj J) ∧
        ∃ (u : J ⟶ T) (ξ : DerivedCategory.Q.obj J ⟶ E.obj),
          IsIso (R.map (DerivedCategory.Q.map u)) ∧
          R.map (DerivedCategory.Q.map u) ≫ s = R.map ξ := by
  classical
  let := SheafOfModules.monoidalCategory X.sheaf
  let := (SheafOfModules.tensorClosed X.sheaf).1.some
  let C := SheafOfModules.{uX} (moduleRings X.toRingedSpace)
  let T := HomologicalComplex.tensorUnit C (ComplexShape.up ℤ)
  let LX := SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U
  let EX : SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace) := Modules.overEquiv U
  let R := (LX ⋙ EX.functor).mapDerivedCategory
  change ∀ s : R.obj (DerivedCategory.Q.obj T) ⟶ R.obj E.obj, _
  intro s
  obtain ⟨P, a, hP, v, hav, hva, D, hD, ι, hι, ⟨hc⟩⟩ :=
    affine_koszul_section_colimit X U hU E
  obtain ⟨n, z, hz⟩ := Types.jointly_surjective D hc s
  let ξ : P n ⟶ E.obj := cast (hD n) z
  have hξ : ι.app n (cast (hD n).symm ξ) = s := by
    simpa only [ξ, cast_cast, cast_eq] using hz
  obtain ⟨J, hJ, c, u, hu⟩ := kflat_augmentation_realization X (P n) T (a n)
  have hp : IsPerfect X (DerivedCategory.Q.obj J) := by
    intro x
    obtain ⟨V, hx, K, hK, ⟨eK⟩⟩ := hP n x
    exact ⟨V, hx, K, hK,
      ⟨(SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) V).mapDerivedCategory.mapIso
        c ≪≫ eK⟩⟩
  let j : R.obj (P n) ≅ R.obj (DerivedCategory.Q.obj T) :=
    ⟨R.map (a n), v n, hav n, hva n⟩
  have hiu : IsIso (R.map (DerivedCategory.Q.map u)) := by
    rw [hu, Functor.map_comp]
    change IsIso (R.map c.hom ≫ j.hom)
    exact (R.mapIso c ≪≫ j).isIso_hom
  refine ⟨J, hJ, hp, u, c.hom ≫ ξ, hiu, ?_⟩
  have hs : v n ≫ R.map ξ = s := (hι n ξ).symm.trans hξ
  rw [hu, Functor.map_comp, Functor.map_comp, ← hs]
  change (R.map c.hom ≫ R.map (a n)) ≫ (v n ≫ R.map ξ) =
    R.map c.hom ≫ R.map ξ
  rw [Category.assoc, ← Category.assoc (R.map (a n)), hav n, Category.id_comp]

end AlgebraicGeometry.Scheme
