/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology
import WeilConjectures.AlgebraicGeometry.PerfectGenerationAffineBase
import WeilConjectures.AlgebraicGeometry.KoszulSupportedAugmentationVanishing
import Mathlib.CategoryTheory.Localization.HomEquiv

/-! # Koszul powers detect supported objects on an affine scheme

Source: Stacks Project, Derived Categories of Schemes, Tag 09IR, proof via
Lemma 36.9.6 and Tag 06Z0 (blueprint: lem-pc-koszul-affine-detection).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- Apply the affine generator criterion in the standard localization, then transport
-- back to the given universe using uniqueness of localization. This avoids asking
-- for new localization instances in the arbitrary universe w on every open.
set_option backward.isDefEq.respectTransparency false in
private theorem affine_unit_detects (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    (h : ∀ n : ℤ, Subsingleton
      (((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) 0).obj
        (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)))⟦n⟧ ⟶ E.obj)) :
    IsZero E.obj := by
  let S := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
  let M : S := SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)
  let Qw : CochainComplex S ℤ ⥤ DerivedCategory S := DerivedCategory.Q
  let K := Qw.objPreimage E.obj
  let eK : Qw.obj K ≅ E.obj := Qw.objObjPreimageIso E.obj
  have hK (n : ℤ) : (K.homology n).IsQuasicoherent := by
    exact (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (.of A)).toRingedSpace)).prop_of_iso
      (((DerivedCategory.homologyFunctorFactors S n).app K).symm ≪≫
        (DerivedCategory.homologyFunctor S n).mapIso eK).symm (E.property n)
  have hsingle (i : ℤ) : Subsingleton
      (Qw.obj ((CochainComplex.singleFunctor S i).obj M) ⟶ Qw.obj K) := by
    have := h (-i)
    let ei := ((DerivedCategory.singleFunctors S).shiftIso (-i) i 0 (by omega)).app M
    exact (Iso.homCongr ei eK.symm).subsingleton_congr.mp (h (-i))
  let := HasDerivedCategory.standard S
  let : ∀ V : (Spec (.of A)).Opens,
      HasDerivedCategory
        (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let Qs : CochainComplex S ℤ ⥤ DerivedCategory S := DerivedCategory.Q
  let Es : schemeDerivedQCohCategory (Spec (.of A)) := ⟨Qs.obj K, fun n ↦
    (SheafOfModules.isQuasicoherent
      (moduleRings (Spec (.of A)).toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors S n).app K).symm (hK n)⟩
  have hs : IsZero Es.obj := by
    apply ((perfectGeneration_affine_base (Spec (.of A))).2.2 Es).mpr
    intro n
    let ei := ((DerivedCategory.singleFunctors S).shiftIso n (-n) 0 (by omega)).app M
    have : Subsingleton (Qs.obj ((CochainComplex.singleFunctor S (-n)).obj M) ⟶ Qs.obj K) :=
      (Localization.homEquiv (HomologicalComplex.quasiIso S (.up ℤ)) Qs Qw).subsingleton_congr.mpr
        (hsingle (-n))
    exact (Iso.homCongr ei (Iso.refl (Qs.obj K))).subsingleton_congr.mpr this
  let e := Localization.uniq Qs Qw (HomologicalComplex.quasiIso S (.up ℤ))
  exact (e.functor.map_isZero hs).of_iso
    (((Localization.compUniqFunctor Qs Qw
      (HomologicalComplex.quasiIso S (.up ℤ))).app K) ≪≫ eK).symm

end AlgebraicGeometry
