/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.PerfectSupportAffineOpenTorsion
import WeilConjectures.AlgebraicGeometry.DerivedOpenHomScalarMayerVietoris
import WeilConjectures.AlgebraicGeometry.QuasiCompactOpenInduction

/-! # Maps from perfect complexes into principal support

Global functions are encoded as compatible families of local sections. On the Zariski
site, evaluation at the top open identifies this ring with the usual global section ring.
The action on derived morphisms is the localization of the sectionwise scalar action.

## References

* Stacks Project, Derived Categories of Schemes, Lemma 36.13.9, Tag 08EJ.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem scalar_id_mul (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (r s : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u})) :
    schemeDerivedScalar X (r * s) (𝟙 E) =
      schemeDerivedScalar X r (𝟙 E) ≫ schemeDerivedScalar X s (𝟙 E) := by
  simp [schemeDerivedScalar, Linear.comp_smul, smul_smul, mul_comm]

private theorem restriction_precomp (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    {U W : X.Opens} (i : U ⟶ W) {E F : schemeDerivedCategory X}
    (s : E ⟶ E)
    (β : (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory.obj E ⟶
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory.obj F) :
    derivedOpenHomRestriction X.toRingedSpace i
        ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) W).mapDerivedCategory.map s ≫ β) =
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory.map s ≫
        derivedOpenHomRestriction X.toRingedSpace i β := by
  let A := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W
  let B := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i
  let : PreservesFiniteLimits (A ⋙ B) := comp_preservesFiniteLimits A B
  let : PreservesFiniteColimits (A ⋙ B) := comp_preservesFiniteColimits A B
  let e := Functor.mapDerivedCategoryCompIso A B ≪≫
    Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u}
      (moduleRings X.toRingedSpace) i)
  change e.inv.app E ≫ B.mapDerivedCategory.map (A.mapDerivedCategory.map s ≫ β) ≫
      e.hom.app F = _
  simp only [Functor.map_comp]
  change e.inv.app E ≫ (B.mapDerivedCategory.map (A.mapDerivedCategory.map s) ≫
      B.mapDerivedCategory.map β) ≫ e.hom.app F =
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory.map s ≫
      (e.inv.app E ≫ B.mapDerivedCategory.map β ≫ e.hom.app F)
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun t ↦ t ≫ B.mapDerivedCategory.map β ≫ e.hom.app F)
      (e.inv.naturality s).symm

private theorem top_restriction_faithful (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over ⊤))] :
    (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) ⊤).mapDerivedCategory.Faithful := by
  let F := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) ⊤
  let e : (⊤ : X.Opens).toScheme.Modules ≌ X.Modules :=
    CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor X.topIso.inv)
      (Scheme.Modules.restrictFunctor X.topIso.hom)
      ((Scheme.Modules.restrictFunctorComp _ _).symm ≪≫
        Scheme.Modules.restrictFunctorCongr X.topIso.hom_inv_id ≪≫
        Scheme.Modules.restrictFunctorId).symm
      ((Scheme.Modules.restrictFunctorComp _ _).symm ≪≫
        Scheme.Modules.restrictFunctorCongr X.topIso.inv_hom_id ≪≫
        Scheme.Modules.restrictFunctorId)
  have : (Scheme.Modules.restrictFunctor (⊤ : X.Opens).ι).IsEquivalence :=
    e.isEquivalence_inverse
  have : (F ⋙ (Scheme.Modules.overEquiv (⊤ : X.Opens)).functor).IsEquivalence :=
    Functor.isEquivalence_of_iso (Scheme.Modules.overFunctorEquiv (⊤ : X.Opens)).symm
  have : F.IsEquivalence :=
    Functor.isEquivalence_of_comp_right F (Scheme.Modules.overEquiv (⊤ : X.Opens)).functor
  change F.mapDerivedCategory.Faithful
  exact inferInstance

set_option maxHeartbeats 800000 in
-- The induction compares restriction functors at four opens and arbitrary integer shifts.
/-- Maps from a perfect complex into a quasi-coherent complex supported on `V(f)` are
annihilated by a power of `f` (Stacks, Tag 08EJ). -/
theorem exists_pow_smul_eq_zero_of_perfect_supported
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (f : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (E E' : schemeDerivedQCohCategory X) (α : E ⟶ E')
    (hE : X.IsPerfect E.obj)
    (hSupport : ∀ (i : ℤ) (x : X), x ∉ X.zeroLocus (U := ⊤) {f.val (op ⊤)} →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E'.obj).val.presheaf x))) :
    ∃ n : ℕ, schemeDerivedScalar X (f ^ n) α.hom = 0 := by
  let R := fun U : X.Opens ↦
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
  let S := fun (U : X.Opens) (n : ℕ) ↦
    (R U).map (schemeDerivedScalar X (f ^ n) (𝟙 E.obj))
  have hmul (U : X.Opens) (a b : ℕ) : S U (a + b) = S U a ≫ S U b := by
    dsimp [S]
    rw [pow_add, scalar_id_mul, Functor.map_comp]
  let P := fun U : X.Opens ↦
    ∀ (k : ℤ) (β : (R U).obj E.obj ⟶ (R U).obj (E'.obj⟦k⟧)),
      ∃ n : ℕ, S U n ≫ β = 0
  have h_affine (U : X.Opens) (hU : IsAffineOpen U) : P U :=
    perfect_support_affine_open_torsion X f E E' hE hSupport U hU
  have h_union (U V : X.Opens) (_ : IsCompact (U : Set X)) (_ : IsAffineOpen V)
      (hU : P U) (hV : P V) (hUV : P (U ⊓ V)) : P (U ⊔ V) := by
    intro k β
    obtain ⟨a, ha⟩ := hU k
      (derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_left) β)
    obtain ⟨b, hb⟩ := hV k
      (derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_right) β)
    obtain ⟨δ, hlift, hlinear⟩ :=
      derived_open_hom_scalar_mayer_vietoris X U V E.obj E'.obj k
    have hzeroU : derivedOpenHomRestriction X.toRingedSpace
        (homOfLE le_sup_left) (S (U ⊔ V) (a + b) ≫ β) = 0 := by
      rw [restriction_precomp]
      change S U (a + b) ≫ _ = 0
      rw [Nat.add_comm a b, hmul, Category.assoc, ha, comp_zero]
    have hzeroV : derivedOpenHomRestriction X.toRingedSpace
        (homOfLE le_sup_right) (S (U ⊔ V) (a + b) ≫ β) = 0 := by
      rw [restriction_precomp]
      change S V (a + b) ≫ _ = 0
      rw [hmul, Category.assoc, hb, comp_zero]
    obtain ⟨γ, hγ⟩ := hlift (S (U ⊔ V) (a + b) ≫ β) hzeroU hzeroV
    obtain ⟨c, hc⟩ := hUV (k - 1) γ
    refine ⟨c + (a + b), ?_⟩
    rw [hmul, Category.assoc, ← hγ]
    change (R (U ⊔ V)).map (schemeDerivedScalar X (f ^ c) (𝟙 E.obj)) ≫ δ γ = 0
    rw [← hlinear, hc, map_zero]
  have htop : P ⊤ := quasiCompactOpen_induction X P h_affine h_union ⊤ isCompact_univ
  let e : E'.obj⟦(0 : ℤ)⟧ ≅ E'.obj :=
    (shiftFunctorZero (schemeDerivedCategory X) ℤ).app E'.obj
  obtain ⟨n, hn⟩ := htop 0 ((R ⊤).map (α.hom ≫ e.inv))
  refine ⟨n, ?_⟩
  have : (R ⊤).Faithful := top_restriction_faithful X
  have hz : schemeDerivedScalar X (f ^ n) (𝟙 E.obj) ≫ (α.hom ≫ e.inv) = 0 := by
    apply (R ⊤).map_injective
    simpa only [Functor.map_comp, Functor.map_zero] using hn
  have hz' : schemeDerivedScalar X (f ^ n) (𝟙 E.obj) ≫ α.hom = 0 := by
    apply (cancel_mono e.inv).mp
    simpa only [Category.assoc, zero_comp] using hz
  simpa [schemeDerivedScalar, Linear.smul_comp] using hz'

end AlgebraicGeometry.Scheme
