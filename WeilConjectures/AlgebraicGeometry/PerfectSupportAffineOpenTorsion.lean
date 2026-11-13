/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar
import WeilConjectures.AlgebraicGeometry.PerfectSupportAffineModuleModel
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedProjectiveHomPowerTorsion

/-! # Power torsion on an affine open

## References

* Stacks Project, Tag 08EJ.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 400000 in
-- Comparing the sheaf-ring coercions in the derived module models needs extra heartbeats.
/-- Every local morphism from a restricted perfect source into a shift of a restricted
supported target is killed by a power of the global function on an affine open.
(Stacks, Tag 08EJ) -/
theorem perfect_support_affine_open_torsion
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (f : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (E E' : schemeDerivedQCohCategory X)
    (hE : X.IsPerfect E.obj)
    (hSupport : ∀ (i : ℤ) (x : X), x ∉ X.zeroLocus (U := ⊤) {f.val (op ⊤)} →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E'.obj).val.presheaf x)))
    (U : X.Opens) (hU : IsAffineOpen U) :
    let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    ∀ (k : ℤ) (β : R.obj E.obj ⟶ R.obj (E'.obj⟦k⟧)),
      ∃ n : ℕ, R.map (schemeDerivedScalar X (f ^ n) (𝟙 E.obj)) ≫ β = 0 := by
  classical
  let A : Type u := ↑(X.sheaf.obj.obj (op U))
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
    HasDerivedCategory.standard (ModuleCat.{u} A)
  let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
  dsimp only
  intro k β
  obtain ⟨P, M, F, hF, hAdd, hb, hf, hp, hM, eP, eM, hscalar⟩ :=
    perfect_support_affine_module_model X f E E' hE hSupport U hU k
  let α := F.preimage (eP.hom ≫ β ≫ eM.inv)
  obtain ⟨n, hn⟩ := DerivedCategory.bounded_projective_hom_power_torsion
    A (f.val (op U)) P hb hf hp M hM α
  refine ⟨n, ?_⟩
  have hzero : F.map
      (((show A from f.val (op U)) ^ n • 𝟙 (DerivedCategory.Q.obj P)) ≫ α) = 0 := by
    rw [Linear.smul_comp, Category.id_comp, hn, F.map_zero]
  have hpow : (show A from (f ^ n).val (op U)) = (f.val (op U)) ^ n := by
    rfl
  rw [F.map_comp, Functor.map_preimage] at hzero
  have htransport := hscalar (f ^ n)
  rw [hpow] at htransport
  rw [← Category.assoc, htransport, Category.assoc] at hzero
  apply (cancel_epi eP.hom).mp
  apply (cancel_mono eM.inv).mp
  simpa only [Category.assoc, zero_comp, comp_zero] using hzero

end AlgebraicGeometry.Scheme
