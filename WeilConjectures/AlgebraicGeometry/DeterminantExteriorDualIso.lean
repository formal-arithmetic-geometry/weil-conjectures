/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.DeterminantDualPairing
import WeilConjectures.AlgebraicGeometry.DeterminantDualPairingLocal

/-! Intermediate determinant facts for the ordinary determinant evaluation.

## References

* Stacks Project, Tag 0BRT
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- Exterior powers commute with the internal dual in top degree (Stacks, Tag 0BRT). -/
theorem exteriorSheaf_dual_iso (X : Scheme.{u}) (M : X.Modules) (d : ℕ)
    (hfree : M.IsFiniteLocallyFreeOfRank d) :
    Nonempty ((Scheme.Modules.exteriorPower
      (SheafOfModules.homObj (R := X.sheaf) M
        (SheafOfModules.unit X.ringCatSheaf)) d) ≅
      Scheme.Modules.dual (Scheme.Modules.exteriorPower M d)) := by
  obtain ⟨f, hf⟩ := exterior_dual_pairing_exists X M d
  obtain ⟨I, U, hU, e⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free.{u, u, u}
      (M := M) (r := d)).mp hfree
  have hb (V : X.Opens) (i : I) (g : V ⟶ U i) :
      Function.Bijective (f.val.app (Opposite.op V)) :=
    exterior_dual_pairing_app_bijective X M d f hf (U i) d (e i).some V g
  have : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map f) :=
    (Sheaf.isLocallyBijective_iff_isIso _).1
      ⟨Presheaf.isLocallyInjective_of_coversTop hU _ fun V i g ↦ (hb V i g).1,
        Presheaf.isLocallySurjective_of_coversTop hU _ fun V i g ↦ (hb V i g).2⟩
  let : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).ReflectsIsomorphisms :=
    PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
  have : IsIso f :=
    isIso_of_reflects_iso f (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
  exact ⟨asIso f⟩

end AlgebraicGeometry
