/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.StalkRestrictionComplexIso
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkMapPositive
@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules
/-- A map between canonical finite free sheaves over a stalk extends locally. -/
theorem exists_local_free_stalk_map
    {Y : Scheme.{u}} (r s : ℕ) (y : Y)
    (t : (Modules.pullback (Y.fromSpecStalk y)).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))) ⟶
      (Modules.pullback (Y.fromSpecStalk y)).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s)))) :
    ∃ (U : Y.Opens), ∃ (hyU : y ∈ U), ∃ (g :
      (restrictFunctor U.ι).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))) ⟶
      (restrictFunctor U.ι).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s)))),
      let E := Functor.isoWhiskerRight (restrictFunctorIsoPullback U.ι)
          (Modules.pullback (U.fromSpecStalkOfMem y hyU)) ≪≫
        pullbackComp (U.fromSpecStalkOfMem y hyU) U.ι ≪≫
        pullbackCongr (U.fromSpecStalkOfMem_ι y hyU)
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map g =
        E.hom.app _ ≫ t ≫ E.inv.app _ := by
  have hfree : ∀ (Z : Scheme.{u}), IsZero
      (SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{u} (Fin 0))) := by
    intro Z
    let hUnique : ∀ X : SheafOfModules Z.ringCatSheaf, Unique
        (SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{u} (Fin 0)) ⟶ X) := fun X =>
      { default := 0
        uniq := by
          intro f
          apply (SheafOfModules.freeHomEquiv X).injective
          funext i
          exact isEmptyElim i }
    letI := hUnique
    exact (IsInitial.ofUnique (SheafOfModules.free (R := Z.ringCatSheaf)
      (ULift.{u} (Fin 0)))).isZero
  by_cases hr : r = 0
  · subst r
    let e := Modules.pullbackFreeIso (Y.fromSpecStalk y)
      (ULift.{u} (Fin 0))
    have hsrc : IsZero ((Modules.pullback (Y.fromSpecStalk y)).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin 0)))) :=
      IsZero.of_iso (hfree _) e
    refine ⟨⊤, trivial, 0, ?_⟩
    have ht : t = 0 := (hsrc.eq_of_src _ _)
    simp [ht]
  · by_cases hs : s = 0
    · subst s
      let e := Modules.pullbackFreeIso (Y.fromSpecStalk y)
        (ULift.{u} (Fin 0))
      have htgt : IsZero ((Modules.pullback (Y.fromSpecStalk y)).obj
          (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin 0)))) :=
        IsZero.of_iso (hfree _) e
      refine ⟨⊤, trivial, 0, ?_⟩
      have ht : t = 0 := htgt.eq_of_tgt _ _
      simp [ht]
    · apply exists_local_free_stalk_map_of_nonempty r s y
      · exact ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩
      · exact ⟨⟨0, Nat.pos_of_ne_zero hs⟩⟩
end AlgebraicGeometry.Scheme.Modules
