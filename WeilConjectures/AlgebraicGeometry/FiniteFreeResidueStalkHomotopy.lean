/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkMinimalComplex

/-! # The local-ring homotopy normal form of a finite free complex

## References

Stacks Project, Tag 00MT.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

private theorem free_zero_isZero {S : Scheme.{u}} :
    IsZero (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin 0))) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (SheafOfModules.freeHomEquiv _).injective
  funext x
  exact Fin.elim0 x.down

private theorem nonempty_free_iso_of_pullback_rank {S : Scheme.{u}}
    {R : CommRingCat.{u}} (hR : IsField R) (f : Spec R ⟶ S) (M : S.Modules)
    (hfree : ∃ s : ℕ, Nonempty
      (M ≅ SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin s))))
    (r : ℕ) (hrank : ((Modules.pullback f).obj M).IsFiniteLocallyFreeOfRank r) :
    Nonempty (M ≅ SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin r))) := by
  obtain ⟨s, ⟨e⟩⟩ := hfree
  let ef := (Modules.pullback f).mapIso e ≪≫ pullbackFreeIso f _
  obtain ⟨hdim, hfin⟩ := finrank_moduleSpecΓFunctor_obj_free hR ef
  have := hfin
  have hr := (isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj
    hR _ r).mp hrank
  have hs : s = r := by simpa using hdim.symm.trans hr
  subst s
  exact ⟨e⟩

/-- Residue cohomology determines the homotopy normal form over the local ring.
(Stacks, Tag 00MT.) -/
theorem nonempty_stalk_homotopyEquiv_single_of_residue
    {Y : Scheme.{u}} (P : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d)
    (hfree : ∀ n : ℤ, ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (i r : ℕ) (y : Y)
    (hy : (∀ q : ℕ, q ≠ i → IsZero
        ((((Modules.pullback (Y.fromSpecResidueField y)).mapHomologicalComplex _).obj
          P).homology q)) ∧
      ((((Modules.pullback (Y.fromSpecResidueField y)).mapHomologicalComplex _).obj
        P).homology i).IsFiniteLocallyFreeOfRank r) :
    Nonempty (HomotopyEquiv
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P)
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj
        ((CochainComplex.singleFunctor Y.Modules (i : ℤ)).obj
          (SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r)))))) := by
  classical
  let s := Y.fromSpecStalk y
  let t := Spec.map (Y.residue y)
  let L : CochainComplex (Spec (Y.presheaf.stalk y)).Modules ℤ :=
    ((Modules.pullback s).mapHomologicalComplex _).obj P
  have hLge : L.IsStrictlyGE 0 := by
    let := hge
    infer_instance
  have hLle : L.IsStrictlyLE d := by
    let := hle
    infer_instance
  have hLfree (n : ℤ) : ∃ k : ℕ, Nonempty
      (L.X n ≅ SheafOfModules.free
        (R := (Spec (Y.presheaf.stalk y)).ringCatSheaf) (ULift.{u} (Fin k))) := by
    obtain ⟨k, ⟨e⟩⟩ := hfree n
    exact ⟨k, ⟨(Modules.pullback s).mapIso e ≪≫ pullbackFreeIso s _⟩⟩
  obtain ⟨Q, ⟨e⟩, hQge, _hQle, hQfree, hd⟩ :=
    exists_stalk_minimal_complex y L d hLge hLle hLfree
  let B := ((Modules.pullback t).mapHomologicalComplex _).obj Q
  let ec := (Functor.mapHomologicalComplexCompIso
    (Modules.pullbackComp t s) (ComplexShape.up ℤ)).app P
  let eb := (Modules.pullback t).mapHomotopyEquiv e
  have eH (n : ℤ) : B.homology n ≅
      ((((Modules.pullback (Y.fromSpecResidueField y)).mapHomologicalComplex _).obj
        P).homology n) :=
    (eb.toHomologyIso n).symm ≪≫
      (HomologicalComplex.homologyFunctor _ _ n).mapIso ec
  have eX (n : ℤ) : B.X n ≅ B.homology n :=
    (ShortComplex.HomologyData.ofZeros (B.sc n)
      (hd _ _) (hd _ _)).left.homologyIso.symm
  have := hy.2
  have hBi : (B.X (i : ℤ)).IsFiniteLocallyFreeOfRank r :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (eX i ≪≫ eH i).symm
  obtain ⟨ei⟩ := nonempty_free_iso_of_pullback_rank
    (Field.toIsField (Y.residueField y)) t (Q.X i) (hQfree i) r hBi
  have hQzero (n : ℤ) (hn : n ≠ (i : ℤ)) : IsZero (Q.X n) := by
    by_cases hneg : n < 0
    · let := hQge
      exact Q.isZero_of_isStrictlyGE 0 n hneg
    · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n)
      have hB : IsZero (B.X (q : ℤ)) :=
        (hy.1 q (by exact_mod_cast hn)).of_iso (eX q ≪≫ eH q)
      have hB0 : (B.X (q : ℤ)).IsFiniteLocallyFreeOfRank 0 :=
        SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (hB.iso free_zero_isZero).symm
      obtain ⟨eq⟩ := nonempty_free_iso_of_pullback_rank
        (Field.toIsField (Y.residueField y)) t (Q.X q) (hQfree q) 0 hB0
      exact free_zero_isZero.of_iso eq
  have : Q.IsStrictlyGE (i : ℤ) :=
    (Q.isStrictlyGE_iff i).mpr fun n hn ↦ hQzero n (by omega)
  have : Q.IsStrictlyLE (i : ℤ) :=
    (Q.isStrictlyLE_iff i).mpr fun n hn ↦ hQzero n (by omega)
  obtain ⟨M, ⟨eQ⟩⟩ := Q.exists_iso_single i
  let eM : M ≅ SheafOfModules.free
      (R := (Spec (Y.presheaf.stalk y)).ringCatSheaf) (ULift.{u} (Fin r)) :=
    ((HomologicalComplex.eval _ _ (i : ℤ)).mapIso eQ ≪≫
      HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (i : ℤ) M).symm ≪≫ ei
  let esingle := HomologicalComplex.singleMapHomologicalComplex
    (Modules.pullback s) (ComplexShape.up ℤ) (i : ℤ)
  exact ⟨e.trans (HomotopyEquiv.ofIso
    (eQ ≪≫ (CochainComplex.singleFunctor _ (i : ℤ)).mapIso eM ≪≫
      (CochainComplex.singleFunctor _ (i : ℤ)).mapIso (pullbackFreeIso s _).symm ≪≫
      (esingle.app _).symm))⟩

end AlgebraicGeometry.Scheme.Modules
