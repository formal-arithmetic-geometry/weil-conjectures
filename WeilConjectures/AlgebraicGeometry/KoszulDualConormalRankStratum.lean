/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Dimension.Finrank

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.AffineConormalFrame
import WeilConjectures.RingTheory.KoszulConormalBasis
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree

/-! # Local rank of the dual conormal for a Koszul-regular immersion

## References

* Stacks Project, Duality for Schemes, Tags 0BQZ and 0BR0.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The dual conormal restricts to a finite locally free module of rank n on the rank-n
stratum. -/
theorem koszulRegularImmersion_dual_conormal_rank_stratum {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsNoetherian Y] [IsClosedImmersion i]
    (hregular : ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (n : ℕ) (f : Fin n → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (r : LocallyConstant Z ℕ)
    (hr : ∀ z : Z, r z = Module.finrank (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)))
    (n : ℕ) :
    ((Scheme.Modules.restrictFunctor (Scheme.Modules.exteriorRankOpen r n).ι).obj
      (SheafOfModules.homObj (R := Z.sheaf)
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
        (SheafOfModules.unit Z.ringCatSheaf))).IsFiniteLocallyFreeOfRank n := by
  classical
  let C := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
  let D := SheafOfModules.homObj (R := Z.sheaf) C
    (SheafOfModules.unit Z.ringCatSheaf)
  let S := Scheme.Modules.exteriorRankOpen r n
  have frames (x : S.toScheme) : ∃ W : Z.Opens, x.1 ∈ W ∧
      Nonempty (D.over W ≅ SheafOfModules.free (ULift.{u} (Fin n))) := by
    obtain ⟨U, hxU, m, f, hf, hreg⟩ := hregular x.1
    obtain ⟨b, _⟩ := ExteriorAlgebra.exists_koszul_conormal_basis
      Γ(Y, U.1) (i.ker.ideal U) m f hreg hf
    obtain ⟨⟨e⟩, hdim⟩ := affine_conormal_frame i U m b
    have hm := hdim x.1 hxU
    let W := i ⁻¹ᵁ U.1
    have hmn : m = n := by
      calc
        m = r x.1 := (hr x.1 |>.trans hm).symm
        _ = n := x.2
    rw [hmn] at e
    refine ⟨W, hxU, ⟨?_⟩⟩
    exact SheafOfModules.overHomObjIso C (SheafOfModules.unit Z.ringCatSheaf) W ≪≫
      ((SheafOfModules.homFunctor (Z.sheaf.over W)).flip.obj
        (SheafOfModules.unit (Z.ringCatSheaf.over W))).mapIso e.symm.op ≪≫
      SheafOfModules.homObjFreeUnitIso (ULift.{u} (Fin n))
  choose W hxW e using frames
  let V : S.toScheme → S.toScheme.Opens := fun x ↦ S.ι ⁻¹ᵁ W x
  have hV : ⨆ x, V x = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩
  apply Scheme.Modules.isFiniteLocallyFreeOfRank_of_restrict_iso_free
    ((Scheme.Modules.restrictFunctor S.ι).obj D) (fun x ↦ (V x).ι)
  · simpa only [Scheme.Opens.opensRange_ι] using hV
  · intro x
    let E := Scheme.Modules.overIsoFreeEquiv D (W x) (ULift.{u} (Fin n)) (e x).some
    refine ⟨(Scheme.Modules.restrictFunctorComp (V x).ι S.ι).symm.app D ≪≫
      (Scheme.Modules.restrictFunctorCongr (morphismRestrict_ι S.ι (W x)).symm).app D ≪≫
      (Scheme.Modules.restrictFunctorComp (S.ι ∣_ W x) (W x).ι).app D ≪≫
      (Scheme.Modules.restrictFunctor (S.ι ∣_ W x)).mapIso E ≪≫
      Scheme.Modules.restrictFreeIso (S.ι ∣_ W x) (ULift.{u} (Fin n))⟩

end AlgebraicGeometry
