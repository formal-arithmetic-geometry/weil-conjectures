/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalData
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechCycleRealization
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechAugmentationTransfer

/-! # Inverse image on normalized additive étale Čech edges
Source: Stacks Project, Tags 01FD and 03P2. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Matched cycles have inverse-image classes for any normalized edge equivalences.
The cycles and both equivalences are supplied: no existence or scalar law is asserted.
Source: Stacks Project, Tag 01FD, Lemma 20.15.1, coefficient/refinement diagram,
applied to the small étale sites; Tag 03P2 identifies the coefficient sections. -/
theorem etaleAdditiveCech_normalized_inverseImage
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    [CompactSpace X] [CompactSpace Y] [X.IsSeparated] [Y.IsSeparated]
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hV : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, V (y l)))
    (hcover : iSup U = ⊤) (hcover' : iSup V = ⊤)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (n : ℕ)
    (a : Sheaf.H X.etaleAdditiveSheaf n ≃+
      (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homology n)
    (ha : IsEtaleAdditiveCechNormalized U n a)
    (a' : Sheaf.H Y.etaleAdditiveSheaf n ≃+
      (cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).homology n)
    (ha' : IsEtaleAdditiveCechNormalized V n a')
    (z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n)
    (z' : (cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).cycles n)
    (hcoords : ∀ y : Fin (n + 1) → ι,
            cechCoordinate Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf) n y
                ((cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).iCycles n z') =
              (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf).presheaf.map
                (homOfLE (hinter n y)).op
                ((SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom).val.app
                  (op (⨅ l, U (y l)))
                  (cechCoordinate X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf) n y
                    ((cechOver X.toSpecΓ U
                      (SheafOfModules.unit X.ringCatSheaf)).iCycles n z)))) :
    (cechOver Y.toSpecΓ V (SheafOfModules.unit Y.ringCatSheaf)).homologyπ n z' =
      a' (Sheaf.H.map
        (((Etale.upperStarLowerStarAdjunction _ g).homEquiv _ _).symm
          (Scheme.etaleAdditiveSheafToLowerStar g)) n
        (Etale.cohomologyMap g X.etaleAdditiveSheaf n
          (a.symm ((cechOver X.toSpecΓ U
            (SheafOfModules.unit X.ringCatSheaf)).homologyπ n z)))) := by
  classical
  have _ := hU
  have _ := hV
  have _ := hcover'
  let I := injectiveResolution X.etaleAdditiveSheaf
  let J := injectiveResolution Y.etaleAdditiveSheaf
  obtain ⟨cX⟩ := Etale.exists_resolutionSection_canonical_comparison X.etaleAdditiveSheaf I
  obtain ⟨cY⟩ := Etale.exists_resolutionSection_canonical_comparison Y.etaleAdditiveSheaf J
  obtain ⟨s, tα, tβ, hα, hβ, heq⟩ :=
    etaleAdditiveCech_cycle_realization U hcover I n z
  have hx := ha I cX s z tα tβ hα hβ heq
  have hx' : cX.globalEquiv n ((additiveCechGlobal I).homologyπ n s) =
      a.symm ((cechOver X.toSpecΓ U
        (SheafOfModules.unit X.ringCatSheaf)).homologyπ n z) := by
    rw [← hx, AddEquiv.symm_apply_apply]
  obtain ⟨s', tα', tβ', hα', hβ', heq', hclass⟩ :=
    etaleAdditiveCech_augmentation_transfer g U V hinter I J cX cY n
      z z' hcoords s tα tβ hα hβ heq
  have hy := ha' J cY s' z' tα' tβ' hα' hβ' heq'
  rw [hclass, hx'] at hy
  exact hy.symm

end AlgebraicGeometry.Scheme.Modules
