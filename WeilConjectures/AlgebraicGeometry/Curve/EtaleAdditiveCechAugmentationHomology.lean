/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechAlphaQuasiIso
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechBetaHomology

/-! # Homology equivalences of the two additive Čech augmentations
Source: Stacks Project, Tags 03P2 and 01FD.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The two explicit augmentations induce isomorphisms on homology.
Source: Stacks Project, Tag 03P2, Theorem 59.22.4 (separated affine-cover proof),
and Tag 01FD, Lemma 20.15.1 (augmented double-complex diagram). -/
theorem exists_additiveCech_augmentation_homology
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤)
    (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ) :
    ∃ p : (additiveCechGlobal I).homology n ≃+ (additiveCechTotal U I).homology n,
    ∃ q : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homology n ≃+
      (additiveCechTotal U I).homology n,
      (∀ s : (additiveCechGlobal I).cycles n,
        ∃ t : (additiveCechTotal U I).cycles n,
          (additiveCechTotal U I).iCycles n t =
            additiveCechAlpha U I n ((additiveCechGlobal I).iCycles n s)) ∧
      (∀ z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n,
        ∃ t : (additiveCechTotal U I).cycles n,
          (additiveCechTotal U I).iCycles n t = additiveCechBeta U I n
            ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).iCycles n z)) ∧
      (∀ (s : (additiveCechGlobal I).cycles n) (t : (additiveCechTotal U I).cycles n),
        (additiveCechTotal U I).iCycles n t =
          additiveCechAlpha U I n ((additiveCechGlobal I).iCycles n s) →
        p ((additiveCechGlobal I).homologyπ n s) =
          (additiveCechTotal U I).homologyπ n t) ∧
      (∀ (z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n)
        (t : (additiveCechTotal U I).cycles n),
        (additiveCechTotal U I).iCycles n t = additiveCechBeta U I n
          ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).iCycles n z) →
        q ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homologyπ n z) =
          (additiveCechTotal U I).homologyπ n t) := by
  classical
  obtain ⟨f, hf, hfi⟩ := etaleAdditiveCech_alpha_quasiIso U hcover I
  let : QuasiIso f := hfi
  obtain ⟨c, b, hb, hc, hbc⟩ := exists_additiveCechBeta_homology X U hU hcover I n
  let p := (isoOfQuasiIsoAt f n).addCommGroupIsoToAddEquiv
  let q := AddEquiv.ofBijective b hb
  have hi : Function.Injective ((additiveCechTotal U I).iCycles n) :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  refine ⟨p, q, ?_, ?_, ?_, ?_⟩
  · intro s
    refine ⟨HomologicalComplex.cyclesMap f n s, ?_⟩
    change (HomologicalComplex.cyclesMap f n ≫ (additiveCechTotal U I).iCycles n) s = _
    rw [HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply, hf]
  · intro z
    exact ⟨c z, hc z⟩
  · intro s t ht
    have he : HomologicalComplex.cyclesMap f n s = t := by
      apply hi
      change (HomologicalComplex.cyclesMap f n ≫ (additiveCechTotal U I).iCycles n) s = _
      rw [HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply, hf, ← ht]
    change HomologicalComplex.homologyMap f n ((additiveCechGlobal I).homologyπ n s) = _
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
      ConcreteCategory.comp_apply, he]
  · intro z t ht
    have he : c z = t := hi ((hc z).trans ht.symm)
    change b ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).homologyπ n z) = _
    rw [hbc, he]

end AlgebraicGeometry.Scheme.Modules
