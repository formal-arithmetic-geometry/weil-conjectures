/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField

/-!
# Residue field of a point of a fibre product

## References

* [Stacks Project, Tag 01JT](https://stacks.math.columbia.edu/tag/01JT)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Pullback

set_option backward.isDefEq.respectTransparency false in
private theorem residueField_equiv_ofPointTensor_core {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g)) :
    let T := Triplet.ofPoint z
    let ψ := (ofPointTensor z).hom
    let p := RingHom.ker ψ
    letI : p.IsPrime := RingHom.ker_isPrime ψ
    ∃ e : p.ResidueField ≃+* (pullback f g).residueField z,
      e.toRingHom.comp (algebraMap T.tensor p.ResidueField) = ψ ∧
      e.toRingHom.comp ((algebraMap T.tensor p.ResidueField).comp T.tensorInl.hom) =
        ((pullback.fst f g).residueFieldMap z).hom ∧
      e.toRingHom.comp ((algebraMap T.tensor p.ResidueField).comp T.tensorInr.hom) =
        ((pullback.snd f g).residueFieldMap z).hom := by
  let T := Triplet.ofPoint z
  let ψ := (ofPointTensor z).hom
  obtain ⟨q, hq, l, hker, hl, hcomp, -⟩ :=
    spec_field_point_residue_field_map T.tensor ((pullback f g).residueField z) ψ
  have hqeq : q = ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ := PrimeSpectrum.ext hker
  cases hqeq
  let q : PrimeSpectrum T.tensor := ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩
  have hz : T.SpecTensorTo q = z := by
    change T.SpecTensorTo ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ = z
    rw [← hq]
    change (Spec.map (ofPointTensor z) ≫ T.SpecTensorTo) _ = z
    rw [ofPointTensor_SpecTensorTo]
    simp
  let L := (Scheme.Spec.residueFieldIso T.tensor q).hom ≫ l
  have hfac : Spec.map L ≫ (Spec T.tensor).fromSpecResidueField q =
      Spec.map (ofPointTensor z) := by
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    rw [← Spec.map_comp_assoc]
    simp only [L, Iso.inv_hom_id_assoc]
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact hcomp
  let d := ((pullback f g).residueFieldCongr hz).inv ≫
    T.SpecTensorTo.residueFieldMap q
  have hdpoint : Spec.map d ≫ (pullback f g).fromSpecResidueField z =
      (Spec T.tensor).fromSpecResidueField q ≫ T.SpecTensorTo := by
    dsimp only [d]
    rw [Spec.map_comp, Category.assoc]
    change Spec.map (T.SpecTensorTo.residueFieldMap q) ≫
      Spec.map ((pullback f g).residueFieldCongr hz.symm).hom ≫ _ = _
    rw [Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have hd : d ≫ L = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id]
    apply (cancel_mono ((pullback f g).fromSpecResidueField z)).mp
    rw [Category.assoc, hdpoint, ← Category.assoc, hfac,
      ofPointTensor_SpecTensorTo]
    exact (Category.id_comp _).symm
  have hsurj : Function.Surjective l.hom := by
    intro x
    refine ⟨((Scheme.Spec.residueFieldIso T.tensor q).hom).hom (d.hom x), ?_⟩
    exact congrArg (fun h => h.hom x) hd
  let e := RingEquiv.ofBijective l.hom ⟨RingHom.injective l.hom, hsurj⟩
  have hinl : ψ.comp T.tensorInl.hom = ((pullback.fst f g).residueFieldMap z).hom := by
    change (T.tensorInl ≫ ofPointTensor z).hom = _
    exact congrArg CommRingCat.Hom.hom (pushout.inl_desc _ _ _)
  have hinr : ψ.comp T.tensorInr.hom = ((pullback.snd f g).residueFieldMap z).hom := by
    change (T.tensorInr ≫ ofPointTensor z).hom = _
    exact congrArg CommRingCat.Hom.hom (pushout.inr_desc _ _ _)
  dsimp only
  refine ⟨e, hcomp, ?_, ?_⟩
  · exact (congrArg (fun h => h.comp T.tensorInl.hom) hcomp).trans hinl
  · exact (congrArg (fun h => h.comp T.tensorInr.hom) hcomp).trans hinr

set_option backward.isDefEq.respectTransparency false in
/-- The residue field of the kernel of the canonical tensor map is isomorphic to the residue
field of the point, compatibly with both factor fields. If the tensor quotient is already a
field, its induced map is likewise an isomorphism compatible with both factors
(Stacks, Tag 01JT). -/
theorem exists_residueField_equiv_ofPointTensor {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g)) :
    let T := Triplet.ofPoint z
    let ψ := (ofPointTensor z).hom
    let p := RingHom.ker ψ
    letI : p.IsPrime := RingHom.ker_isPrime ψ
    (∃ e : p.ResidueField ≃+* (pullback f g).residueField z,
      e.toRingHom.comp (algebraMap T.tensor p.ResidueField) = ψ ∧
      e.toRingHom.comp ((algebraMap T.tensor p.ResidueField).comp T.tensorInl.hom) =
        ((pullback.fst f g).residueFieldMap z).hom ∧
      e.toRingHom.comp ((algebraMap T.tensor p.ResidueField).comp T.tensorInr.hom) =
        ((pullback.snd f g).residueFieldMap z).hom) ∧
    (IsField (T.tensor ⧸ p) →
      ∃ e : (T.tensor ⧸ p) ≃+* (pullback f g).residueField z,
        e.toRingHom.comp (Ideal.Quotient.mk p) = ψ ∧
        e.toRingHom.comp ((Ideal.Quotient.mk p).comp T.tensorInl.hom) =
          ((pullback.fst f g).residueFieldMap z).hom ∧
        e.toRingHom.comp ((Ideal.Quotient.mk p).comp T.tensorInr.hom) =
          ((pullback.snd f g).residueFieldMap z).hom) := by
  dsimp
  obtain ⟨e, he, hl, hr⟩ := residueField_equiv_ofPointTensor_core f g z
  refine ⟨⟨e, he, hl, hr⟩, ?_⟩
  intro hfield
  let T := Triplet.ofPoint z
  let ψ := (ofPointTensor z).hom
  let p := RingHom.ker ψ
  let : p.IsPrime := RingHom.ker_isPrime ψ
  have hsurj : Function.Surjective (algebraMap (T.tensor ⧸ p) p.ResidueField) :=
    IsFractionRing.surjective_iff_isField.mpr hfield
  let a := RingEquiv.ofBijective (algebraMap (T.tensor ⧸ p) p.ResidueField)
    ⟨IsFractionRing.injective _ _, hsurj⟩
  let e' := a.trans e
  have he' : e'.toRingHom.comp (Ideal.Quotient.mk p) = ψ := by
    change e.toRingHom.comp
      ((algebraMap (T.tensor ⧸ p) p.ResidueField).comp (Ideal.Quotient.mk p)) = ψ
    exact he
  refine ⟨e', he', ?_, ?_⟩
  · change (e'.toRingHom.comp (Ideal.Quotient.mk p)).comp T.tensorInl.hom = _
    rw [he']
    exact (congrArg (fun h => h.comp T.tensorInl.hom) he.symm).trans hl
  · change (e'.toRingHom.comp (Ideal.Quotient.mk p)).comp T.tensorInr.hom = _
    rw [he']
    exact (congrArg (fun h => h.comp T.tensorInr.hom) he.symm).trans hr

end AlgebraicGeometry.Scheme.Pullback
