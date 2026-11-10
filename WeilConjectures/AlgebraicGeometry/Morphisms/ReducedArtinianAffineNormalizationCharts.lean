/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.Artinian.Defs
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Artinian.Module
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteAffineNormalizationCoproduct

/-! # ReducedArtinianAffineNormalizationCharts

Source: Stacks Project and Mathlib.
(blueprint: lem-sbc-reduced-artinian-affine-normalization-charts) -/

@[expose] public section

universe u
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem affine_normalization_iso (A : CommRingCat.{u}) (D : Type u)
    [CommRing D] [Algebra A D] :
    ∃ n : Spec (CommRingCat.of (integralClosure A D)) ≅
        (Spec.map (CommRingCat.ofHom (algebraMap A D))).normalization,
      n.hom ≫ (Spec.map (CommRingCat.ofHom (algebraMap A D))).fromNormalization =
        Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A D))) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A D))
  let G := Γ(Spec A, ⊤)
  let H := Γ(Spec (CommRingCat.of D), ⊤)
  let : Algebra G H := f.appTop.hom.toAlgebra
  let C := integralClosure G H
  let S := integralClosure A D
  let s : G ≃+* A := (ΓSpecIso A).commRingCatIsoToRingEquiv
  let t : H ≃+* D := (ΓSpecIso (CommRingCat.of D)).commRingCatIsoToRingEquiv
  have h : (algebraMap A D).comp s.toRingHom = t.toRingHom.comp (algebraMap G H) := by
    exact congrArg CommRingCat.Hom.hom
      (ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A D))).symm
  have h' : (algebraMap G H).comp s.symm.toRingHom =
      t.symm.toRingHom.comp (algebraMap A D) := by
    ext x
    apply t.injective
    simpa using congrArg (fun f ↦ f (s.symm x)) h.symm
  let w : C ≃+* S :=
    { toFun := fun x ↦ ⟨t x, x.property.map_of_comp_eq s.toRingHom t.toRingHom h⟩
      invFun := fun x ↦ ⟨t.symm x,
        x.property.map_of_comp_eq s.symm.toRingHom t.symm.toRingHom h'⟩
      left_inv := fun x ↦ Subtype.ext (t.symm_apply_apply x)
      right_inv := fun x ↦ Subtype.ext (t.apply_symm_apply x)
      map_mul' := fun x y ↦ Subtype.ext (t.map_mul x y)
      map_add' := fun x y ↦ Subtype.ext (t.map_add x y) }
  let U : (Spec A).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let c : Spec (CommRingCat.of S) ⟶ f.normalization :=
    Spec.map w.toCommRingCatIso.hom ≫ f.normalizationOpenCover.f U
  have hr : (f.normalizationOpenCover.f U).opensRange = ⊤ := by
    rw [← f.fromNormalization_preimage U]
    rfl
  let : IsIso (f.normalizationOpenCover.f U) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ hr
  let : IsIso c := by dsimp [c]; infer_instance
  refine ⟨asIso c, ?_⟩
  change c ≫ f.fromNormalization = _
  dsimp only [c]
  rw [Category.assoc, f.ι_fromNormalization U]
  simp only [IsAffineOpen.fromSpec_top, isoSpec_Spec_inv,
    ← Spec.map_comp, Category.assoc]
  congr 1
  ext x
  change t (algebraMap G H (s.symm x)) = algebraMap A D x
  simpa using congrArg (fun f ↦ f (s.symm x)) h.symm

set_option backward.isDefEq.respectTransparency false in
/-- Residue-field integral-closure charts for one reduced Artinian affine algebra.

Source: Stacks Project, Tags 035H and 035I; Mathlib IsArtinianRing.equivPi.
Proof: First identify the normalization of any affine A-algebra D with
Spec (integralClosure A D). The normalization open-cover chart over the
whole of Spec A is an isomorphism, since its open range is the preimage
of the whole base. Transport its integral-closure ring across the global
section isomorphisms Gamma(Spec A) = A and Gamma(Spec D) = D. Integrality
is preserved in both directions by these commuting ring isomorphisms,
and naturality of GammaSpecIso proves the structural equation.
Now IsArtinianRing.equivPi identifies the reduced Artinian ring D with
the finite product of its quotients D/P by maximal ideals. Apply Spec,
use sigmaSpec to identify the product spectrum with the coproduct, and
reindex the finite maximal spectrum by Fin r. Quotient maps are precisely
the coordinates of equivPi, so this identification is over Spec A with
the quotient-induced algebra structures. Apply
finite_affine_normalization_coproduct to this presentation. Its coproduct
open cover selects the component containing the inverse image of x.
The affine normalization isomorphism for that quotient, followed by the
summand inclusion and the normalization isomorphism, is the requested
open immersion. The two structural equations give its structural map;
the inverse affine isomorphism gives a preimage of x. Zero rings have
empty maximal spectrum, so the same cover argument handles them without
an extra nontriviality assumption. No product-of-integral-closures lemma
or additional localization argument is needed.
(blueprint: lem-sbc-reduced-artinian-affine-normalization-charts) -/
theorem reduced_artinian_affine_normalization_charts
    (A : CommRingCat.{u}) (D : Type u) [CommRing D] [Algebra A D]
    [IsArtinianRing D] [_root_.IsReduced D]
    (x : (Spec.map (CommRingCat.ofHom (algebraMap A D))).normalization) :
    ∃ (P : Ideal D) (hP : P.IsMaximal),
    letI := hP
    let F := D ⧸ P
    letI := ((Ideal.Quotient.mk P).comp (algebraMap A D)).toAlgebra
    let S := integralClosure A F
    ∃ c : Spec (CommRingCat.of S) ⟶
        (Spec.map (CommRingCat.ofHom (algebraMap A D))).normalization,
      IsOpenImmersion c ∧
      c ≫ (Spec.map (CommRingCat.ofHom (algebraMap A D))).fromNormalization =
        Spec.map (CommRingCat.ofHom (algebraMap A S)) ∧ x ∈ Set.range c  := by
  classical
  let : Fintype (MaximalSpectrum D) := Fintype.ofFinite _
  let r := Fintype.card (MaximalSpectrum D)
  let v : MaximalSpectrum D ≃ Fin r := Fintype.equivFin _
  let Q (i : Fin r) := D ⧸ (v.symm i).asIdeal
  let (i : Fin r) : Algebra A (Q i) :=
    ((Ideal.Quotient.mk (v.symm i).asIdeal).comp (algebraMap A D)).toAlgebra
  let E := (IsArtinianRing.equivPi D).toRingEquiv
  let ZM (P : MaximalSpectrum D) := Spec (CommRingCat.of (D ⧸ P.asIdeal))
  let Z (i : Fin r) := Spec (CommRingCat.of (Q i))
  let e : Spec (CommRingCat.of D) ≅ ∐ Z :=
    (Scheme.Spec.mapIso E.toCommRingCatIso.op).symm ≪≫
      (asIso (sigmaSpec (fun P : MaximalSpectrum D ↦
        CommRingCat.of (D ⧸ P.asIdeal)))).symm ≪≫
          (Sigma.reindex v.symm ZM).symm
  let f := Spec.map (CommRingCat.ofHom (algebraMap A D))
  have he : e.hom ≫ Sigma.desc (fun i : Fin r ↦
      Spec.map (CommRingCat.ofHom (algebraMap A (Q i)))) = f := by
    rw [← cancel_epi e.inv]
    simp only [Iso.inv_hom_id_assoc]
    dsimp only [e]
    simp only [Iso.trans_inv, Iso.symm_inv, asIso_hom, Scheme.Spec.mapIso_hom]
    apply Sigma.hom_ext
    intro i
    simp only [Category.assoc, Sigma.ι_comp_desc]
    rw [show Sigma.ι Z i = Sigma.ι (ZM ∘ v.symm) i from rfl]
    rw [Sigma.ι_reindex_hom_assoc]
    simp only [ZM, ι_sigmaSpec_assoc]
    dsimp only [f]
    simp only [Scheme.Spec_map, Iso.op_hom, Quiver.Hom.unop_op, ← Spec.map_comp]
    congr 1
  obtain ⟨n, hn⟩ := finite_affine_normalization_coproduct A r Q _ f e he
  let N (i : Fin r) := (Spec.map (CommRingCat.ofHom (algebraMap A (Q i)))).normalization
  obtain ⟨i, y, hy⟩ := (sigmaOpenCover N).exists_eq (n.inv x)
  obtain ⟨s, hs⟩ := affine_normalization_iso A (Q i)
  refine ⟨(v.symm i).asIdeal, (v.symm i).isMaximal,
    s.hom ≫ Sigma.ι N i ≫ n.hom, ?_, ?_, ?_⟩
  · infer_instance
  · rw [Category.assoc, Category.assoc, hn, hs]
  · refine ⟨s.inv y, ?_⟩
    rw [Hom.comp_apply]
    have hsy : s.hom (s.inv y) = y := by
      rw [← Hom.comp_apply, s.inv_hom_id]
      rfl
    rw [hsy, Hom.comp_apply]
    change n.hom ((sigmaOpenCover N).f i y) = x
    rw [hy, ← Hom.comp_apply, n.inv_hom_id]
    rfl

end AlgebraicGeometry.Scheme
