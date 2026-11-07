/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Etaleness of the affine fibre algebra

Source: Stacks Project, Tag 0BJF, fibre-algebra argument.
(blueprint: lem-sbc-affine-fibre-tensor-etale)
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- An affine fibre is etale precisely when its residue-field tensor algebra is etale.

Source: Stacks Project, Tag 0BJF, fibre-algebra argument, and affine base change.
(blueprint: lem-sbc-affine-fibre-tensor-etale)

Proof: The point morphism factors through the affine open U because y belongs to U.
Pullback along this factorization identifies the fibre of f with the fibre of its
restriction to U. The restriction has affine source since f is affine, so writing
R = Gamma(Y,U), B = Gamma(X,f inverse U), k = kappa(y), the affine pullback formula
identifies this fibre with Spec(k tensor_R B), with structure map induced by k to
k tensor_R B. This identification is over Spec(k). Etaleness is invariant under
isomorphisms over the base, and for Spec of a ring homomorphism it is equivalent to
etaleness of the ring homomorphism, hence of its algebra. This also covers the zero
algebra: its spectrum is empty and both the algebra and scheme morphism are etale. -/
theorem etale_fibre_iff_etale_tensor_section_algebra
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1) :
    letI := (f.app U.1).hom.toAlgebra
    letI := (Y.evaluation U.1 y hy).hom.toAlgebra
    Etale (f.fiberToSpecResidueField y) ↔
      Algebra.Etale (Y.residueField y)
        (TensorProduct (Γ(Y, U.1)) (Y.residueField y) (Γ(X, f ⁻¹ᵁ U.1))) := by
  let := (f.app U.1).hom.toAlgebra
  let := (Y.evaluation U.1 y hy).hom.toAlgebra
  let hB := U.2.preimage f
  have hchart : IsPullback (Spec.map (f.app U.1)) hB.fromSpec U.2.fromSpec f := by
    apply IsOpenImmersion.isPullback
    · simpa only [Hom.appLE_eq_app] using (IsAffineOpen.SpecMap_appLE_fromSpec f U.2 hB le_rfl).symm
    · simp
  have heval : Spec.map (Y.evaluation U.1 y hy) ≫ U.2.fromSpec =
      Y.fromSpecResidueField y := by
    rw [evaluation, Spec.map_comp, Category.assoc,
      ← IsAffineOpen.fromSpecStalk, IsAffineOpen.fromSpecStalk_eq_fromSpecStalk]
    rfl
  let R := Γ(Y, U.1)
  let B := Γ(X, f ⁻¹ᵁ U.1)
  let k := Y.residueField y
  let e := pullbackSpecIso R k B
  have ht : IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap k (TensorProduct R k B))))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom)))
      (Spec.map (Y.evaluation U.1 y hy)) (Spec.map (f.app U.1)) := by
    apply IsPullback.of_iso_pullback _ e.symm
    · exact pullbackSpecIso_inv_fst' R k B
    · exact pullbackSpecIso_inv_snd R k B
    · constructor
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext r
      simp [R, B, k, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  have hf := ht.flip.paste_horiz hchart.flip
  rw [heval] at hf
  change Etale (pullback.snd f (Y.fromSpecResidueField y)) ↔ _
  rw [← hf.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso (P := @Etale)]
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap

end AlgebraicGeometry.Scheme
