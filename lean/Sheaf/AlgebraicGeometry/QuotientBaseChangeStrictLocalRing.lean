/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.AlgebraicGeometry.QuotientBaseChangeAffineModel
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian

/-! # Strict local rings of a base change by a quotient

Source: Stacks Project, Tag 05WS (lemma-quotient-strict-henselization)
(blueprint: lem-trf-quotient-base-change-strict-local-ring).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The strict local ring of the inverse image of `Spec (A/I)` is the quotient of the
ambient strict local ring by the extended ideal, with its canonical quotient map.
Source: Stacks Project, Tags 05WS and 01JO
(blueprint: lem-trf-quotient-base-change-strict-local-ring).

Proof: The quotient spectrum is a closed subscheme and its base change is a closed
immersion i. The closed-immersion strict-localization Cartesian theorem identifies
`Spec H_z` with `Z ×_X Spec H_w`. Paste the defining square of Z to identify this
with `Spec H_w ×_Spec A Spec (A/I)`. The affine quotient calculation identifies
its ring with `H_w / I H_w`. All maps in these identifications are the projections,
so the induced ring equivalence composed with the quotient map equals the
functorial strict-local ring map. Full faithfulness of Spec gives the equation. -/
theorem quotient_base_change_strict_local_ring {X : Scheme.{u}} (A : CommRingCat.{u})
    (p : X ⟶ Spec A) (I : Ideal A)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (z : Spec (.of Ω) ⟶ pullback p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :
    ∃ e : (strictHenselizationRing (z ≫ pullback.fst _ _) ⧸
        Ideal.map (Spec.preimage
          (strictHenselizationStructuralMap (z ≫ pullback.fst _ _) ≫ p)).hom I) ≃+*
        strictHenselizationRing z,
      e.toRingHom.comp (Ideal.Quotient.mk _) =
        (Spec.preimage (strictHenselizationMap (pullback.fst _ _) z)).hom := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let i := pullback.fst p q
  let w := z ≫ i
  let c := pullback.lift (f := i) (g := strictHenselizationStructuralMap w)
    (strictHenselizationStructuralMap z) (strictHenselizationMap i z)
    (strictHenselizationMap_over i z).symm
  have hq : IsClosedImmersion q := IsClosedImmersion.spec_of_quotient_mk I
  have hi : IsClosedImmersion i := inferInstance
  have hc : IsIso c := isIso_strictHenselizationClosedImmersionCartesian i z
  obtain ⟨e, he⟩ := quotient_base_change_affine_model A p I
    (strictHenselizationRing w) (strictHenselizationStructuralMap w)
  let Q : CommRingCat.{u} := .of (strictHenselizationRing w ⧸
    Ideal.map (Spec.preimage (strictHenselizationStructuralMap w ≫ p)).hom I)
  let E : Spec (strictHenselizationRing z) ≅ Spec Q := asIso c ≪≫ e
  let eC : Q ≅ strictHenselizationRing z :=
    (Scheme.Spec.preimageIso (X := Opposite.op (strictHenselizationRing z))
      (Y := Opposite.op Q) E).unop
  let eR := eC.commRingCatIsoToRingEquiv
  refine ⟨eR, ?_⟩
  apply congrArg CommRingCat.Hom.hom
  change CommRingCat.ofHom (Ideal.Quotient.mk _) ≫
      eC.hom = Spec.preimage (strictHenselizationMap i z)
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_preimage]
  have hE : Spec.map eC.hom = E.hom := by
    exact Spec.map_preimage (R := Q) (S := strictHenselizationRing z) E.hom
  rw [hE]
  change (c ≫ e.hom) ≫ _ = _
  rw [Category.assoc, he]
  exact pullback.lift_snd _ _ _

end AlgebraicGeometry.Scheme
