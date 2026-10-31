/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions

/-! # Affine charts of base change by a quotient

Source: Stacks Project, Tag 01JO, affine fibre products
(blueprint: lem-trf-quotient-base-change-affine-model).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Pulling back `Spec (A/I)` gives the quotient by the extended ideal on each affine chart.
There is no reducedness or finiteness assumption on the ideal.
Source: Stacks Project, Tag 01JO (section-fibre-products), affine construction
(blueprint: lem-trf-quotient-base-change-affine-model).

Proof: Paste the two pullback squares to identify the source with the pullback of
`j ≫ p` and `Spec (A/I) → Spec A`. Full faithfulness of Spec identifies `j ≫ p`
with the ring map `A → D`. The affine pullback formula identifies this with
`Spec (D ⊗[A] (A/I))`. The ring maps `d ⊗ ā ↦ d * ā` and `d̄ ↦ d ⊗ 1`
are well defined: balancing gives the first map and the image of I vanishes for
the second. They are inverse on pure tensors and quotient representatives.
The first projection becomes the quotient homomorphism `D → D/ID`, proving
also the displayed equation. -/
theorem quotient_base_change_affine_model {X : Scheme.{u}} (A : CommRingCat.{u})
    (p : X ⟶ Spec A) (I : Ideal A) (D : CommRingCat.{u}) (j : Spec D ⟶ X) :
    ∃ e : pullback (pullback.fst p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) j ≅
        Spec (.of (D ⧸ Ideal.map (Spec.preimage (j ≫ p)).hom I)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) = pullback.snd _ j := by
  let φ : A ⟶ D := Spec.preimage (j ≫ p)
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let i := pullback.fst p q
  have hn : IsPullback (pullback.snd i j)
      (pullback.fst i j ≫ pullback.snd p q) (j ≫ p) q :=
    (IsPullback.of_hasPullback i j).flip.paste_vert
      (IsPullback.of_hasPullback p q)
  have hs : IsPullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.map φ.hom I))))
      (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap (Ideal.map φ.hom I) φ.hom Ideal.le_comap_map))) (j ≫ p) q := by
    simpa only [φ, Spec.map_preimage] using
      (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_quotient φ I)).flip
  refine ⟨hn.isoPullback ≪≫ hs.isoPullback.symm, ?_⟩
  change (hn.isoPullback.hom ≫ hs.isoPullback.inv) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.map φ.hom I))) = _
  rw [Category.assoc, hs.isoPullback_inv_fst, hn.isoPullback_hom_fst]

end AlgebraicGeometry.Scheme
