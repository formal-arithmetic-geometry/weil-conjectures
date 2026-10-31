/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Blowup.Affine.Functoriality
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Closed fibres from a canonical Rees reduction comparison

Source: ILO, Exposé XX, §4.4, final Note, printed p. 374
(blueprint: lem-per-blowup-closed-fiber-of-rees-reduction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AffineBlowup

/-- A canonical isomorphism of the reduced Rees rings identifies the closed fibres.

Source: ILO, Exposé XX, §4.4, final Note, printed p. 374
(blueprint: lem-per-blowup-closed-fiber-of-rees-reduction).

Proof: the ideal extended from `I` in the Rees ring is homogeneous: its component in
degree `n` is `I * J^n`. Thus coefficientwise application of `f` induces a graded map of
these quotient rings. The formula on all representatives identifies that map with `eR`,
so it is a graded isomorphism, and its degree-zero map is `e₀`. Base change of Proj to
`Spec (A/I)` is the Proj of the Rees ring modulo `I`; likewise over `B`. Apply the graded
isomorphism between these two Proj schemes and compose with the two base-change
isomorphisms. On a standard chart the map sends a fraction `F/s^d` to `f(F)/f(s)^d`.
Consequently its composite with the first projection is the canonical affine blowup map,
and its composite with the second projection is `Spec.map e₀`. These chartwise identities
agree on overlaps and therefore give both claimed equalities globally. This uses arbitrary
Proj base change, not base change of the blowup along an arbitrary nonflat ring map.
When the reduced Rees ring is zero both closed fibres are empty; for the unit centre the
claim is precisely the isomorphism on the two quotient affine schemes.
-/
theorem exists_closedFiberIso_of_reesReduction
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I J : Ideal A)
    (e₀ : A ⧸ I ≃+* B ⧸ I.map f)
    (he₀ : ∀ a : A, e₀ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk _ (f a))
    (eR : reesAlgebra J ⧸ I.map (algebraMap A (reesAlgebra J)) ≃+*
      reesAlgebra (J.map f) ⧸ (I.map f).map (algebraMap B (reesAlgebra (J.map f))))
    (heR : ∀ F : reesAlgebra J,
      eR (Ideal.Quotient.mk _ F) = Ideal.Quotient.mk _ (reesGrading.hom f rfl F)) :
    ∃ e : pullback (AffineBlowup.toSpec (J.map f))
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f)))) ≅
        pullback (AffineBlowup.toSpec J)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))),
      e.hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ AffineBlowup.hom f rfl ∧
      e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ≫
        Spec.map (CommRingCat.ofHom e₀.toRingHom) := by sorry

end AlgebraicGeometry.AffineBlowup
