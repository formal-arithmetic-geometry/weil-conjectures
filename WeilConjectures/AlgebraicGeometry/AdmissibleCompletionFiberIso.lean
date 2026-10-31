/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Blowup.Affine.Functoriality
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.AlgebraicGeometry.Pullbacks


/-! # Infinitesimal fibres of corresponding admissible blowups

Source: ILO, Travaux de Gabber, XX 4.4, final Note, p.374, and XX 2.4.3,
p.364 (blueprint: lem-per-admissible-completion-fiber-iso).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The two infinitesimal fibres are isomorphic by the canonical comparison, specified
by both projections. In particular, the isomorphism is not an independently chosen map.

Source: ILO XX 4.4 final Note, p.374; XX 2.4.3, p.364
(blueprint: lem-per-admissible-completion-fiber-iso).

Proof: equality of radicals and finite generation of I give r ≥ 1 with I^r ≤ J.
For each d, the ideals J^d and I^n J^d contain I^(n+rd). The canonical isomorphism
A/I^N ≃ A'/I^N A' therefore induces isomorphisms on the two ambient quotients by
these ideals. Taking kernels gives J^d/I^n J^d ≃ J^d A'/I^n J^d A'. These are the
canonical congruences recorded in admissibleModificationSystem. Their maps respect
multiplication, so their direct sum identifies the reduced Rees algebras, preserving
the degree-zero quotient map and every homogeneous generator. Arbitrary base change
of Proj identifies the two pullbacks with the Proj schemes of these reduced algebras.
The graded isomorphism gives e. On the chart at a ∈ J it sends z/a^d to its canonical
image, hence its first projection is the Rees blowup comparison. The degree-zero map
is the displayed quotientMap, proving the second projection identity. For I = 0 use
r = 1; the argument also covers nilpotent ideals and empty blowups. No flatness of
A → A' or regularity assumption on a generator is used. -/
theorem admissibleCompletion_fiber_iso {A : Type u} [CommRing A]
    (I : Ideal A) [HenselianRing A I] (hI : I.FG)
    (J : Ideal A) (hJ : J.FG) (hJI : J.radical = I.radical)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ e :
      pullback (AffineBlowup.toSpec (J.map (algebraMap A (AdicCompletion I A))))
          (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk ((I ^ n).map (algebraMap A (AdicCompletion I A)))))) ≅
        pullback (AffineBlowup.toSpec J)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))),
      e.hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫
        AffineBlowup.hom (algebraMap A (AdicCompletion I A)) rfl ∧
      e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ≫
        Spec.map (CommRingCat.ofHom
          (Ideal.quotientMap ((I ^ n).map (algebraMap A (AdicCompletion I A)))
            (algebraMap A (AdicCompletion I A)) Ideal.le_comap_map)) := by sorry

end AlgebraicGeometry
