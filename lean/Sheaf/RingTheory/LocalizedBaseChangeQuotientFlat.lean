/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Flat quotients after localized base change

Source: Stacks Project, Algebra, Tag 00MO.
(blueprint: lem-weil-pbc-localized-base-change-quotient-flat)
-/

@[expose] public section

universe u v w z t

open scoped TensorProduct

namespace Module

/-- Flatness of the quotient after localized base change.
Source: Stacks Project, Algebra, Tag 00MO, proof, first paragraph; Tags 00HI, 00CS, 00DK.
(blueprint: lem-weil-pbc-localized-base-change-quotient-flat)

Proof:
1. Set A = S tensor_R R', N = R' tensor_R M and J = IR'. Tensor cancellation
   identifies S' tensor_S M with S' tensor_A N; the formula sends
   c' tensor (r' tensor x) to c' algebraMap(R', S')(r') tensor x.
   Thus the latter module is the localization of N at W.
2. Put Q = R/I and Q' = R'/J. The quotient map R to Q' factors uniquely through Q,
   since each element of I maps into J. The mutually inverse maps
   (q' tensor (q tensor x)) to q'q tensor x and (q' tensor x) to
   q' tensor (1 tensor x) identify Q' tensor_Q (Q tensor_R M) with Q' tensor_R M.
   Base change of the flat Q-module Q tensor_R M makes this a flat Q'-module.
3. The quotient-tensor equivalence identifies Q' tensor_R M with N/JN.
   Localization is exact, so localizing N to M' also localizes N/JN to M'/JM'.
   For an injective Q'-linear map U to V, tensoring with N/JN is injective by step 2.
   Localize this injection at W. Tensor/localization compatibility identifies its
   source and target with U tensor_Q' (M'/JM') and V tensor_Q' (M'/JM'), respectively.
   Exactness keeps it injective. Hence M'/JM' is Q'-flat.
4. The quotient-tensor equivalence identifies M'/JM' with Q' tensor_R' M',
   preserving the Q'-action because the quotient map R' to Q' is surjective.

Neither finiteness, Noetherianity, locality, nor properness of I is needed. -/
theorem flat_quotient_localized_baseChange
    {R : Type u} {S : Type v} {R' : Type w} {S' : Type z}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
    [IsScalarTower R S S'] [IsScalarTower R R' S']
    (I : Ideal R)
    (M : Type t) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M]
    (hloc : ∃ (q : S ⊗[R] R' →+* S') (W : Submonoid (S ⊗[R] R')),
      (∀ (s : S) (r' : R'), q (s ⊗ₜ[R] r') =
        algebraMap S S' s * algebraMap R' S' r') ∧
      (letI := q.toAlgebra; IsLocalization W S'))
    (hquot : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)) :
    Module.Flat (R' ⧸ I.map (algebraMap R R'))
      ((R' ⧸ I.map (algebraMap R R')) ⊗[R'] (S' ⊗[S] M)) := by
  sorry

end Module
