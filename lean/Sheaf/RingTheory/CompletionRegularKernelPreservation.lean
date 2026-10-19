/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import WeilConjectures.RingTheory.LocalCompletionQuotient
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Regular.RegularSequence
import Sheaf.RingTheory.LocalGeneratingTuples
import Sheaf.RingTheory.QuasiRegularNoetherianLocal
import WeilConjectures.RingTheory.RegularSequenceConormal
import Sheaf.RingTheory.RegularSequenceGradedPolynomial
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-!
# Regular sequences and completed quotients

Source: Stacks Project, Algebra, Tags 00MA, 00MB, and 09Q1
(blueprint: lem-trf-completion-regular-kernel-preservation).
-/

@[expose] public section

universe u

open RingTheory

/-- For a Noetherian local ring, regular-sequence generation of an ideal is equivalent
 to regular-sequence generation of the kernel of the canonical map from the local
 completion to the completion of the quotient.

Source: Stacks Project, Algebra, Tags 00MA and 00MB, and Divided Power Algebra Tag 09Q1
(blueprint: lem-trf-completion-regular-kernel-preservation).

Proof: The completion of a quotient is the quotient of the completion by the extended
ideal, and completion is exact on finite modules. These identifications preserve the
successive multiplication maps defining regular sequences. The converse uses the
conormal basis of a regular sequence, Nakayama's lemma, and exactness of completion
to reflect each multiplication map. The empty sequence is included.
-/
theorem completionRegularKernelPreservation
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) (hIfg : I.FG) :
    let B := R ⧸ I
    let m := IsLocalRing.maximalIdeal R
    let n := Ideal.map (Ideal.Quotient.mk I) m
    let c := AdicCompletion.exists_local_completion_quotient R B
      (Ideal.Quotient.mk I) (Ideal.Quotient.mk_surjective)
    let q : AdicCompletion m R →+* AdicCompletion n B := c.2.choose
    Function.Surjective q ∧
      ((∃ xs : List R,
        RingTheory.Sequence.IsRegular R xs ∧
          Ideal.ofList xs = I ∧
            ∀ x ∈ xs, x ∈ m) ↔
      (∃ ys : List (AdicCompletion m R),
        RingTheory.Sequence.IsRegular (AdicCompletion m R) ys ∧
          Ideal.ofList ys = RingHom.ker q ∧
            ∀ y ∈ ys, y ∈ IsLocalRing.maximalIdeal (AdicCompletion m R))) := by
  sorry

end
