/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.LocalRing.Basic
import Sheaf.RingTheory.RegularSequenceGradedPolynomial
import Sheaf.RingTheory.QuasiRegularFlatQuotientBaseChange
import Mathlib.RingTheory.TensorProduct.Quotient
import Sheaf.RingTheory.QuasiRegularNoetherianLocal
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Nakayama
import WeilConjectures.RingTheory.RegularSequenceFlatClosedFiber

/-!
# Regular generation of a flat quotient ideal on the closed fibre

Source: Stacks Project, More on Algebra, Tag 0CEP, and Algebra, Tags 00MG and 00DV
(blueprint: lem-sfb-flat-quotient-ideal-fibre-regularity).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Ideal

/-- For a flat local homomorphism of Noetherian local rings whose quotient by `K`
is flat over the source, regular generation of `K` is equivalent to regular generation
of its image in the closed fibre. Lists include the empty sequence.

Source: Stacks Project, More on Algebra, Tag 0CEP
(`lemma-relative-regular-immersion-algebra`), and Algebra, Tags 00MG and 00DV
(blueprint: lem-sfb-flat-quotient-ideal-fibre-regularity).

Proof:
1. Put `I = m_A T`. Locality gives `I ≤ m_T`, so `T/I` is a nonzero Noetherian
   local ring, and the image of `K` is contained in its maximal ideal.
2. Given regular generators of `K`, use lem-pur-regular-sequence-graded-polynomial
   to identify its associated graded algebra with the polynomial algebra over `T/K`.
   Apply lem-pur-quasi-regular-flat-quotient-base-change with `A/m_A`; the hypothesis
   that `T/K` is flat permits this nonflat base change. Identify the tensor product
   with `T/I` by lem-weil-pbc-tensor-quotient-base-change. The images are quasi-regular,
   hence regular by lem-pur-quasi-regular-noetherian-local, and generate the image ideal.
3. Conversely, tensor `0 → K → T → T/K → 0` with `A/m_A`.
   The flat-quotient injection lem-weil-pbc-flat-quotient-tensor-injective and
   lem-weil-pbc-tensor-over-quotient-ring identify `K/m_A K` with its image in `T/I`.
   In particular `K ∩ I = IK`, where the source action gives `m_A K = IK`.
4. Lift a regular generating list of the image ideal to elements of `K`, generating
   an ideal `J ≤ K`. Step 3 gives `K = J + IK`. The module `K/J` is finite since
   `T` is Noetherian (def-weil-pbc-noetherian-ring). As `I ≤ m_T`, apply
   lem-weil-pbc-nakayama-jacobson to obtain `K/J = 0`, hence `J = K`.
5. Apply lem-weil-pbc-grothendieck-regular-sequence-flat to the chosen lifts:
   regularity of their closed-fibre images implies regularity in `T`.
   For an empty generating list step 4 gives `K = 0`; the empty list is regular
   in each nonzero local ring. Step 2 also permits an empty list.
-/
theorem regularGeneration_iff_closedFibre_of_flat_quotient
    {A : Type u} {T : Type v} [CommRing A] [CommRing T]
    [IsLocalRing A] [IsLocalRing T] [IsNoetherianRing A] [IsNoetherianRing T]
    (a : A →+* T) (hflat : a.Flat)
    (hlocal : (IsLocalRing.maximalIdeal A).map a ≤ IsLocalRing.maximalIdeal T)
    (K : Ideal T) (hK : K ≤ IsLocalRing.maximalIdeal T)
    (hquot : ((Ideal.Quotient.mk K).comp a).Flat) :
    (∃ fs : List T, RingTheory.Sequence.IsRegular T fs ∧ Ideal.ofList fs = K) ↔
      ∃ fs : List (T ⧸ (IsLocalRing.maximalIdeal A).map a),
        RingTheory.Sequence.IsRegular (T ⧸ (IsLocalRing.maximalIdeal A).map a) fs ∧
          Ideal.ofList fs = K.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map a)) := by
  sorry

end Ideal
