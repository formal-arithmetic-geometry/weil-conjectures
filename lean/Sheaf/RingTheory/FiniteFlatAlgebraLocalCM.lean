/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Regular.Flat
import WeilConjectures.RingTheory.DepthLeSupportDimension

/-!
# Cohen–Macaulay prime localizations of finite flat algebras

Source: Stacks Project, Algebra, Tag 00R5 (lemma-finite-flat-over-regular-CM),
second alternative after prime localization; global form used in Tag 045M
(lemma-tensor-fields-CM) (blueprint: lem-trf-finite-flat-algebra-local-cm).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingHom

/-- A finite flat algebra over a Noetherian ring whose prime localizations have depth
equal to dimension is Noetherian, and its prime localizations have depth and dimension
equal to the dimension at the contracted prime.
Source: Stacks Project, Algebra, Tags 00R5 and 045M
(blueprint: lem-trf-finite-flat-algebra-local-cm).

Proof:
1. `lem-weil-pbc-finite-algebra-noetherian` makes B Noetherian. For a prime q of B,
   put p = q.comap φ, R = A_p and S = B_q. By `lem-weil-pbc-flat-local-ring-maps`,
   R and S are Noetherian local rings and the induced map R → S is flat and local.
2. `lem-weil-pbc-finite-algebra-is-integral` makes φ integral. By
   `lem-weil-pbc-integral-incomparability`, strict chains below q contract to strict
   chains below p. The chain description in
   `lem-weil-pbc-localization-dimension-chains-below-prime` gives dim S ≤ dim R.
   This does not require that R → S be finite or integral.
3. By `lem-weil-pbc-noetherian-local-finite-krull-dimension`, dim R is a natural d.
   The hypothesis gives depth R = d. The supremum defining `def-weil-pbc-depth`
   therefore contains a regular sequence of length d: if d > 0 and every length
   were smaller, d - 1 would be an upper bound. For d = 0 take the empty sequence;
   R is nonzero because p is prime. This uses `def-weil-pbc-regular-sequence`.
4. `lem-weil-pbc-flat-local-hom-faithfully-flat` makes R → S faithfully flat.
   By `lem-sfb-regular-sequence-faithfully-flat-ascent`, the image sequence is
   S-regular, including its nonzero final quotient. Locality puts its entries in
   the maximal ideal, so `def-weil-pbc-depth` gives d ≤ depth S, also for d = 0.
5. Apply `lem-weil-pbc-depth-le-support-dimension` to the nonzero finite S-module S.
   Its support is all Spec S: at a prime P the fraction 1/1 cannot vanish, since
   that would require an element outside P to be zero. Thus depth S ≤ dim S.
   Combining d ≤ depth S ≤ dim S ≤ dim R = d proves both equalities, with dimension
   as in `def-weil-pbc-krull-dimension-ring` and prime localizations as in
   `def-weil-pbc-localization-at-prime`. If B is zero there are no q, and the
   Noetherianity assertion already proves the conclusion. -/
theorem finite_flat_algebra_local_depth_eq_dimension
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (hCM : ∀ (p : Ideal A) [p.IsPrime],
      (IsLocalRing.depth (R := Localization.AtPrime p) (Localization.AtPrime p) : WithBot ℕ∞) =
        ringKrullDim (Localization.AtPrime p))
    (φ : A →+* B) (hfinite : @Module.Finite A B _ _ φ.toAlgebra.toModule)
    (hflat : φ.Flat) :
    IsNoetherianRing B ∧ ∀ (q : Ideal B) [q.IsPrime],
      IsNoetherianRing (Localization.AtPrime q) ∧ IsLocalRing (Localization.AtPrime q) ∧
        (IsLocalRing.depth (R := Localization.AtPrime q) (Localization.AtPrime q) : WithBot ℕ∞) =
          ringKrullDim (Localization.AtPrime q) ∧
        ringKrullDim (Localization.AtPrime q) =
          ringKrullDim (Localization.AtPrime (q.comap φ)) := by
  sorry

end RingHom
