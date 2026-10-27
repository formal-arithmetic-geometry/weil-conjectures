module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Length
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Group.Idempotent

import WeilConjectures.RingTheory.SimpleFiltration

/-!
# Ring invariance of normalization pairs

Source: Stacks Project, Curves, Tag 0C1U (equation-multicross), and Algebra,
Tags 00CP, 00GP, 02LY, 00J3, 00J2 and 00IV. The comparison is the explicit
ring-invariance argument accompanying the multicross normalization computation
(blueprint: lem-trf-normalization-pair-ring-invariance).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v v' w w' t t'

namespace RingEquiv

/-- The additive module quotient of the integral closure in total fractions by the
image of the original ring. This abbreviates the actual quotient, with its canonical
scalar actions; it chooses no normalization model or quotient map.

Source: Stacks Project, Curves, Tag 0C1U (equation-multicross), and Algebra, Tag 00GP
(blueprint: lem-trf-normalization-pair-ring-invariance). -/
abbrev normalizationPairDefect (R : Type v) [CommRing R] :=
  integralClosure R (FractionRing R) ⧸
    (Algebra.linearMap R (integralClosure R (FractionRing R))).range

/-- Ring isomorphisms preserve normalized local pairs, their quotient submodule lattices,
primitive nonzero idempotents, branch counts and defect lengths and dimensions.
The two lattices are pinned to the images under the indicated isomorphisms, and the
quotient isomorphism is pinned on representatives. Scalar compatibility is required
only for the final linearity clause.

Source: Stacks Project, Curves, Tag 0C1U (equation-multicross); Algebra,
Tags 00CP, 00GP, 02LY, 00J3, 00J2 and 00IV
(blueprint: lem-trf-normalization-pair-ring-invariance).

Proof:
1. A ring isomorphism and its inverse preserve non-zero-divisors: pull a vanishing
   product back along the isomorphism and use injectivity. The localization universal
   property (lem-weil-pbc-ring-localization-universal-property, Tag 00CP) therefore
   extends both maps to total fractions. Uniqueness makes them inverse and proves
   uniqueness of the extension. The base rings inject into their total fractions
   because a denominator cannot annihilate a nonzero element.
2. Apply the extended map to a monic equation and apply its inverse for the converse.
   By def-weil-pbc-integral-closure (Tag 00GP), it restricts to the asserted closure
   isomorphism E, compatible with the original ring isomorphism.
3. Send [z] to [E(z)]. Changing z by h changes E(z) by the image of h, so the map is
   well defined. The inverse construction is inverse, and multiplicativity gives
   T(h m) = phi(h) T(m).
4. Send submodules to their images under T, or under E for the closures. Surjectivity
   of phi and the semilinear identities make those images submodules over the other
   ring. Inverse images give inverse order maps. Strict chains and their lengths
   correspond, giving equality of lengths (def-weil-pbc-module-length, Tag 02LY).
5. Each strict submodule chain of a defect is a strict chain of k-subspaces, bounded
   by its finite dimension. Thus both defects have finite length. Apply
   lem-weil-pbc-finite-length-module-simple-filtration (Tag 00J3) to each one;
   the zero defect has the filtration of length zero.
6. For a nonzero vector in a simple factor, its cyclic span is the whole factor.
   Its annihilator is maximal, since an intermediate ideal would give a proper
   nonzero submodule (def-weil-pbc-simple-module; Tag 00J2). Locality identifies
   it with the maximal ideal. The structural residue-field identification with k
   makes each factor one-dimensional over k and of length one.
7. Additivity of length (lem-weil-pbc-length-additive-short-exact, Tag 00IV), and
   basis extension in each short exact sequence, show separately that each defect
   has dimension equal to its length. Combine with step 4. No compatibility of the
   two structural maps from k was used.
8. E and its inverse preserve idempotency, nonzeroness and orthogonal decompositions.
   In a finite product of domains every idempotent coordinate is zero or one.
   A nonempty support is primitive exactly when it is a singleton: otherwise split
   it into two disjoint nonempty supports. Hence the number of primitive nonzero
   idempotents is the number of factors, and the two branch counts agree.
9. If phi respects k, its fraction extension fixes the structural image of k.
   Multiplicativity gives k-linearity of that extension, of E and of T.
-/
theorem normalization_pair_ring_invariance
    (k : Type u) [Field k]
    (H : Type v) [CommRing H] [IsLocalRing H] [IsNoetherianRing H] [IsReduced H]
    [Algebra k H]
    (H' : Type v') [CommRing H'] [IsLocalRing H'] [IsNoetherianRing H'] [IsReduced H']
    [Algebra k H']
    (hres : Function.Bijective ((IsLocalRing.residue H).comp (algebraMap k H)))
    (hres' : Function.Bijective ((IsLocalRing.residue H').comp (algebraMap k H')))
    [Module.Finite H (integralClosure H (FractionRing H))]
    [Module.Finite H' (integralClosure H' (FractionRing H'))]
    [FiniteDimensional k (normalizationPairDefect H)]
    [FiniteDimensional k (normalizationPairDefect H')]
    (I : Type w) [Finite I] [Nonempty I]
    (S : I → Type t) [∀ i : I, CommRing (S i)] [∀ i : I, IsLocalRing (S i)]
    [∀ i : I, IsDomain (S i)]
    (decomp : integralClosure H (FractionRing H) ≃+* ∀ i : I, S i)
    (I' : Type w') [Finite I'] [Nonempty I']
    (S' : I' → Type t') [∀ i : I', CommRing (S' i)] [∀ i : I', IsLocalRing (S' i)]
    [∀ i : I', IsDomain (S' i)]
    (decomp' : integralClosure H' (FractionRing H') ≃+* ∀ i : I', S' i)
    (phi : H ≃+* H') :
    ∃ (F : FractionRing H ≃+* FractionRing H')
      (E : integralClosure H (FractionRing H) ≃+* integralClosure H' (FractionRing H'))
      (T : normalizationPairDefect H ≃+ normalizationPairDefect H')
      (L : Submodule H (normalizationPairDefect H) ≃o
        Submodule H' (normalizationPairDefect H'))
      (LC : Submodule H (integralClosure H (FractionRing H)) ≃o
        Submodule H' (integralClosure H' (FractionRing H'))),
      (∀ h : H, F (algebraMap H (FractionRing H) h) =
        algebraMap H' (FractionRing H') (phi h)) ∧
      (∀ F' : FractionRing H ≃+* FractionRing H',
        (∀ h : H, F' (algebraMap H (FractionRing H) h) =
          algebraMap H' (FractionRing H') (phi h)) → F' = F) ∧
      (∀ z : integralClosure H (FractionRing H),
        (E z : FractionRing H') = F (z : FractionRing H)) ∧
      (∀ z : integralClosure H (FractionRing H),
        T (Submodule.Quotient.mk z) = Submodule.Quotient.mk (E z)) ∧
      (∀ (h : H) (m : normalizationPairDefect H), T (h • m) = phi h • T m) ∧
      (∀ (N : Submodule H (normalizationPairDefect H)) (m : normalizationPairDefect H),
        T m ∈ L N ↔ m ∈ N) ∧
      (∀ (N : Submodule H (integralClosure H (FractionRing H)))
        (z : integralClosure H (FractionRing H)), E z ∈ LC N ↔ z ∈ N) ∧
      Module.length H (normalizationPairDefect H) < ⊤ ∧
      Module.length H' (normalizationPairDefect H') < ⊤ ∧
      (∀ e : integralClosure H (FractionRing H),
        (IsIdempotentElem e ∧ e ≠ 0 ∧
          ∀ f g : integralClosure H (FractionRing H),
            IsIdempotentElem f → IsIdempotentElem g → f * g = 0 →
              e = f + g → f = 0 ∨ g = 0) ↔
        (IsIdempotentElem (E e) ∧ E e ≠ 0 ∧
          ∀ f g : integralClosure H' (FractionRing H'),
            IsIdempotentElem f → IsIdempotentElem g → f * g = 0 →
              E e = f + g → f = 0 ∨ g = 0)) ∧
      Nat.card I = Nat.card I' ∧
      (Module.finrank k (normalizationPairDefect H) : ℕ∞) =
        Module.length H (normalizationPairDefect H) ∧
      Module.length H (normalizationPairDefect H) =
        Module.length H' (normalizationPairDefect H') ∧
      Module.length H' (normalizationPairDefect H') =
        (Module.finrank k (normalizationPairDefect H') : ℕ∞) ∧
      ((∀ a : k, phi (algebraMap k H a) = algebraMap k H' a) →
        (∀ (a : k) (x : FractionRing H), F (a • x) = a • F x) ∧
        (∀ (a : k) (z : integralClosure H (FractionRing H)), E (a • z) = a • E z) ∧
        (∀ (a : k) (m : normalizationPairDefect H), T (a • m) = a • T m)) := by
  sorry

end RingEquiv
