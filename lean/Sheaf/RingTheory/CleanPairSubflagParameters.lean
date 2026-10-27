module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters

import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.LocalRing.Module

/-!
# Simultaneous parameters for a clean pair and a regular subflag

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, VIII Lemma 4.2.6,
printed p.120, with the regular subflag extension used in Proposition 4.2.8(iii),
printed p.121 (blueprint: lem-per-clean-pair-subflag-parameters).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace IsLocalRing

/-- A clean pair of ideals and a larger ideal with regular quotient admit one regular
system of parameters adapted to all three ideals. Indices start at zero, so the first
`l` parameters have indices `i` with `i.val < l`.
Source: ILO, VIII Lemma 4.2.6, printed p.120, and Proposition 4.2.8(iii), printed p.121
(blueprint: lem-per-clean-pair-subflag-parameters).

Proof:
1. Put S = P + Q, k = R/m, V = m/m², and U_L = (L + m²)/m² for L = P,Q,S,K.
   The cotangent dimension is d = dim R by lem-weil-pbc-regular-local-cotangent-dimension.
   By lem-weil-pbc-regular-local-quotient-independent-generators, each L has generators
   with independent cotangent classes. Expanding an element of L intersect m² in these
   generators shows that all coefficients lie in m. Thus L intersect m² = mL and
   L/mL maps isomorphically onto U_L.
2. For a class in U_P intersect U_Q choose representatives p in P and q in Q.
   Write p - q = a + b with a in mP and b in mQ, using S intersect m² = mS.
   Then c = p - a = q + b lies in P intersect Q and represents the same class.
3. Choose a basis C of U_P intersect U_Q and common lifts as in step 2. Extend C
   to bases C union X of U_P and C union Y of U_Q, using
   lem-weil-pbc-vector-space-basis-through-vector. Lift X in P and Y in Q.
   C union X union Y is a basis of U_S: a relation first puts its X-part in
   U_P intersect U_Q, killing the X coefficients, and then all remaining coefficients.
4. Extend this basis first through U_K, adding Z, and then through V, adding T,
   by the same basis-extension lemma. Lift Z in K and T in m, retaining the common
   lifts already chosen. Enumerate the finite basis in the order C,X,Y,Z,T and let
   l be the length of the first four blocks.
5. The chosen lifts span P/mP, Q/mQ, K/mK and m/m² in their respective blocks.
   Apply lem-weil-pbc-nakayama-local-generators to these four finite modules to obtain
   P = (C,X), Q = (C,Y), K = (C,X,Y,Z), and m = (C,X,Y,Z,T).
6. The full list has length d and generates m, so it is a regular system of parameters
   by def-weil-pbc-regular-system-of-parameters. Let A index C,X and B index C,Y.
   Both subsets lie below l and give the required ideal equalities. Empty blocks allow
   zero ideals, P = Q, K = P + Q, and d = 0 throughout.
-/
theorem exists_cleanPair_subflag_parameters
    {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (P Q K : Ideal R) (hP : P ≠ ⊤) (hQ : Q ≠ ⊤) (hK : K ≠ ⊤)
    (hPQK : P ⊔ Q ≤ K)
    (hPreg : IsRegularLocalRing (R ⧸ P))
    (hQreg : IsRegularLocalRing (R ⧸ Q))
    (hPQreg : IsRegularLocalRing (R ⧸ (P ⊔ Q)))
    (hKreg : IsRegularLocalRing (R ⧸ K)) :
    ∃ (d : ℕ) (t : Fin d → R), IsRegularSystemOfParameters (List.ofFn t) ∧
      ∃ l : ℕ, l ≤ d ∧ ∃ A B : Set (Fin d),
        A ⊆ {i | i.val < l} ∧ B ⊆ {i | i.val < l} ∧
        K = Ideal.span (t '' {i | i.val < l}) ∧
        P = Ideal.span (t '' A) ∧ Q = Ideal.span (t '' B) := by
  sorry

end IsLocalRing
