/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Conormal basis of a relative global complete intersection

Source: Stacks Project, Algebra, Lemma 00SV (3)
(blueprint: lem-weil-pbc-relative-global-complete-intersection-conormal-free).
-/

@[expose] public section

universe v

namespace Algebra

/-- The equation classes form a basis of the conormal module of the specified relative global
complete intersection; hence it is free and isomorphic to the finite direct sum of `c`
copies of the quotient ring. Source: Stacks Project, Algebra, Lemma 00SV (3)
(blueprint: lem-weil-pbc-relative-global-complete-intersection-conormal-free).

Proof:
1. Write `I = (f)` and `S = P/I`. The classes `e_j` define the map `S^c → I/I²`;
   being a basis means that this map is bijective (def-weil-pbc-free-module).
2. At a prime `q` of `S`, let `q'` be its inverse image in `P` and `J = I P_q'`.
   Localization at a prime of a quotient identifies `S_q` with `P_q'/J`
   (lem-weil-pbc-localization-at-prime-of-quotient). Exactness of localization identifies
   `(I/I²)_q` with `J/J²`, carrying each `e_j/1` to the class of `f_j/1`
   (lem-weil-pbc-localization-module-exact).
3. The localized equations form a regular sequence by 00SV (1)
   (lem-weil-pbc-relative-global-complete-intersection-local-regular-sequence).
   Regular sequences give a conormal basis by 00LN
   (lem-weil-pbc-regular-sequence-conormal-free).
4. Localization commutes with finite direct sums, so the localized map is the basis map
   with these localized equation classes, and is bijective.
5. Bijectivity at every maximal localization gives global bijectivity
   (lem-weil-pbc-linear-map-bijective-at-maximal-localizations), hence the asserted basis,
   freeness and isomorphism. If `S = 0`, both modules are zero. -/
theorem relativeGlobalCompleteIntersection_conormal_free
    {R : Type v} [CommRing R] {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation f) :
    (∃ b : Module.Basis (Fin c)
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent,
      ∀ j : Fin c, b j = (Ideal.span (Set.range f)).toCotangent
        ⟨f j, Ideal.subset_span (Set.mem_range_self j)⟩) ∧
    Module.Free (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))
      (Ideal.span (Set.range f)).Cotangent ∧
    Nonempty ((Ideal.span (Set.range f)).Cotangent ≃ₗ[
      MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)]
      (Fin c → (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) := by
  sorry

end Algebra
