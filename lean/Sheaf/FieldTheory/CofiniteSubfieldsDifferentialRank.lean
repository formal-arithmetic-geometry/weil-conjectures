/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Finiteness.Basic
import WeilConjectures.FieldTheory.IntersectionSubfieldsSubspace
import WeilConjectures.FieldTheory.FrobeniusBasisCompositum
import WeilConjectures.FieldTheory.PBasisExtension
import WeilConjectures.FieldTheory.PBasisDifferentialsBasis

/-!
# Stabilization of differential ranks over cofinite subfields

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé IV, Proposition 1.2.4,
printed p.49 (blueprint: lem-per-cofinite-subfields-finite-extension-differential-rank).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace FieldTheory

/-- Differential ranks in a finite field extension agree over every cofinite subfield below
some member of a nonempty downward directed family whose intersection is the Frobenius image.

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé IV, Proposition 1.2.4,
printed p.49 (blueprint: lem-per-cofinite-subfields-finite-extension-differential-rank).

Proof:
1. Choose a finite K-basis e of L using lem-weil-pbc-vector-space-free. Its p-th powers
   are independent over K^p: take p-th roots of coefficients in a relation and use
   injectivity of Frobenius in L and independence of e.
2. Apply lem-weil-pbc-intersection-subfields-subspace to the K-linear relation subspace
   of these p-th powers. Its intersection over K^p is zero, so some K_beta has zero
   intersection as well. Thus the p-th powers are independent over every subfield of K_beta.
3. For any cofinite K' below K_beta, put E = K'K^p and F = K'L^p. Derivations kill
   p-th powers and hence these composita. The universal property of
   def-weil-pbc-kahler-differentials gives Omega(K/K') = Omega(K/E) and
   Omega(L/K') = Omega(L/F), up to the canonical differential-preserving isomorphisms.
4. By lem-weil-pbc-frobenius-basis-compositum, the p-th powers of e span F over E.
   Step 2 makes them independent, so [F:E] = [L:K] = n.
5. All degrees are finite. Apply lem-weil-pbc-field-degree-multiplicativity to
   E contained in K contained in L and E contained in F contained in L.
   Cancelling the positive n gives [L:F] = [K:E].
6. Apply lem-weil-pbc-p-independent-extends-to-p-basis to the empty families for K/E
   and L/F. Their p-bases have finite sizes r and s, and the bounded monomial bases
   give [K:E] = p^r and [L:F] = p^s. By lem-weil-pbc-p-basis-differentials-basis,
   the differential dimensions are r and s. As p is prime, p^r = p^s implies r = s.
   Transfer this equality through step 3. The chosen beta works for every such K'. -/
theorem exists_cofinite_subfield_differential_finrank_eq
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [CharP K p]
    (L : Type v) [Field L] [Algebra K L] [Module.Finite K L]
    {I : Type w} [Nonempty I] (F : I → Subfield K)
    (hcofinite : ∀ a : I, Module.Finite (F a) K)
    (hinter : (⋂ a : I, (F a : Set K)) = Set.range (fun x : K ↦ x ^ p))
    (hdirected : ∀ a b : I, ∃ c : I, F c ≤ F a ⊓ F b) :
    ∃ b : I, ∀ K' : Subfield K, K' ≤ F b → Module.Finite K' K →
      Module.finrank L (KaehlerDifferential K' L) =
        Module.finrank K (KaehlerDifferential K' K) := by
  sorry

end FieldTheory
