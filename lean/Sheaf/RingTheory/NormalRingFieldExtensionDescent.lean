/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Flat

/-!
# Descent of normality under scalar field extension

Source: Stacks Project, Algebra, Tag 033G (lemma-descent-normal), specialized to scalar
field extension (blueprint: lem-weil-pbc-normal-ring-field-extension-descent).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- Normality of a commutative algebra descends along an arbitrary scalar field extension.
Normality means that every prime localization is an integrally closed domain.

Source: Stacks Project, Algebra, Tag 033G (lemma-descent-normal).
(blueprint: lem-weil-pbc-normal-ring-field-extension-descent).

Proof:
1. Set S = B ⊗[F] E. The map i : B → S, b ↦ b ⊗ 1, is faithfully flat by
   lem-weil-pbc-field-extension-base-change-faithfully-flat, hence flat by
   def-weil-pbc-faithfully-flat-ring-map. For any prime p of B, lift p to a prime q of S
   by lem-weil-pbc-faithfully-flat-surjective-spectrum.
2. Put A = B_p and C = S_q. By lem-weil-pbc-flat-local-ring-maps the induced map
   j : A → C is flat and local, so lem-weil-pbc-flat-local-hom-faithfully-flat makes it
   faithfully flat. Normality of S says that C is an integrally closed domain.
3. Apply lem-weil-pbc-faithfully-flat-ideal-contraction to the zero ideal to see that
   j is injective. Since C is a domain, injectivity shows that A is a domain too.
4. An element x = a/b of Frac(A) integral over A maps to j(a)/j(b) in Frac(C).
   Injectivity preserves nonzero denominators and gives an injective fraction-field map.
   Mapping the monic equation shows that this image is integral over C. As C is
   integrally closed, it equals s/1 for some s in C, and j(a) = j(b)s.
5. Thus j(a) belongs to the extension of the principal ideal bA. By
   lem-weil-pbc-faithfully-flat-ideal-contraction, a belongs to bA, so a = br for some
   r in A and x = r/1 in Frac(A).
6. Hence A is integrally closed. Since p was arbitrary, def-weil-pbc-normal-ring says
   that B is normal. For B = 0 there are no primes and the conclusion is vacuous. -/
theorem normal_ring_of_normal_tensor_field
    (F : Type u) (E : Type v) (B : Type w)
    [Field F] [Field E] [Algebra F E] [CommRing B] [Algebra F B]
    (h : ∀ (q : Ideal (B ⊗[F] E)) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) :
    ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  sorry

end Algebra
