/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.RingTheory.FiniteProjectiveComplexFreeModel
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import WeilConjectures.Algebra.Homology.RingPseudoCoherentSummand
import Sheaf.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
import Mathlib.RingTheory.Flat.Basic

/-!
# Direct summands of perfect complexes over a ring

Source: Stacks Project, More on Algebra, Tag 066S, `lemma-summands-perfect`
(blueprint: lem-sf-perfect-ring-summand).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- If the binary direct sum of two objects of `D(A)` is perfect, both objects are perfect.
Source: Stacks Project, More on Algebra, Tag 066S, `lemma-summands-perfect`
(blueprint: lem-sf-perfect-ring-summand).

Proof:
1. Put S = K ⊞ L. By def-pc-perfect-ring-complex choose a bounded finite projective
   model P, zero outside an interval [a, b], with Q(P) isomorphic to S.
   By lem-pc-finite-projective-complex-free-model replace P by a bounded-above
   finite-free complex quasi-isomorphic to it. Thus S is pseudo-coherent in the
   sense of def-pc-ring-pseudo-coherent-complex.
2. Choose complex representatives of K and L. Their termwise direct sum represents S.
   Apply the final clause of lem-pc-ring-pseudo-coherent-summand (Tag 064X) to obtain
   bounded-above finite-free models of K and L, hence pseudo-coherence of both.
3. Every term of P is flat by lem-weil-pbc-projective-module-flat.
   By lem-pc-module-bounded-flat-kflat its bounded-above complex is K-flat.
4. For every A-module M in degree zero, use the K-flat computation clause of
   lem-pc-derived-tensor-second-factor-functor for A → A to compute S ⊗ᴸ M by P ⊗ M.
   This tensor complex vanishes outside [a, b], so the same interval bounds its
   cohomology for every M. Thus S has finite Tor amplitude in [a, b].
5. For T = K and T = L, the biproduct inclusion i : T → S and projection p : S → T
   satisfy i ≫ p = 1. Apply the tensor functor of
   lem-pc-derived-tensor-second-factor-functor and then each cohomology functor of
   def-weil-abstract-derived-category. Outside [a, b] the resulting identity of
   H^j(T ⊗ᴸ M) factors through the zero module H^j(S ⊗ᴸ M), hence is zero.
   Thus both summands have Tor amplitude in [a, b], the retract argument of Tag 066G.
6. Apply lem-pc-ring-pseudo-coherent-finite-tor-perfect to each summand, using step 2
   for pseudo-coherence and step 5 for finite Tor dimension. Its bounded finite
   projective models give exactly def-pc-perfect-ring-complex for K and for L.
No Noetherian hypothesis is used. -/
theorem isPerfectRingComplex_summand {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (K L : DerivedCategory (ModuleCat.{u} A)) (h : IsPerfectRingComplex (K ⊞ L)) :
    IsPerfectRingComplex K ∧ IsPerfectRingComplex L := by
  sorry

end DerivedCategory
