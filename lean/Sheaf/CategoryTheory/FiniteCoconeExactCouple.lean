/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.FiniteCoconeLimits
import Sheaf.CategoryTheory.FiniteCoconeWeakMaps

/-!
# Exact couples with finite diagonal cocones

Source: Stacks Project, Homology, Sections 12.20--12.21 and Lemma 12.24.11.
(blueprint: lem-sp-finite-cocone-exact-couple).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple

/-- A diagonal cocone with an isomorphic lower tail and zero upper source tail gives
stationary cycles and the canonical weak convergence comparison.
Source: Stacks Homology Lemma 12.24.11, bounded exact-couple argument;
Sections 12.20--12.21, derived-couple recursion.
(blueprint: lem-sp-finite-cocone-exact-couple).

Proof: On each diagonal the cocone equation implies that alpha is an isomorphism
between sufficiently low indices, since both cocone maps there are isomorphisms.
Sufficiently high D terms are zero. Induct on derivation: the finite cycle object
is the inverse image under the initial f of the incoming alpha image, and the
finite boundary object is the initial g image of the kernel of the outgoing alpha
iterate. The incoming images are eventually zero; the outgoing kernels are
eventually the kernel of the cocone map, because its sufficiently low target map
is an isomorphism. Thus cycles and boundaries are stationary. Their stationary
values are their greatest lower and least upper bounds and give L; stationarity
of cycles gives regularity. Exactness identifies the stationary cycles with the
image of initial g. Therefore D surjects onto their quotient. Its kernel is the
sum of the image of alpha and the kernel of the cocone map. The canonical map to
the graded image of the cocone is also epi: it is the image factorization followed
by a cokernel projection. Pulling the next cocone image back along the current
map gives precisely the same sum, by the cocone equation and the abelian image
and kernel calculus. Hence the two epi maps have equal kernels. This is weak
convergence, with the canonical maps, rather than an arbitrary quotient isomorphism. -/
theorem finiteCocone_weakConvergence
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (A : ∀ n : ℤ, X.AlphaColimit n)
    (hA : ∀ n : ℤ, ∃ a b : ℤ,
      (∀ P : ℤ, P ≤ a → IsIso ((A n).ι P)) ∧
      (∀ P : ℤ, b ≤ P → IsZero (X.D P (n - P)))) :
    ∃ L : X.LimitSubobjects, X.IsRegular ∧ X.WeaklyConvergesTo L A := by
  obtain ⟨L, hreg⟩ := finiteCocone_limits X A hA
  exact ⟨L, hreg, finiteCocone_weakMaps X A hA L hreg⟩

end CategoryTheory.BigradedExactCouple
