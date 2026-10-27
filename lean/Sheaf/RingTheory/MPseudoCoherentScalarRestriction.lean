module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import WeilConjectures.RingTheory.MPseudoCoherent
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.RingTheory.FiniteHomologyOfMPseudoCoherent

/-!
# Fixed-degree pseudo-coherence and restriction of scalars

Source: Stacks Project, More on Algebra, Tag 064Z, lemma-finite-push-pseudo-coherent,
equivalence (1) and (2) for a fixed integer
(blueprint: lem-sfb-m-pseudocoherent-algebra-scalar-restriction).
-/

@[expose] public section

set_option autoImplicit false

universe uS uT v wS wT

open CategoryTheory

namespace DerivedCategory

/-- Restriction through an algebra pseudo-coherent over the base preserves and reflects
`m`-pseudo-coherence for every integer `m`. The regular module is lifted only to place it
in the same module universe as `K`. The functor is the derived functor of exact ordinary
restriction: it retains additive groups and differentials and acts by `s • x = f(s) • x`.

Source: Stacks Project, More on Algebra, Tag 064Z, lemma-finite-push-pseudo-coherent,
equivalence (1) and (2) for a fixed integer
(blueprint: lem-sfb-m-pseudocoherent-algebra-scalar-restriction).

Proof:
1. Ordinary restriction keeps kernels and images, so cohomology is restricted cohomology.
   It preserves quasi-isomorphisms, shifts, cones and distinguished triangles. Finite
   direct sums of a bounded-above finite-free base-ring model of `T[0]` model restricted
   finite-free `T`-modules, including rank zero.
2. For a bounded finite-free `T`-complex `E`, its restricted terms are pseudo-coherent.
   Apply lem-sfb-pseudocoherent-terms-bounded-above and then
   lem-pc-ring-pseudo-coherent-iff-all-m to make its restriction `q`-pseudo-coherent for
   every `q`. Over `T`, the identity of `E` is itself a witness.
3. Given an `m`-approximation `E → K`, the cone has zero cohomology in degrees at least
   `m`, by lem-sf-derived-homology-long-exact. Restriction retains that vanishing, and
   the zero complex witnesses `m`-pseudo-coherence of the restricted cone. Step 2 and
   the middle-vertex clause of lem-pc-ring-pseudo-coherent-distinguished-triangle yield
   `m`-pseudo-coherence of the restriction of `K`.
4. Conversely, an `m`-approximation over the base gives an upper cohomological bound for
   `K`. Induct uniformly on `n-m+1`, where `n ≥ m-1` bounds its cohomology above. For
   `n = m-1`, the zero complex is a witness; this includes the acyclic case.
5. If `n ≥ m`, the restricted object is also `n`-pseudo-coherent. Apply
   lem-sc-finite-cohomology at `n`. Finite base-ring generators of its top cohomology
   also generate over `T`. Lift them to cycles in a representative and map the finite
   free `T`-module in degree `n` to these cycles, obtaining a map `E → K` surjective
   on degree-`n` cohomology.
6. The long exact sequence of the cone triangle shows that this cone has cohomology
   bounded above by `n-1`; restriction retains the same cone and vanishing.
7. By Step 2, the restriction of `E` is `(m+1)`-pseudo-coherent. The first-vertex-to-cone
   clause of lem-pc-ring-pseudo-coherent-distinguished-triangle makes the restricted
   cone `m`-pseudo-coherent. Induction makes the cone `m`-pseudo-coherent over `T`.
   Since `E` is `m`-pseudo-coherent over `T`, the middle-vertex clause gives the result.
-/
theorem isMPseudoCoherent_restrictScalars_iff
    {S : Type uS} {T : Type uT} [CommRing S] [CommRing T] (f : S →+* T)
    [HasDerivedCategory.{wS} (ModuleCat.{max uS uT v} S)]
    [HasDerivedCategory.{wT} (ModuleCat.{max uS uT v} T)]
    (hT : IsPseudoCoherent
      ((singleFunctor (ModuleCat.{max uS uT v} S) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of T (ULift.{max uS v} T)))))
    (m : ℤ) (K : DerivedCategory (ModuleCat.{max uS uT v} T)) :
    IsMPseudoCoherent m K ↔
      IsMPseudoCoherent m ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K) := by
  sorry

end DerivedCategory
