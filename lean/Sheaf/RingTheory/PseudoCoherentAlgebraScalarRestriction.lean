module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Module.ULift
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.RingTheory.FiniteHomologyOfMPseudoCoherent
import WeilConjectures.RingTheory.FiniteConeFreeModel

/-!
# Restriction through a pseudo-coherent algebra

Source: Stacks Project, More on Algebra, Tag 064Z,
lemma-finite-push-pseudo-coherent, final assertion
(blueprint: lem-sfb-pseudocoherent-algebra-scalar-restriction).
-/

@[expose] public section

set_option autoImplicit false

universe uS uT v wS wT

open CategoryTheory

namespace DerivedCategory

/-- Restriction of scalars preserves and reflects pseudo-coherence when the target ring
is pseudo-coherent over the source. The `ULift` places the regular target module in the
common module universe; it changes neither its module structure nor its isomorphism class.
The functor `mapDerivedCategory` is induced by termwise ordinary restriction, retaining
additive groups and differentials and acting by `s • x = f s • x`.

Source: Stacks Project, More on Algebra, Tag 064Z,
lemma-finite-push-pseudo-coherent, final assertion
(blueprint: lem-sfb-pseudocoherent-algebra-scalar-restriction).

Proof, following the accepted split:
1. Restriction keeps kernels, images, quotient additive groups and cohomology. It preserves
   quasi-isomorphisms and mapping cones, hence cone triangles. A bounded-above finite-free
   source-ring model P of T[0] gives P raised to any finite direct-sum power as a model of
   the corresponding finite-free T-module restricted to S, including rank zero.
2. For pseudo-coherent K over T, choose a bounded-above finite-free T-complex E representing
   it. Every restricted term is pseudo-coherent by step 1. Apply
   lem-sfb-pseudocoherent-terms-bounded-above (Tag 064Y) over S. Restriction preserves the
   quasi-isomorphism, so its conclusion is pseudo-coherence of restricted K.
3. Conversely, represent K by C. A finite-free S-model of its restriction supplies an upper
   cohomology bound b for C. For any bounded finite-free T-complex F, map F to C, and n with
   its cone acyclic above n, step 1 and Tag 064Y make restricted F pseudo-coherent.
4. Apply lem-pc-ring-pseudo-coherent-iff-all-m to restricted F and C. For every m, the first
   clause of lem-pc-ring-pseudo-coherent-distinguished-triangle gives m-pseudo-coherence of
   the restricted cone. The all-m equivalence makes this cone pseudo-coherent.
5. Its n-pseudo-coherence and vanishing above n imply finite S-module cohomology in degree n
   by lem-sc-finite-cohomology. The same generators generate over T, by sending each source
   coefficient through f. Thus the top cone cohomology is finite over T.
6. Apply lem-pc-ring-finite-cone-free-model to C, b, and the arbitrary cone tests of steps
   3-5, in the common universe containing the rings and modules. It gives a finite-free
   T-model zero above b and a quasi-isomorphism to C, proving pseudo-coherence over T.
   Together with step 2 this proves the equivalence. -/
theorem isPseudoCoherent_restrictScalars_iff_of_algebra
    {S : Type uS} {T : Type uT} [CommRing S] [CommRing T] (f : S →+* T)
    [HasDerivedCategory.{wS} (ModuleCat.{max uS uT v} S)]
    [HasDerivedCategory.{wT} (ModuleCat.{max uS uT v} T)]
    (hT : IsPseudoCoherent
      ((singleFunctor (ModuleCat.{max uS uT v} S) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of T (ULift.{max uS v} T)))))
    (K : DerivedCategory (ModuleCat.{max uS uT v} T)) :
    IsPseudoCoherent K ↔
      IsPseudoCoherent ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K) := by
  sorry

end DerivedCategory
