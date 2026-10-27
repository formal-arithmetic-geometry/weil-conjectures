module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.RelativeAssassin
import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.RelativeAssassinBaseChange
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Containment of fibre associated points in an open after base change

Source: Stacks Project, More on Morphisms, Tag 05KQ,
`lemma-base-change-assassin-in-U`
(blueprint: lem-sfb-fibre-assassin-containment-base-change).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Containment of the associated points of a fibre in an open subscheme is equivalent
before and after arbitrary base change. The point downstairs is `h s'`. The inverse
images on the two sides are precisely the point sets of `U_s` and `U'_{s'}`.

Source: Stacks Project, More on Morphisms, Tag 05KQ,
`lemma-base-change-assassin-in-U`
(blueprint: lem-sfb-fibre-assassin-containment-base-change).

Proof plan, following the four steps of the node:

1. By [def-pc-scheme-fibre], the fibre projections identify fibre points with points
of the total spaces above the specified base points. Restrict the base-change projection
to obtain a map from the upstairs fibre to the downstairs fibre. The square of fibre
projections commutes. By [def-trf-relative-assassin], association on each fibre is relative
association of its image. Since the upstairs open is the inverse image of `U`, membership
in its fibre is equivalent to membership of the image in the downstairs open fibre.

2. Suppose the downstairs associated points lie in the open fibre. The forward implication
of [lem-trf-relative-assassin-base-change] sends every upstairs relative associated point to
a downstairs relative associated point. Step 1 therefore puts every upstairs associated
point in the upstairs open fibre. Local finite type and quasi-coherence are exactly the
hypotheses required by that base-change theorem; no condition on `h` is used.

3. For a downstairs associated point `z`, the residual fibre is the spectrum of
`κ(s') ⊗[κ(s)] κ(z)`, by [lem-trf-relative-assassin-base-change]. This ring is nonzero by
[lem-weil-common-extension-fields-tensor-nontrivial]. Choose a minimal prime over zero
using [lem-weil-pbc-minimal-prime-over-proper-ideal]. By
[lem-weil-pbc-spec-irreducible-components-minimal-primes], its zero locus is an irreducible
component. The closure of that prime point is its zero locus, so it gives a residual-fibre
generic point above `z`. This does not require Noetherianity of the residual tensor ring.

4. Suppose the upstairs associated points lie in the upstairs open fibre. Given a downstairs
associated point, choose the residual generic lift from step 3. The reverse implication
of [lem-trf-relative-assassin-base-change] makes this lift upstairs associated. It lies
in the upstairs open fibre by assumption. Step 1 then puts its image, the original
point, in the downstairs open fibre. This proves the reverse containment, including
empty fibres and empty associated-point sets. -/
theorem associatedPoints_fiber_subset_open_iff_baseChange {X S S' : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (F : X.Modules)
    (hF : F.IsQuasiCoherentFiniteType) (U : X.Opens) (h : S' ⟶ S) (s' : S') :
    associatedPoints ((tensorPullback (f.fiberι (h s'))).obj F) ⊆
        (f.fiberι (h s')) ⁻¹' (U : Set X) ↔
      associatedPoints
          ((tensorPullback ((pullback.snd f h).fiberι s')).obj
            ((tensorPullback (pullback.fst f h)).obj F)) ⊆
        ((pullback.snd f h).fiberι s') ⁻¹'
          ((pullback.fst f h) ⁻¹' (U : Set X)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
