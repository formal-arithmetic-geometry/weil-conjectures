module

public import Sheaf.AlgebraicGeometry.RelativeCoefficientWindowApproximation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.AffinePushforwardResolutionQuasiIso
import WeilConjectures.AlgebraicGeometry.AffinePseudoCoherentCriterion
import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.AlgebraicGeometry.AffineDerivedPushforwardTExact
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.AlgebraicGeometry.AffineFiniteTypeGeneratingSections
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.ConePseudoCoherent
import WeilConjectures.RingTheory.FiniteHomologyOfMPseudoCoherent
import Mathlib.RingTheory.FiniteType

/-! # Two-open locality of finite-window coefficient approximation

Source: agent-formulated two-open prerequisite for the unnumbered Kiehl assertion after
Stacks Project, perfect.tex, Tag 0CSD. This assertion is not stated by that tag.
The primary Kiehl descente source is WANTED.
(blueprint: lem-sfb-relative-coefficient-window-two-open-locality).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Approximation on two quasi-compact opens and their intersection implies approximation
on their union, uniformly in the initially supplied finite coefficient stage.
Source: agent-formulated prerequisite after Stacks 0CSD; primary Kiehl source WANTED
(blueprint: lem-sfb-relative-coefficient-window-two-open-locality).

Proof (the node's seven steps):
1. Choose finite affine charts R_j over B and polynomial surjections over D.
Relative pseudo-coherence on these charts gives absolute pseudo-coherence over A[x].
D is Noetherian since it is finite type over B.
2. Finite free representatives give a common upper bound b. On the empty scheme
use F=0 over D. Otherwise start at N=b+1 with F=0; affine direct image is t-exact.
3. At each coefficient stage E, coherent cohomology is finite on the Noetherian
charts. The Noetherian criterion supplies bounded-above finite-free polynomial models.
4. Their terms are also E-free, hence K-flat over E. Derived affine tensor and
pushforward comparisons identify theta with the extension/restriction counit, without
flatness. Both transposes multiply the given A-scalar and apply gamma.
5. The cone is pseudo-coherent over each A-polynomial chart. Vanishing in degrees
at least N and top-cohomology finiteness make H^(N-1) finite on that chart.
6. Apply lem-sfb-sheaf-single-degree-coefficient-cancellation at n=N-1. Separated
finite type is preserved by base change. The refinement is finite type over D by
transitivity, and the new invariant holds at N-1.
7. Iterate b+1-a times if a <= b+1; otherwise retain the zero model. This proves
P(W) for every quasi-compact W, hence the stated conditional implication. No overlap
isomorphism for independently chosen models is asserted. -/
theorem relativeCoefficientWindow_twoOpenLocality {B A : CommRingCat.{u}}
    [IsNoetherianRing B] (b : B ⟶ A) {Y : Scheme.{u}} (f : Y ⟶ Spec B)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (U V : Y.Opens) (hU : IsCompact (U : Set Y)) (hV : IsCompact (V : Set Y))
    (hPU : HasRelativeCoefficientWindowApproximation (U.ι ≫ f) b)
    (hPV : HasRelativeCoefficientWindowApproximation (V.ι ≫ f) b)
    (hPUV : HasRelativeCoefficientWindowApproximation ((U ⊓ V).ι ≫ f) b) :
    HasRelativeCoefficientWindowApproximation ((U ⊔ V).ι ≫ f) b := by
  sorry

end AlgebraicGeometry
