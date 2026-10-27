module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import WeilConjectures.Topology.PresheafModuleStalkFunctor

import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.ThickeningAffineScheme
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.ResidueField

/-! # A common affine neighbourhood from an affine source

Source: Stacks Project, Varieties, Tag 09NI, Lemma `varieties-lemma-points-in-affine`
(blueprint: lem-trf-affine-source-stalk-isomorphism-neighbourhood).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Suppose an affine scheme maps to a quasi-separated scheme with finitely many component
generic points, maps its component generic points injectively to component generic points,
and induces isomorphisms on local rings at finitely many selected points. Their images have
a common affine open neighbourhood.

Source: Stacks Project, Varieties, Tag 09NI, Lemma `varieties-lemma-points-in-affine`
(blueprint: lem-trf-affine-source-stalk-isomorphism-neighbourhood).

Proof plan, following the node and Tag 09NI:

1. For no selected points, take the empty affine open. Otherwise pass to the reductions
   (def-weil-pbc-scheme-reduction). Their maps are surjective closed immersions and
   homeomorphisms (lem-weil-pbc-reduction-universal-homeomorphism), so the generic-point
   hypotheses persist. Reduction of an affine is affine. Stalks reduce by quotienting by
   nilpotents, using localization (lem-weil-pbc-affine-open-stalk-localization): if a/s is
   nilpotent, some u kills a power of a, so ua is nilpotent and a/s = ua/(us).
   The selected stalk maps remain isomorphisms. Quasi-separatedness persists by the affine
   cover criterion (lem-weil-pbc-quasi-separated-affine-cover-criterion). An affine open in
   the reduction lifts to an affine open by lem-weil-pbc-thickening-affine-scheme.

2. The affine source is quasi-compact and quasi-separated
   (lem-weil-pbc-affine-scheme-qcqs). A finite subfamily of affine opens of the target
   (lem-weil-pbc-affine-opens-basis) covers its image. Shrink the target to their union.
   This is quasi-compact and quasi-separated by the affine cover criterion. Its generic
   points are the original generic points lying in that open. The generic hypotheses
   and selected local rings persist; the source has finitely many generic points too.

3. Apply lem-trf-qcqs-relative-finite-presentation-approximation. Its affine transitions
   and affine limit give an affine stage by lem-weil-pbc-limit-affine-stage. Write the
   stage as Spec R_i and the source as Spec R, with its projection induced by R_i → R.

4. Let B be the image subring of R_i → R and Y = Spec B (def-weil-affine-spectrum).
   The quotient map R_i → B gives a closed immersion into the chosen stage
   (def-weil-closed-immersion). Thus Y is affine and reduced. The induced g : Y → X is
   finite type: over an affine open of X the finite-presentation stage has finitely many
   affine charts, whose ring maps are finitely presented by
   lem-weil-pbc-lfp-affine-opens-finite-presentation. Their quotient rings remain finitely
   generated (def-weil-finite-type-morphism). The morphism g is separated by
   lem-weil-pbc-affine-source-morphism-separated.

5. Apply lem-trf-reduced-affine-injective-factor-stalk-comparison to B ↪ R. It identifies
   the source and Y generic points bijectively and makes g injective on generic points.
   At every selected point the given local-ring isomorphism factors through the local
   ring of Y, and that comparison makes both factors isomorphisms.

6. Apply lem-trf-finite-type-stalk-isomorphism-open-neighbourhood at each selected point
   of Y. The union U of the resulting neighbourhoods maps locally isomorphically to X.
   Its map is separated by restriction of the closed diagonal (def-weil-proper-morphism).
   Its component generic points lie among those of Y, since Y has finitely many
   components. Generic injectivity therefore persists, and
   lem-trf-separated-local-isomorphism-generic-injectivity makes U → X an open immersion.

7. In the affine Y, write Y ∖ U = V(J). The ideal J lies in none of the finitely many
   selected primes. Prime avoidance (lem-weil-pbc-prime-avoidance) supplies a ∈ J in none
   of those primes. The principal open D(a) lies inside U and contains every selected
   point. It is affine by lem-weil-pbc-affine-open-section-vanishing-prime, clause (b).
   Its image under the open immersion is the desired affine open in X. Undo the target
   shrinking and reduction.
-/
theorem exists_isAffineOpen_of_affine_source_stalkMap_isIso
    {T X : Scheme.{u}} (f : T ⟶ X) [IsAffine T] [QuasiSeparatedSpace X]
    (hfinite : (genericPoints X).Finite)
    (hgeneric : Set.MapsTo f (genericPoints T) (genericPoints X))
    (hinjective : Set.InjOn f (genericPoints T))
    (m : ℕ) (t : Fin m → T) (hstalk : ∀ j : Fin m, IsIso (f.stalkMap (t j))) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ j : Fin m, f (t j) ∈ U := by
  sorry

end AlgebraicGeometry
