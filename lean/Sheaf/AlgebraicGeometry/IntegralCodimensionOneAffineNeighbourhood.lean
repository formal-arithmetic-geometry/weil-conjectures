module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme

import Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Sheaf.RingTheory.OneDimensionalSubringsCommonDvr
import Sheaf.AlgebraicGeometry.SemilocalSubringAffineGluing
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.AffineSourceStalkIsomorphismNeighbourhood

/-!
# A common affine neighbourhood of codimension-at-most-one points

Source: Stacks Project, Varieties, Tag 09NJ,
Lemma `varieties-lemma-finite-set-codim-1-points-in-affine`.
(blueprint: lem-trf-integral-codimension-one-affine-neighbourhood).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- A finite set of points of an integral separated scheme has a common affine open
neighbourhood if its local rings are Noetherian and have Krull dimension at most one.

Source: Stacks Project, Varieties, Tag 09NJ,
Lemma `varieties-lemma-finite-set-codim-1-points-in-affine`.
(blueprint: lem-trf-integral-codimension-one-affine-neighbourhood).

Proof plan:
1. By lem-sc-integral-scheme-stalks-in-function-field, embed every selected local
   ring in the function field K with fraction field K. A dimension-zero local domain
   is a field; lem-weil-pbc-spec-local-ring-canonical-morphism then identifies its
   point with the generic point. Remove that point and enumerate the remaining
   distinct points. If none remain, an affine neighbourhood of any point, supplied
   by lem-weil-pbc-affine-opens-basis, contains the generic point and suffices.
2. No DVR in K contains two of the remaining local rings. Its maximal ideal
   contracts in each one-dimensional local domain to either zero or the maximal
   ideal. Zero contraction would force the DVR to contain the fraction field K,
   making it a field, a contradiction. Both inclusions are therefore local.
   Their spectrum maps to X agree generically, so
   lemma-nagata-separated-valuation-lift-unique makes them equal, contradicting
   the distinct images of their closed point.
3. Apply lem-trf-one-dimensional-subrings-common-dvr-criterion. The Noetherian
   dimension-one hypotheses hold, and step 2 excludes the common-DVR alternative.
   Thus the tensor multiplication maps for distinct local rings are surjective.
4. Apply lem-trf-semilocal-subring-affine-gluing to this nonempty finite family.
   It produces an affine spectrum S covered by the spectra of these local rings,
   with their closed points distinct and the pairwise overlaps equal to Spec K.
5. The canonical maps of lem-weil-pbc-spec-local-ring-canonical-morphism agree
   on Spec K. Glue them by lem-weil-pbc-scheme-morphism-gluing to obtain S → X.
   Each selected closed point maps to its prescribed point and has an isomorphic
   stalk map. The generic-point sets on both sides are singletons and the map
   identifies them.
6. By lem-pc-separated-quasi-separated the target is quasi-separated. Apply
   lem-trf-affine-source-stalk-isomorphism-neighbourhood to obtain an affine open
   containing all remaining points. When there are remaining points it is nonempty,
   so it also contains the removed generic point. This gives the required inclusion.
-/
theorem exists_isAffineOpen_superset_of_isIntegral_of_stalk_dimension_le_one
    (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]
    (T : Set X) (hT : T.Finite)
    (hnoetherian : ∀ x ∈ T, IsNoetherianRing (X.presheaf.stalk x))
    (hdimension : ∀ x ∈ T, ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    ∃ V : X.Opens, IsAffineOpen V ∧ T ⊆ (V : Set X) := by
  sorry

end AlgebraicGeometry
