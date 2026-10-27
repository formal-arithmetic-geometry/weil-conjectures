## What changed

Replaced the hole in
`WeilConjectures.PointFrobeniusNormalization.point_frobenius_transport_normalization`
with a categorical assembly proof. It localizes the multiplication inverse, proves finite
kappa-lambda cancellation, obtains the integral whole-cone comparison and actual unit,
proves integral cancellation, derives both equations for every given sheaf Weil isomorphism,
and applies the rational and algebraically closed coefficient functors to the integral equation.
The tensor and dual clause is proved directly by coefficient normalization and naturality.

Moved the 26 complete coordinate declarations verbatim to
`Sheaf.Paper.PointFrobeniusNormalizationDefinitions`, publicly reexported by the original module.
A programmatic comparison verifies identical signatures and bodies for all 26. The original
theorem's signature and meaning stay unchanged.

`Sheaf.Paper.PointQuotientComparisonCoordinates` constructs the uniquely normalized tower and
cone isomorphisms as a named data object with a coordinate API. Its proved existence theorem
projects the four coordinate properties from multiplication-cone descent. The inverse-generator
formula determines the entire tower inverse and hence j; both cone coordinates determine eta.hom,
and its inverse is unique. No arbitrary object is chosen from mere existence. The assembly can
use this canonical data without carrying the unrelated rho and descended-theta witnesses through
its proof term. The construction is over a variable point automorphism, calculus and Roos model.
No existing definition body or target statement changes.

The common vocabulary also permits the acyclic proof modules
`Sheaf.Paper.PointFiniteMultiplicationInverse` and `Sheaf.Paper.PointIdentityExchangeRecipe`.
The finite helper is proved from `point_automorphism_finite_transport_inverse`; only the
identity-exchange helper is pending.

The integral quotient clause uses the canonical strict tower and cone comparison data, whose
coordinate API is proved from `isomorphismMultiplicationConeDescent`. The specified generator equation identifies its hom as
a left inverse of the finite comparison. The finite multiplication hom is a right inverse;
uniqueness of inverses identifies these section functions and transfers the scalar formula.
This comparison is sectionwise because the tower components have restricted completed scalar
action, whereas the finite isomorphism is over the finite coefficient ring.
`isomorphismRoosUnitCancellation` gives the whole augmentation equality. Explicit categorical
associativity avoids unfolding concrete chain-map composition. The actual completion unit is
invertible by the complete field of `FrobeniusExchange.models`. The whole-cone normalization
theorem, applied to a coherent evaluation calculus, supplies a two-sided inverse of kappa.
Theta is that inverse followed by the image of the recorded actual unit. Cancelling kappa
proves its normalization directly, without transporting theta between calculi.

## Proved and sorry left

One original hole is closed by decomposition:
`WeilConjectures.PointFrobeniusNormalization.point_frobenius_transport_normalization`
(node `lem-pur-point-frobenius-transport-normalization`). Its body has no sorry.

The new theorems `pointFiniteMultiplicationInverse` and `pointQuotientComparison_exists` are
proved from the existing stated dependencies, with zero sorry in either helper module.

One hole is added, the complete proof of a named public theorem:

- `WeilConjectures.PointFrobeniusNormalization.pointIdentityExchangeRecipe`, node
  `lem-pur-point-identity-exchange-recipe`: identity direct-image exchange and sigma-then-kappa
  recipes, without multiplication inversion, cancellation, equations involving v or tensor/dual.

This is a decomposition, not a complete proof: one hole removed, one added. The final file proves
the nontrivial composition of these parts, including all cancellation and scalar-image equations.
All definitions are complete; no arbitrary object is chosen from a mere existence theorem.
The existing coherent calculus is used as a proof witness only to obtain the two-sided inverse
of the fixed comparison. Theta uses the recorded actual completion unit. The existential multiplication isomorphism is pinned
uniquely by its inverse being the specified chain map.

## No longer needed

Removed the original proof-only imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso` (already used below the existing
  point-automorphism inverse theorem, not needed directly in the assembly proof).
- `Sheaf.Paper.BasicOperationsCoefficientReduction`.
- `Sheaf.Paper.CondensedAmbientExchange`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.
- `Sheaf.Paper.SemilinearDerivedSections`.
- `Sheaf.Paper.PointProEtaleSectionsExactOfUniverses`.

The middle five belong to the pending identity-exchange calculation and remain in that node's
proof dependencies as appropriate; they are not claimed mathematically unnecessary. Exact derived
point sections already have the needed instances in the coordinate vocabulary, so a separate
proof dependency on the point exactness theorem is unnecessary for the assembly.

The original public imports remain publicly available through the coordinate module except
`Sheaf.Paper.PurInverseImageTensorHom`, replaced by
`Sheaf.Paper.PurInverseImageTensorHomDefinitions`. The normalization predicate needs its pure-tensor
section convention, and naturality proves the clause directly. Node
`lem-pur-isomorphism-inverse-image-tensor-hom` is not a dependency of this argument; its full
tensor/Hom, tensor-power, scalar-extension and limit comparison results are not used here.
No source-library declaration or module is removed. No current Lean importer of the original
module exists, but its unfinished DAG parents still need it; it is retained, not withdrawn.
No whole module is claimed pruned from the targets' closure. The proof does not need
Adjunction.unit_leftAdjointUniq_hom_app or the whiskered left-adjoint-uniqueness comparison:
constructing theta from the given kappa inverse and actual unit replaces that transport.

## Where the brief, the DAG or earlier work was wrong

The planned scalar-extension lemma supplies multiplication after scalar extension along an
isomorphism of ring sheaves. It does not itself identify that presentation with the specified
coefficient-sized pullback and inverseImageFiniteComparisonComplex. The existing point_automorphism_finite_transport_inverse supplies that identification.
The new finite helper specializes it and constructs the inverse isomorphism from its two equations.

The identity-square calculation for the selected derived compositors is not a direct consequence
of an arbitrary identity-operation isomorphism. The new exchange statement retains the actual
rightAdjointUniq identity identification and requires the whole-system calculation before limit.
No equality of derived morphisms is inferred from equality of their finite evaluations.

The whole-cone normalization theorem asks for a coherent calculus; the selected models expose
only its underlying calculus. A coherent evaluation calculus suffices to obtain the two-sided
inverse of kappa, which is independent of that calculus. Define theta by that inverse followed
by the image of the recorded actual unit. This avoids the initial planned transport of theta
along left-adjoint uniqueness. The unrestricted legacy completeness predicate quantifies over
a universe-zero auxiliary datum. The proof constructs that datum explicitly from ZMod p and
its algebraic closure for p greater than l, rather than reusing the possibly larger datum D.

The tensor/dual predicate in the existing statement is a sectionwise restriction identity.
It follows from sheafification-unit and slice-morphism naturality; it does not require adding
an isomorphism-of-tensor-products assertion to this already reviewed statement.

## New nodes

`def-pur-point-normalization-coordinates` records the 26 existing canonical coordinate definitions
in their common module. All 26 bodies, including the existing ring and scalar instances, remain
verbatim.

`def-pur-point-quotient-comparison-coordinates` records the canonical strict tower and cone
comparison data, their determining normalization predicate, the proved existence theorem and
the resulting data definition. The inverse-generator and full two-coordinate specification
determine the two isomorphisms uniquely; no arbitrary witness is used as mathematical data.

`lem-pur-point-finite-multiplication-inverse` records point normalization step 1, on arbitrary point automorphisms and arbitrary complexes and without freeness or constructibility. The zero module, rank zero,
rank one and the first positive coefficient exponent pose no exception to the balancing argument.

`lem-pur-point-identity-exchange-recipe` records steps 3--4 before cancellation. Its finite assertion
is on arbitrary derived objects for the exchange and arbitrary complexes for the recipe; its
integral assertion uses the original constructible complete domain. It keeps whole-system maps
and the exact chosen identity-direct-image comparisons.

Change record: `coord/changes/G7-point-normalization-coordinate-module.md`.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
