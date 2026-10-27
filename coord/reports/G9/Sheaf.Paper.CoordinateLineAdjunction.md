## What changed

The statement and all definitions of Sheaf.Paper.CoordinateLineAdjunction are unchanged.
coordinateLineAdjunction now assembles finite-type geometry, coordinate tower identities,
universal coordinate Cartier, the level-th-power annihilation, finite Tate covers and
comparisons, ordinary conjugate counit/transpose equations, the explicit site Hom-chain
calculation, invertibility and exponent compatibility.

CoordinateLineCounitTensor contains the ordinary counit calculation. It derives the open
projection/counit identity from Adjunction.projectionMap_app_app_comp_map_counit, moves
symmetries using derived pullback compatibility, cancels the pullback compositor, applies
proper projection naturality, and uses the normalized projective counit. It proves
invertibility of the specified projection and its precise inverse formula.

Two separate source calculations remain as named public theorems in new modules:
CoordinateLineAugmentationRealization and CoordinateLineConjugateExponents. Their docstrings
and nodes give the argument and the actual maps, including the representative coordinates.
The main proof combines these lemmas with real Lean Hom-equivalence naturality and mates
calculations. Every existing signature, target and source-library declaration is unchanged.
The unclaimed CoordinateLineAdjunctionMaps.projection definition is expanded into its
canonical proper/open components. The two proved source equations specifying this
expansion are recorded in coord/changes/coordinate-line-projection-components.md.
The new formula retains the pullback compositor and both symmetries, with their exact
orientations. This representation repair avoids normalization of the entire
compactification record in the counit calculation. It contains no holes or new choices.
Local reducibility attributes keep the specified compact-support comparison and Brown
adjunction abstract during unification. This reduces the assembly check from over 90
seconds to 38 seconds without changing any construction or exported attribute.

## Proved and sorry left

One original hole closed:
AlgebraicGeometry.ProEtale.CoordinateLine.coordinateLineAdjunction
(lem-pur-coordinate-line-adjunction), proved from the named lower results below.

The new ordinary calculation
AlgebraicGeometry.ProEtale.CoordinateLine.coordinate_line_counit_tensor
(lem-pur-coordinate-line-counit-tensor) has no sorry.

Two holes added, each the complete body of a public theorem in its own module:

- AlgebraicGeometry.ProEtale.CoordinateLine.coordinate_line_augmentation_realization:
  lem-pur-coordinate-line-augmentation-realization.
- AlgebraicGeometry.ProEtale.CoordinateLine.coordinate_line_conjugate_exponents:
  lem-pur-coordinate-line-conjugate-exponents.

This is a decomposition, not a net hole reduction: one original hole closed, two added.
The assigned module and the ordinary counit module contain zero holes. No private theorem,
definition, instance, or partial proof contains sorry. Existing imported theorem holes are
used as the stage-3 contract permits.

## No longer needed

No module is withdrawn. The unit's open/projective coordinate-line route is retained.
The ordinary counit calculation uses lem-etale-proper-projection-formula-finite directly,
rather than the finite-field compact-support comparison theorem. The latter remains a
proof dependency of augmentation realization, where its pro-etale comparison is needed.
The direct proof of universal coordinate Cartier uses the already declared
AffineZeroPurity.coordinate_cartier from AffineSpaceCoordinateBoundaries.

Removed private proof imports from the assigned module:

- Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
- WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
- Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
- Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian

Removed the obsolete top-level tool approval det-pe-finite-tor-comparison-noetherian
from the item node; no tool approvals are added or reordered.

Their general constructions need no separate invocation in the assembly: the canonical
maps already occur in CoordinateLineAdjunctionMaps, while the ordinary tensor/counit
calculation imports its actual proof dependencies privately. In particular
lem-weil-pbc-inverse-image-composition-module-linear and
lem-weil-pbc-ringed-topoi-derived-tensor-pullback are not additional proof obligations
of this assembly. The specified source-coordinate definitions use the existing exact
pullback/tensor maps directly. The general exceptional-adjoint existence and open
adjunction statements are already built into those definitions.

det-pe-finite-tor-comparison-noetherian is not needed to choose representatives:
the statement itself quantifies over every retained ordinary representative.
The bounded-below comparison-unit isomorphism suffices for invertibility.
The remaining original geometry and interface declarations stay available through the
original public imports, all of which are preserved.

The original direct proof dependencies removed from this node are accounted for explicitly:

- def-amb-etale-compact-support, def-pur-affine-line-purity-comparison,
  def-weil-pbc-composite-adjunction and def-weil-pbc-etale-sum-extension: their actual
  constructions are retained in CoordinateLineAdjunctionMaps and the public statement
  imports; the assembly uses the specified maps without a separate existence argument.
- def-weil-finite-type-morphism, def-weil-proper-morphism and
  lemma-nagata-relative-affine-space-open-immersion: the geometry proof uses the existing
  finite-type-over-Noetherian API and the canonical standard projective compactification.
- lem-asd-ordinary-finite-p1-adjunction and lem-pur-etale-open-derived-tensor: retained
  under the new counit-tensor node; they remain needed in its ordinary calculation.
- lem-weil-finite-compact-projection-formula: retained under augmentation realization;
  its site-comparison content remains needed there.
- det-pe-finite-tor-comparison-noetherian: no representative choice is needed because
  the statement already supplies the representative and its comparison isomorphism.
- lem-amb-etale-adjoint-locality and thm-amb-etale-exceptional-adjoint: the fixed Brown
  adjunction and the explicit ordinary adjunction are already supplied by the map
  definitions. No additional adjoint-existence/locality application occurs in this proof.
- lem-weil-pbc-inverse-image-composition-module-linear and
  lem-weil-pbc-ringed-topoi-derived-tensor-pullback: the source-coordinate isomorphisms
  already specify these maps, so neither general auxiliary theorem is applied separately.

These are changes to the direct proof plan, not requests to withdraw the retained
construction modules or source-library declarations.

## Where the brief, the DAG or earlier work was wrong

AffineCoefficientCounitNormalization has overlapping normalization and exponent statements,
but its DAG proof depends on this item. Importing it would hide a mathematical dependency
cycle, so it is not used.

The fixed compact-support comparison is oriented from pro-etale support of comparison
to comparison of ordinary support. Its inverse begins the realization equation used in
the specified Hom chain.

The finite positive-level coefficient convention is zero based. The arithmetic proof uses
(P.level - 1) + 1 = P.level and proves ell^P.level = 0, including ramified E.

The realization calculation can use the generic siteTensorUnitEvaluation declaration.
The earlier finite-ring tensor coherence specialization alone would not cover this
universe, but this generic lemma removes that concern. The remaining task is the
actual source-coordinate and trace square, including comparison of the fixed and
canonical compact-support maps and the supplied realization eK. The new realization
lemma isolates that calculation before any Hom transpose or invertibility assertion.

The exponent proof must also identify the actual root transition, after ordinary Tate
pullback and site comparison, with the coefficientTwistIso composite. An equality of
isomorphism classes alone would not suffice. The retained lemma states that actual-map
compatibility explicitly. Zero coefficients, empty schemes and equal exponents are
included by the naturality/cancellation argument in its proof.

## New nodes

lem-pur-coordinate-line-counit-tensor records the proved actual ordinary tensor-counit
calculation for the standard compactification over every Noetherian base.

lem-pur-coordinate-line-augmentation-realization isolates the integration augmentation
square before transposition. It asserts neither exceptional-map invertibility nor the
geometry, arithmetic, ordinary adjunction or exponent clauses of the original statement.

lem-pur-coordinate-line-conjugate-exponents isolates compatibility of the ordinary
conjugate in realized source coordinates, before boundedSiteRho and the representative
target map. Its source argument is root compatibility of projective traces, projection
naturality and Brown transposition. It is strictly one part of the original conjunction.

The definition representation repair is recorded in
coord/changes/coordinate-line-projection-components.md. The Maps definition node keeps
its statement and Lean attachment, with a proof entry explaining the exact component
expansion. No module held by another group is adapted.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
