## What changed

Filled six of the seven existing theorem holes in
`Sheaf.Paper.ProjectionPurityAgreement`. No public signature, definition body,
public import, target statement, or DAG statement changed.

`projection_smooth` follows the coordinate tower by induction, using smoothness
of the affine line and addition of relative dimensions. The two coordinate
existence-and-uniqueness theorems split rank into zero and successor, identify
the literal endpoints, and use the recorded heterogeneous equalities for uniqueness.

`projectionTarget_isIso` uses the identity map at positive rank. At rank zero,
the ordinary exceptional identity isomorphism and the comparison-adjunction
counit are invertible. A private categorical proof deduces the latter from the
bounded comparison unit and the triangle identity, then transports it across eK.

A private presentation lemma obtains an ordinary bounded constructible origin
from `finiteRing_constructibleDerived_origin`, reflects the same Tor interval,
and transports its comparison to the fixed intrinsic inverse image of K.
`projectionAffineIntrinsic_existsUnique` constructs the intrinsic map using that
presentation. The ordered-integration-transpose theorem and its fixed raw-map
characterization prove independence of the representative.
`projectionSmoothIntrinsic_existsUnique` uses the literal recorded smooth map
and its heterogeneous-equality normalization.

Added proof imports for the constructible comparison interface, finite-ring
constructible origin, and ordered integration transposes. Removed unused proof
imports listed below. Existing remaining theorem documentation and its DAG plan
are preserved.

## Proved and sorry left

Closed six original holes, all in namespace
`WeilConjectures.PurityFiniteSetting`:

- `projection_smooth`
- `projectionSourceIso_existsUnique`
- `projectionTargetMap_existsUnique`
- `projectionTarget_isIso`
- `projectionAffineIntrinsic_existsUnique`
- `projectionSmoothIntrinsic_existsUnique`

One original hole remains: `projection_purity_agreement`, node
`lem-pur-projection-purity-agreement`. Its proof is exactly `by sorry` with its
original sourced proof documentation. No holes were added or split off.

The remaining calculation identifies the actual smooth tensor-counit map with
the actual ordered integration transpose through the specified tensor coordinates
and adjacent annihilator transition. Attempts at this calculation are not included
as partial proofs or new assumed statements.

## No longer needed

The following proof imports are unused by the six completed proofs and have been
removed from this module:

- `Sheaf.Paper.VectorIntegrationSiteComparison`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension`
- `Sheaf.Paper.AffineTranslationTrace`
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`
- `Sheaf.Paper.TraceTransposeBaseChange`
- `Sheaf.Paper.PurityDncComparisons`
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`
- `Sheaf.Paper.TensorTraceTranspose`
- `Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle`
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`
- `Sheaf.SixFunctors.CompositionProjectionMate`
- `Sheaf.Paper.FiniteProjectionActionLaws`
- `Sheaf.Paper.PullbackTorAmplitude`
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction`
- `Sheaf.Paper.CompositeIntegrationCounit`

No mathematical node or module is claimed withdrawn: the main agreement theorem
remains open, so its planned dependencies and the unit route remain applicable.
The DAG proof and proof_deps are therefore unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned assembly uses several different literal coordinate presentations:
`affineTraceTower` versus `iteratedAffineLine`, the ordinary coefficient unit
versus the monoidal unit, and killing exponents ell^(n+1) versus ell^(n+2).
The existing prerequisite conclusions do not make all connecting maps
definitionally equal. Explicit source, tensor, trace-transition and transpose
compatibilities are still required for the seventh theorem. No statement is
marked disputed, and no weakening or replacement of that theorem is delivered.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
