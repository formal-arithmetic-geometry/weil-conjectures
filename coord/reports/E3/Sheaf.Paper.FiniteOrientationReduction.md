## What changed

`AlgebraicGeometry.ProEtale.SpFiniteOrientation.unit_tower_reduction` now follows from the
actual `SpTowerGluing.Levels.reduction` equation. The proof transports normalization
along the supplied identification of whole towers, using the realization unit and
naturality of the canonical reduction. It then postcomposes the exceptional
reduction equation with the finite right adjoint of the inverse input reduction.
Functoriality and the hom-inverse identity give exactly the displayed equation.
The unit-reduction statement, coefficient mate and evaluation comparisons are unchanged.
Private generic categorical lemmas supply naturality, functoriality and cancellation.
All previously proved theorems retain their original proofs.

Added the private proof import `Sheaf.Paper.CoefficientUnitTowerNormalized`. Its one
public theorem isolates normalization of the inverse-realized strict coefficient
unit, without any exceptional functor, adjunction, smoothness or finite-type
hypotheses. Its docstring and node give the free rank-one/K-flat computation of the
actual quotient transitions. Updated the item's node to record this decomposition.

All existing statement text, visibility and definition bodies are preserved.
Added `towerCoefficientCommRing`, a direct cache of the ordinary commutative-ring
structure on the lifted ell-power quotient, and registered it only locally.
The inferred dictionaries are definitionally equal to the original ones. Profiling
identified the two existing uniformizer signatures as expensive for Lean's exported
premise indices; this cache reduces their combined indexing pass from approximately
22 seconds to 4 seconds. No proof check or compile limit is disabled. The change
record is `coord/changes/finite-orientation-coefficient-ring-cache.md`.
Server compilation with exported artifacts passed for both delivered Lean modules.
Development diagnostics have been removed. Static checks confirm the twelve original
public signatures, line lengths and the DAG proof-dependency unions.

## Proved and sorry left

One of the four original holes is closed in Lean:
`AlgebraicGeometry.ProEtale.SpFiniteOrientation.unit_tower_reduction`.
This is a decomposition, not a net proof: one lower hole is added,
`AlgebraicGeometry.ProEtale.SpFiniteOrientation.coefficient_unit_tower_normalized`
(node `lem-sp-coefficient-unit-tower-normalized`). The lower statement is just the
input normalization step; it contains no exceptional-output reduction equation.
The combining argument uses naturality and the existing `Levels.reduction` field.

The other three original holes remain unchanged, all attached to
`lem-sp-finite-orientation-reduction`:

- `AlgebraicGeometry.ProEtale.SpFiniteOrientation.uniformizer_orientation_agreement`;
- `AlgebraicGeometry.ProEtale.SpFiniteOrientation.finite_orientation_reduction`;
- `AlgebraicGeometry.ProEtale.SpFiniteOrientation.unit_tower_mem`.

Thus this packet closes one original hole and adds one, leaving four direct holes
across its two Lean modules. It adds no axiom or data choice; its one structure cache contains no hole.

## No longer needed

Removed unused direct imports of `Sheaf.Paper.ExchangeProjectionSuppliedDomains`,
`Sheaf.Paper.DerivedPullbackTensorHom` and
`Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the finite proof uses the
specified ordinary-etale operations already supplied by its finite-purity imports,
without the general integral/rational operations or unrestricted completed twists.
Their mathematical citations in the node's statement remain unchanged.
Removed the duplicate public import of `Sheaf.SecSmoothPurity.ReductionCompatibilities`;
the proof-only `import all` entry retains the private coefficient-compatibility lemma.
The other public imports already supply the finite-purity statements and definitions.

Replaced `Sheaf.Paper.SmoothPurityTowerGluing` with
`Sheaf.Paper.SmoothPurityTowerGluingData`: only its `Levels` interface and reduction
field are used, without constructing the glued adjunction. This removes the gluing
construction and its chart-level construction imports from this module's closure.
The node `det-sp-tower-gluing` remains needed for that interface. The sole downstream
module, `Sheaf.Paper.ProEtaleCtfPullbackDomains`, directly imports the full gluing
module and the general derived operations itself; no consumer adaptation is needed.

No module, declaration or unit-route step is withdrawn. The new private proof import
supplies only the normalization step actually used.

## Where the brief, the DAG or earlier work was wrong

The last planned step already has its exceptional-reduction equality available as
`SpTowerGluing.Levels.reduction`. The remaining missing input is normalization of
the actual coefficient unit; the output equality requires only formal cancellation
once this is supplied. This delivery separates those two tasks explicitly.

The existing `reductionOrientation` declaration compares two rings at a single
common annihilating exponent. It cannot directly close `finite_orientation_reduction`,
whose supplied orientations have different annihilating exponents. The normalization
and Kummer comparison needed for that change of exponent have not been bypassed.
Likewise `unit_tower_mem` asks for uniform bounds in the intrinsic ringed-site
presentation on arbitrary schemes; the ordinary-etale finite-unit membership lemmas
are not directly the same statement. These three holes are retained honestly.

The original node's `proof_deps` included `def-exchange-projection` without listing
it in a proof step's `uses`. Its existing projection-unit step now records that
definition explicitly, so the dependency union matches the recorded proof.

## New nodes

`lem-sp-coefficient-unit-tower-normalized`, in
`dag/nodes/sec-smooth-purity/lem-sp-coefficient-unit-tower-normalized.json`, is the
normalization calculation for the strict coefficient unit. It retains the actual
quotient transitions and section/adjunction normalizations. Its proof uses the
free rank-one single complex, the representative formula `reduction_rep`, and
ordinary multiplication on scalar tensors. Equal levels, ramified extensions and
empty schemes satisfy this computation; flatness of the quotient is not assumed.
The structure-cache addition is recorded in
`coord/changes/finite-orientation-coefficient-ring-cache.md`; no existing statement
or definition body changes.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
