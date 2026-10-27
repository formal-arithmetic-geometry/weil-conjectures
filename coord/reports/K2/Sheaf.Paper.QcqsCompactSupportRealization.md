## What changed

Replaced the hole in `WeilConjectures.sfQcqsCompactSupportRealization_existsUnique`
with a reduction through the construction of a normalized natural morphism and the
ambient completeness and finite-coefficient comparison theorem. Existing declaration signatures,
public imports, definitions, and the chosen realization remain unchanged.

The combination is proved in Lean. First, a complete object with zero reductions
is zero by its defining Roos triangle: both product vertices are zero. Second,
triangulation of the integral constructible predicate and exactness of derived
reduction give conservativity on constructible objects by applying that argument
to a cone. Finally, the finite normalization and invertibility of the actual finite
mates make every reduction of the constructed morphism invertible. Their isomorphisms
transport the target constructibility and common support interval to the complete
source, proving source constructibility without a separate geometric bound. Conservativity
makes its components invertible; component inverses give a natural isomorphism.
The uniqueness of its hom determines the isomorphism.

Added proof imports of `SfIntegralConstructibleTriangulated`, `ProEtaleBoundedConstructibleTriangulated`,
`QcqsCompactSupportFiniteComparison`, and `QcqsCompactSupportNormalizedLift`.
Updated the original node's proof route and added the two prerequisite nodes.

## Proved and sorry left

This is a decomposition, not a completed geometric proof. One original hole is
closed and two holes are added; the net hole change is +1.

Closed: `WeilConjectures.sfQcqsCompactSupportRealization_existsUnique` (1 of the
item's 1 original holes). Its proof is complete from the stated prerequisites.
The private helpers `complete_zero_of_reductions` and
`constructible_of_complete_reduction_isos` and
`constructible_isIso_of_reductions` are proved without new holes.

Added and still sorry:

- `WeilConjectures.sfQcqsCompactSupport_finiteComparison`, node
  `lem-qcqs-compact-support-finite-comparison`.
- `WeilConjectures.sfQcqsCompactSupport_normalizedLift_existsUnique`, node
  `lem-qcqs-compact-support-normalized-lift`.

The first concerns completeness of the ambient proper/open image and its finite scalar mates,
without any recorded integral realization. The second constructs and rigidifies a
natural morphism, without asserting its invertibility. The original theorem's
invertibility assertion is established by the Roos/cone proof in this packet.
Each remaining theorem has its source and proof in words in its own module.
No sorry is added inside a definition or a private helper.

## No longer needed

Removed `lem-sf-qbar-etale-lower-shriek-constructible` from this node's proof
requirements: the argument is integral and does not use algebraically closed
coefficient finiteness. No Lean module is withdrawn: other consumers may still
need that node. No original public import is removed.

## Where the brief, the DAG or earlier work was wrong

The assigned node's proof array was empty and its only proof dependency concerned
Qbar etale lower shriek, rather than the normalized integral proper/open comparison.
The module docstring supplied the actual argument; the revised node records it.

`PurCompactSupport.recordedIdentification_existsUnique` cannot directly supply the
assigned theorem. It has separated structure-morphism and finite-field binders,
whereas this item has arbitrary base field and qcqs structure morphisms.

Uniqueness cannot be justified merely by evaluating reductions of derived arrows:
coherent reduction is fully faithful, but separate finite evaluations need not be.
The normalized-lift obligation retains the specific naturality and universal
projection normalization; proving that rigidity is still part of the remaining
work. No blanket faithfulness assertion has been introduced or used.

## New nodes

`lem-qcqs-compact-support-finite-comparison` states completeness of actual
completed proper/open image and invertibility of its actual positive finite scalar
mates. Its proof uses open extension, perfect quotient coefficients, the proper
image/total-limit comparison and their canonical completion units.

`lem-qcqs-compact-support-normalized-lift` states existence and uniqueness of the
natural morphism with the fixed chosen Roos projection equations. It concerns
construction and normalization, leaving invertibility to the proved combination.

No existing statement or definition is changed, so no interface change record is
needed. No forced adaptation of a module held by another group is included.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
