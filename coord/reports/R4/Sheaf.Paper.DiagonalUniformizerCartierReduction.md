## What changed

The item is reduced through the cyclic coefficient ring R = ULift(Z/l^(n+1)).
The public statement and its three existing public imports are unchanged.
The proof privately imports the cyclic projection and coefficient-square modules,
CartierReductionScalar, DiagonalFiniteCartierScalarCancellation, and
DiagonalFiniteCartierClassToArrow.

The new DiagonalCyclicCartierFrame module constructs the actual continuous
cyclic coefficient map, the tensor quotient of the base Tate line, its tensor
unit, and the Ext representative of an arrow with supplied finite endpoints.
A CyclicCartierFrame records only normalized coefficient and root comparisons;
it contains neither an arrow nor a Cartier equality. Its reduce operation is
an explicit composition of derived scalar extension and exact finite realization.
No data is chosen from an unproved existence theorem by these definitions.

The proved GeoCartierScalarUnitDerivedUnit module identifies the two unit
predicates for arbitrary sheaf objects. This keeps the associativity proof
generic and prevents repeated normalization of concrete supported modules.

The generic CoefficientArrowRoute and CartierScalarMaps structures in
DiagonalCoefficientArrowTransport group supplied diagrams and normalized maps.
Their Equation definition explicitly names the Yoneda square without asserting
it. The definition is irreducible, so checking a concrete square does not repeat
the costly expansion of the scalar functors. These records and this definition
keep concrete coefficient types out of repeated kernel comparisons; no shared
definitions are changed.

UniformizerRootFrame records exactly the supplied integral roots, finite roots
and normalized line endpoint, with the ordinary coefficient ring A left as a
parameter. The item's original QuotientLineRealization supplies its three fields.
UniformizerSquareData additionally groups the supplied route, endpoints, cyclic
frame and scalar maps. Its irreducible equation definition names the Yoneda
square without asserting it. This avoids repeating the concrete uniformizer
quotient ring and endpoint expressions in the theorem statement. The new
coefficient comparison requires no Noetherian or finiteness assumptions once
these normalized realizations are supplied. No existing shared interface changes.

The two new obligations separate parts of the original plan:

- diagonalCompleted_cyclicCartier projects the specified completed class only
  to Z/l^(n+1). It has no finite extension E or uniformizer quotient.
- diagonalCyclic_uniformizerSquare compares the two coefficient routes for an
  arbitrary initial diagonal arrow. It has no completed arrow, completion
  specification, limit characterization, or Cartier-class hypothesis.

The main proof obtains the cyclic class, extracts the canonical finite Cartier
scalar square, and applies the second obligation to the very same normalized
coefficient and root maps. Substitution identifies the two scalar adjuncts.
The proved class_eq_of_scalar_square in DiagonalFiniteCartierScalarCancellation
converts the supported GeoCartierScalarUnit to DerivedUnit and uses the
injectivity part of scalar_unit_ext_bijective in degree two, over abstract
coefficient rings. Its proof privately imports ScalarUnitExt and the generic
unit conversion. Keeping this argument in a separate module follows the
compile-time improvements to the data definitions and unit conversion. Finally it
uses finiteCartierArrowEquation_of_class to recover exactly the original arrow
equation. This proved generic conversion uses Equiv.symm_apply_eq directly,
avoiding simplification through concrete quotient-ring and sheaf expressions. Thus no
faithfulness assertion about forgetting scalars in derived categories is used.

The original DAG node now records those three steps and their actual imports.
No existing module besides the item, existing shared definition, or existing
public signature is changed.

Validation: every packet module compiled through lcompile.py. The final item
compiled without warnings in 15.4 seconds; the three supporting modules updated during the final
cleanup each compiled in less than 39 seconds. The original theorem signature
and all three original public imports were compared with the repository and are
identical. The existing hπ and hYpow binders remain verbatim; the proof uses hA
for coefficient factorization and hWpow for the canonical Cartier class instead.
The two inherited binders are explicitly referenced without changing their
types or the statement. There are no temporary Lean probes or profiling options
in the packet.

## Proved and sorry left

Original holes: 1. Closed in the item: 1, named
AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalUniformizer_cartierReduction.

Also proved without any new hole:
AlgebraicGeometry.ProEtale.geoCartierScalarUnit_derivedUnit
(lem-diagonal-scalar-unit-derived-unit), and
AlgebraicGeometry.ProEtale.DiagonalCoefficients.class_eq_of_scalar_square
(lem-diagonal-finite-cartier-scalar-cancellation), and
AlgebraicGeometry.ProEtale.DiagonalCoefficients.finiteCartierArrowEquation_of_class
(lem-diagonal-finite-cartier-class-to-arrow).

Added holes: 2, each exactly `:= by sorry` in a new public theorem:

- AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCompleted_cyclicCartier
  (lem-diagonal-cyclic-cartier-projection), in DiagonalCyclicCartierProjection.
- AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCyclic_uniformizerSquare
  (lem-diagonal-cyclic-uniformizer-square), in DiagonalCyclicUniformizerSquare.

There are zero holes in the item and zero in the three construction/data modules.
This is a decomposition, not a net proof: one upper hole is replaced by two
strictly separated obligations, a net addition of one hole in this packet. The existing
geoCartierCanonicalClass_scalar theorem used by the proof is already stated with its
own node; its hole is neither added nor changed here.

## No longer needed

No original public import is removed. The redundant direct import of
DiagonalCoefficientArrowTransport in the new coefficient-square module is
removed; its statement obtains the context structure from
DiagonalUniformizerRootFrame, which publicly imports the transport data. No existing module or declaration is
withdrawn, and no whole module is claimed pruned. The original broad proof
mentions of trace models, scalar definitions and reference definitions are
replaced in the item's direct proof_deps by the actual two intermediate
statements and the scalar cancellation, class-to-arrow and Cartier coefficient theorems. Those
interfaces remain transitively needed by the new statements. The cyclic
projection only unpacks the supplied IsDiagonalLimit hypothesis, so its plan
does not use det-prop-diagonal-tower-limit as an existence theorem; no such node
is withdrawn from the project.

Neither new obligation asserts trace compatibility or existence of finite
right-derived pushforward models; none of those modules is imported for this
proof. The explicit cyclic frame stores no projective trace or integration
identities. The coefficient-square obligation uses the existing scalar-compatible
diagrams, without requiring any property of their initial class.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies provide the normalized completed and scalar interfaces
and the ordinary finite Cartier coefficient theorem. They do not yet provide
the completed/condensed cyclic reduction comparison or the normalized
reassociation square between cyclic and uniformizer reduction. These are the
two precise missing comparisons stated here; no existing statement is marked
false or weakened. The original node's plan did not expose them as separate
Lean declarations.

Edge cases checked at statement level: n=0 retains exponent one; the empty
scheme and zero quotient ring give zero endpoints; the second obligation uses
derived coefficient extension so it assumes no flatness over the cyclic ring.
Its hA explicitly handles ramified quotients. The frame's root maps retain the
kernel normalization and integral projections, so an arbitrary sign or scalar
rescaling is not permitted. The coefficient continuation square asserts no
Cartier property of its arbitrary initial arrow. For general supplied ordinary
coefficients its factorization is on the pulled-back coefficient rings of P
and W, using the finite realizations, rather than a global identification of
the original condensed quotient with an arbitrary ordinary ring.

## New nodes

- lem-diagonal-finite-cartier-class-to-arrow: the proved conversion from a
  realized class equality to its arrow equation in
  Sheaf.Paper.DiagonalFiniteCartierClassToArrow.

- lem-diagonal-finite-cartier-scalar-cancellation: the proved scalar-adjunct
  cancellation in Sheaf.Paper.DiagonalFiniteCartierScalarCancellation.

- lem-diagonal-scalar-unit-derived-unit: the proved unit-predicate conversion in
  Sheaf.AlgebraicGeometry.GeoCartierScalarUnitDerivedUnit.

- def-diagonal-coefficient-arrow-transport: generic supplied diagrams and
  normalized finite scalar maps, in Sheaf.Paper.DiagonalCoefficientArrowTransport.

- def-diagonal-uniformizer-root-frame: supplied root normalization with a generic
  ordinary coefficient ring, in Sheaf.Paper.DiagonalUniformizerRootFrame.
- def-diagonal-cyclic-cartier-frame: explicit constructions and normalized
  coefficient-only frame in Sheaf.Paper.DiagonalCyclicCartierFrame.
- lem-diagonal-cyclic-cartier-projection: completed projection to the cyclic
  residue in Sheaf.Paper.DiagonalCyclicCartierProjection.
- lem-diagonal-cyclic-uniformizer-square: coefficient continuation, independent
  of completion or Cartier normalization, in Sheaf.Paper.DiagonalCyclicUniformizerSquare.

All new nodes record the three searches actually run for this item. Their
blueprint ancestor is det-prop-diagonal-tower-coefficients, as recorded by the
current item, with the inherited intermediate nodes retained in via. Whole
blueprint searches for Cartier coefficients, cyclic reduction, normalized cyclic
data, diagonal coefficient realization, and the exact scalar-unit predicate
found no blueprint node stating any of these formal interface comparisons
verbatim; same_as is therefore empty. The read-only ancestor utility returned
None for this module-created node, so the existing item field supplied the
ancestor, whose blueprint.is field was checked directly. No change
record is required: no existing definition or statement is changed.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
