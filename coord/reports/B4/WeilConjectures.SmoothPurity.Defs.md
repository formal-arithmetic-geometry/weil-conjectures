## What changed

Partial delivery of WeilConjectures.SmoothPurity.Defs: the four original holes
remain. This packet certifies the already reported statement defect and proves the
formal adjunction assembly step of the planned smooth-purity construction.

Added Sheaf.SmoothPurity.OpenDimensionObstruction with the fully proved theorem
AlgebraicGeometry.ProEtale.CondensedRing.isZero_unit_of_open_positive_purity.
For an open immersion j and positive d, any isomorphism of the claimed purity
shape forces the source regular coefficient module to be a zero object.
The proof uses the actual open-adjunction unit comparison and zeroth cohomology:
the source is a single in degree zero, while the shifted Tate single is in
degree -2d. It never imports SmoothPurity.Defs or uses its disputed instance. The
cohomology argument is abstracted into the proved private helper
isZero_of_single_shift_iso over an arbitrary abelian category.

Added Sheaf.SmoothPurity.PointUnitNonzero and proved
not_isZero_unit_on_separablyClosed_point. It evaluates the actual condensed
coefficient ring at a singleton and reflects nonvanishing through the library
point-equivalence API. The latter existing equivalence theorem still has a
sorry in the source library; this is a proof from that named declaration, not
an axiom-free proof of that equivalence.

The assigned source module imports both new modules privately and consumes them in
smoothPurityMap_not_isIso_of_open (private). Given a nonzero coefficient unit,
that lemma rules out invertibility of the actual smoothPurityMap for an open
immersion with positive proposed dimension, for any choice of the trace.
It occurs before isIso_smoothPurityMap and uses only explicitly hypothetical
invertibility to form asIso. The additional private theorem
smoothPurityMap_point_dimension_one_not_isIso specializes it to the identity
of a separably closed point and d=1, using the proved unit nonvanishing. Thus
the point example has no external nonvanishing premise. All these proofs
occur before the disputed instance. Three proved private identity-morphism
instance lemmas are registered locally inside PointObstruction to make the
point presentation explicit during this proof. Their registration ends with
that section. The dispute comment points to the example.

Also proved isIso_smoothPurityMap_of_trace_formula (private), the final formal
assembly step of the written plan. Given an actual comparison isomorphism e
and the exact counit formula for smoothTrace, it identifies smoothPurityMap
with e.hom and proves invertibility. This supplies no arbitrary comparison and
adds no geometric hypothesis to an existing declaration. The comparison and
normalization formula remain to be constructed.

All existing source declarations, signatures, attributes, public imports and
non-theorem bodies are preserved. No normalized witness is selected and no
existing proof is replaced. The existing isIso node records the completed
formal adjunction step; its statement, dependency list and unit route are unchanged.

Validation: the final lcompile.py --all check compiled all three delivered Lean
modules without warnings. Profiling options were removed. The abstract
cohomology proof was checked independently of smoothTrace and the disputed
instance; the point counterexample is placed before that instance.

## Proved and sorry left

Assigned module: 0 of 4 holes closed; 0 holes added; 0 split off. The new theorem
and private consumer are genuine proved results, not a decomposition of purity
and not a completed definition repair.

New proved declarations:

- AlgebraicGeometry.ProEtale.CondensedRing.isZero_unit_of_open_positive_purity
  (lem-pur-open-positive-dimension-obstruction), with the private proved helper
  isZero_of_single_shift_iso.
- AlgebraicGeometry.ProEtale.CondensedRing.not_isZero_unit_on_separablyClosed_point
  (lem-pur-geometric-point-unit-nonzero), with the proved private helper
  condensed_unit_not_isZero.
- AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityMap_point_dimension_one_not_isIso
  (private concrete counterexample), with proved private pointObstruction_locallyOfFiniteType,
  pointObstruction_quasiCompact and pointObstruction_isSeparated.
- AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothPurityMap_of_trace_formula
  (private, formal assembly of lem-route-is-iso-smooth-purity-map).
- AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityMap_not_isIso_of_open
  (private consumer in the assigned module).

Every retained original hole:

- AlgebraicGeometry.ProEtale.CondensedRing.smoothTrace
  (def-route-smooth-trace).
- AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothPurityMap
  (lem-route-is-iso-smooth-purity-map).
- AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_zero_of_isOpenImmersion
  (lem-route-smooth-purity-iso-zero-of-is-open-immersion).
- AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_comp_openImmersion
  (lem-route-smooth-purity-iso-comp-open-immersion).

No new sorry or axiom is added. In particular the pre-existing smoothTrace data
hole is not filled by arbitrary existence or an unnormalized map.

## No longer needed

None. No existing imports, nodes, declarations or modules are pruned. The finite,
integral and condensed normalized purity route remains necessary and unchanged.
The cohomology audit is not a replacement route for the blueprint's unit.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the elaborated smoothTrace, smoothPurityMap and
isIso_smoothPurityMap signatures omit SmoothOfRelativeDimension d f.left.
The surrounding section variable is insufficient to retain a binder unused
by the declaration's type and body. Thus the instance purports to prove
invertibility even for an open immersion and d=1. Its intended DAG statement
requires actual smoothness of relative dimension d.

The new theorem formally proves the cohomological obstruction without using
the disputed instance: such an isomorphism at positive d makes the regular
module zero. The private consumer adds an explicit nonzero-unit premise to
conclude noninvertibility of the actual map. The native unit nonvanishing
is proved from the existing point-equivalence declaration and the concrete
coefficient ring. The private point theorem therefore gives the specific
counterexample without a nonvanishing premise. It does not invoke the false
instance, extract False from it, or use it to close any other hole.

The defect was already identified by E1. This packet adds the mathematical
certificate missing from that report. No correction for this module is listed
in coord/upstream-statement-exceptions.tsv. Restoring the smoothness binders
requires a protected source-signature correction; changing the trace body so
that Lean starts retaining the binder would also change the public interface.
The missing normalized trace construction and its presentation bridges remain
unresolved. Introducing an unconditionally invertible witness would merely
repeat the already withdrawn false NormalizedWitness statement.

## New nodes

lem-pur-open-positive-dimension-obstruction: the proved cohomological obstruction,
with its exact Lean statement, proof in words and three kinds of Mathlib search.
It records an edge-case audit of lem-route-is-iso-smooth-purity-map, and introduces
no new unfinished mathematical item. The empty-source and d=0 edge cases are
explicit: an empty source satisfies the conclusion, and d=0 is excluded by hd.

lem-pur-geometric-point-unit-nonzero: nonvanishing of the actual native regular
coefficient module on a separably closed point. Its proof uses the existing
lem-pe-point-module-pullback-equivalence, which remains an existing unfinished
dependency. The theorem adds no new hole and completes the nonvanishing premise
of the counterexample.

Change record: coord/changes/B4-smooth-purity-degree-obstruction.md.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
