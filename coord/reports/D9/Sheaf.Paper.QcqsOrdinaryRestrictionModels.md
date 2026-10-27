## What changed

Replaced the hole in
`WeilConjectures.IntegralOnSlice.qcqsOrdinaryRestrictionModels` by a chain-level
assembly from two strictly smaller geometric and quotient-tower statements.
The original public signature and public import are unchanged.

The proof derives finite colimit preservation directly from `ordinaryAdjunction`.
It uses all-small-limit preservation for finite limits and countable products.
For each quotient tower it takes the existing `scalarRoosMap`; the private
`restrictionRoosIsIso` proves that this map is invertible under countable-product
preservation, without requiring an equivalence. Its degreewise matrix is the
additive biproduct comparison followed by two product comparison isomorphisms.
The private generic lemma `restrictionRoosModels` assembles the natural comparison
and its coordinates without unfolding geometric definitions.
The Roos isomorphism is that map followed by
`integralOperationsRoosFunctor.mapIso (tau.app P)`.
`podReindexingRoosNaturality` and tau naturality prove naturality. The existing
mapping-cocone coordinates and `podReindexingRoosCoordinates` prove the required
coordinate equalities. The private `restrictionRoosSnd` derives the shifted
coordinate directly from `scalarRoosMap_existsUnique` at arbitrary compatible
degrees by product extensionality, avoiding a rewrite through dependent indices.

Added proof imports of the two new modules and private proof imports of
`PodReindexingRoosComparison` and `IntegralAmbientOperationModels`; their existing
coordinate lemmas and the scalar map's defining equations are reused. No other
existing Lean module changes.

Validation: both new statement modules compile with the default transparency
settings (54.7 s and 54.5 s), and the item compiles in 24.1 s through
`lcompile.py`. All three files are below the 60 s per-file limit. The original
public theorem signature is byte-for-byte unchanged, both new node signatures
match their Lean declarations, and every Lean line has at most 100 characters.

## Proved and sorry left

Original holes: 1. Closed in the item: the direct hole of
`WeilConjectures.IntegralOnSlice.qcqsOrdinaryRestrictionModels`
(node `lem-fix-qcqs-ordinary-restriction-models`). The item has zero textual holes.

Added holes: 2, both entire public named theorem proofs in new modules:

- `WeilConjectures.IntegralOnSlice.qcqsOrdinaryRestrictionExact`, node
  `lem-fix-qcqs-ordinary-restriction-exact`: only ordinary pullback limit
  preservation and invertibility of its specified coefficient map.
- `WeilConjectures.IntegralOnSlice.qcqsOrdinaryQuotientRestriction`, node
  `lem-fix-qcqs-ordinary-quotient-restriction`: only the strict quotient-tower
  isomorphism preserving its augmentation.

This is a decomposition, not a net sorry reduction: 1 direct hole closed and
2 strictly smaller holes added. Neither new theorem asserts a Roos comparison,
its naturality, or either of its coordinate identities. Those are proved in the
item. Both docstrings give sources and complete proofs in words. The empty
scheme, zero module/complex and first quotient (n=0, exponent one) are covered;
there are no added nonemptiness, boundedness or completeness assumptions.

## No longer needed

No original import was removed, and no module is withdrawn. The original proof
plan's `lem-cbc-exact-product-functor-strict-limit`
(`Sheaf.Paper.ExactProductFunctorStrictLimit`) is not needed: the statement is
about strict chain models, so ordinary additive cocone coordinates suffice.
The step also does not require
`lem-weil-proetale-countable-products-exact`
(`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`): exactness of products
is needed for derived-limit interpretations, not for the ordinary chain
isomorphism. These are removed from this node's direct proof dependencies;
no claim is made that their modules leave the library's existing import closure.

`def-pur-integral-derived-operations` remains a direct dependency. The remaining
original geometric dependencies are retained under the new exactness node:
`lem-weil-pbc-proetale-immersion-limit-preservation`,
`lem-weil-proetale-weakly-etale-localization`,
`lem-pur-site-restriction-module-adjunction-exact`,
`lem-weil-pbc-proetale-restriction-preserves-limits`,
`lem-weil-pbc-module-sheaves-limits-sectionwise`, and
`prop-weil-pbc-proetale-constant-ring-map`.
`lem-weil-pbc-reduction-pullback-derived-tower` and the constant-ring-map node
remain under the new quotient-tower node. They are not globally pruned.

## Where the brief, the DAG or earlier work was wrong

The geometric declarations are genuine inputs but do not immediately specialize
to these fixed ordinary models with independent scheme/coefficient universes:
the immersion/module comparison is stated at coefficient size t+1, whereas this
item uses max u (t+1) and independently chosen adjoints. The new exactness node
records precisely that transport and coefficient normalization step.
The existing reduction/pullback theorem is stated on derived tensor models;
its application is not itself the strict ordinary quotient-tower isomorphism
with the augmentation normalization required here. The new quotient node records
that concrete transition/generator argument rather than repackaging the whole
item.

The original Roos step unnecessarily called for derived strict-limit comparison
and exact products. The proof uses the ordinary additive comparison and product
preservation only. The unit's realized route is unchanged; its realized statement
and step lists are empty. No target statement, existing definition, instance,
attribute or public import was changed.

## New nodes

`lem-fix-qcqs-ordinary-restriction-exact` is in
`dag/nodes/sec-six-functors/lem-fix-qcqs-ordinary-restriction-exact.json` and
`Sheaf.Paper.QcqsOrdinaryRestrictionExact`. It states the geometric input of the
original first proof step, with Type-0 limit preservation sufficient for the
finite-limit and countable-product uses in the item.

`lem-fix-qcqs-ordinary-quotient-restriction` is in
`dag/nodes/sec-six-functors/lem-fix-qcqs-ordinary-quotient-restriction.json` and
`Sheaf.Paper.QcqsOrdinaryQuotientRestriction`. It states the original second
proof step before any Roos construction. Both inherit the item's chapter, unit,
and blueprint ancestry, and record LeanSearch, LeanFinder and source grep checks.
No change record is required: no existing interface changes.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
