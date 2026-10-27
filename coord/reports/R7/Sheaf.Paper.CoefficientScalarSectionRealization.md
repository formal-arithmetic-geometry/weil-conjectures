## What changed

Filled `coefficientScalarSectionRealization` by constructing its comparison data from
`internal_section_scalar_adjunction`, the existing ordinary scalar-extension constraint
coherence theorem, and the specified internal derived scalar tensorator. The internal
adjunction's unit normalization identifies its derived extension with the native one by
left-adjoint uniqueness. This comparison transports the computation equation and the
Hom formula. The ordinary monoidal structure is transported through the scalar pair's
object equalities, including its full scalar generator formula. Precomposition by the
product section equivalence is fully faithful; its inverse on natural isomorphisms
constructs the section tensorator and proves the internal identification square.

The signed totalization representative equation is isolated in
`Sheaf.Paper.CoefficientScalarTensorRepresentative`. This theorem assumes the already
constructed comparisons and their normalization properties and asserts only that
representative equation. It does not construct a scalar pair, an adjunction, an ordinary
monoidal structure, or a derived tensorator. No existing statement or definition changes.
The original public import is preserved; proof imports are private. Generic categorical
lemmas construct the adjoint-uniqueness and whiskering comparisons with their component
formulas, and transport the Hom equation. The ordinary generator calculation is proved
over an arbitrary ringed site and then specialized through explicit section-generator
equations. The small alias `internalScalarExtension` is locally reducible; the main proof
keeps the underlying derived functors and large tensor constructions locally irreducible.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.coefficientScalarSectionRealization`
(node `lem-sfb-coefficient-scalar-section-realization`). Added one hole in
`AlgebraicGeometry.ProEtale.CondensedRing.coefficientScalarTensorRepresentative`
(node `lem-sfb-coefficient-scalar-tensor-representative`). This is a decomposition:
one hole closed and one strictly smaller hole added, net zero explicit holes in the packet.
The import-closure ledger is measured separately by the delivery tools. The item module
has no remaining holes. There are no holes in definitions or private helpers.

Validation: `lcompile.py` accepted the realization module in 54.2 seconds; the new
representative module also compiled. The temporary profiling settings were removed.
Static checks confirm the unchanged public theorem signature, the permitted existing-node
changes, exact agreement between the new node's Lean statement and its module, and the
100-character Lean line limit. The delivery command reruns the final preflight checks.

## No longer needed

The declared dependency `lem-pe-internal-kflat-scalar-tower-realization`
(`Sheaf.Algebra.Homology.InternalKFlatScalarTowerRealization`) is unnecessary for this
argument: no coefficient tower is used. The native derived adjunction's unit formula
and left-adjoint uniqueness identify the internal scalar pair directly.

The declared dependency `lem-sfb-scalar-ordinary-tensor-comparison`
(`Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison`) is unnecessary: the stronger
existing scalar-extension constraint-coherence theorem supplies the full monoidal
structure and its arbitrary-scalar generator formula. Neither dependency is added as a
direct proof import. The item's original data import is preserved. There were no unused
initial proof imports to remove; no global withdrawal of either dependency is claimed.

The internal-section tensor comparison and the section tensor representative theorem
remain needed by the split-off signed totalization equation. No module is withdrawn,
no source-library declaration is removed, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The coefficient-tower realization dependency was more general machinery than the
single-map identification needs. The separate ordinary scalar tensor comparison is
redundant with the stated full constraint-coherence theorem. The normalized scalar
adjunction theorem itself is usable: its section-ring and equivalence data agree with
the coefficient realization data without changing any mathematical statement.

`blueprint_refs.py ancestor lem-sfb-coefficient-scalar-section-realization` returned
`None`: its chain follows `created.item` as a node ID, whereas this stage-3 node records
a module name there. The new node retains the item's explicit blueprint ancestor
`det-thm-sfb-proper-base-change-rational`, rational proof (3), with the full existing
origin chain extended by the item node. The cited current blueprint text was read.

The remaining representative equation was checked on zero complexes, zero coefficients,
identity coefficient maps and arbitrary unbounded complexes. Its hypotheses retain the
existing flat-term K-flat tests, generator normalization, and the prescribed internal
tensorator; no boundedness or enough-points assumption is introduced.

## New nodes

`lem-sfb-coefficient-scalar-tensor-representative`, in
`dag/nodes/sec-six-functors-basics/`, records the signed totalization compatibility step
of Stacks 07A4 (constituent isomorphisms from 03EL). Its module has one public theorem
with its source and a complete natural-language proof. LeanSearch, LeanFinder, Loogle
and Mathlib grep searches found no theorem for this prescribed compatibility square.
The generic sheaf bilinear universal property is used as a tool at the ordinary
comparison step, as it already is in the scalar-adjunction dependency's proof route.

Related existing nodes were also checked: `lem-sfb-section-tensor-conjugate-computation`
is the unary extension/restriction versus tensor-right comparison for the integral
coefficient model, whereas the new equation is the binary tensorator in the S-module
category. `lem-sfb-scalar-tensor-comparison` supplies a comparison for simultaneous
`ScalarHomModels`; it does not identify that chosen tensor model and scalar comparison
with the specified internal tensorator and the conjugated section tensor in this item.
The new lemma is this compatibility step, rather than a duplicate construction of an
unspecified scalar tensor comparison.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
