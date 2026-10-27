## What changed

Reduced `AlgebraicGeometry.Scheme.RingedRestrictionExchange.open_comparison`
to the ordinary geometric comparison `ordinary_open_isIso`, in the new module
`Sheaf.AlgebraicGeometry.RingedOrdinaryOpenExchange`. The derived assertion now
has a complete Lean proof: on a K-injective complex, `exchange_chain` expresses
the exchange between invertible comparison factors. Open pullback preserves
K-injectives, so both right-derived cochain units are invertible. The ordinary
exchange is invertible degreewise, hence on complexes and after localization.
Cancellation proves invertibility on K-injectives; a resolution and naturality
transfer it to every derived object. The transfer is a proved private lemma
over abstract functors, specialized to the four specified ringed operations.

The new theorem is strictly the ordinary part of the original conjunction. It
contains neither derived categories nor resolutions, and its documented proof
is the sectionwise fibre-product identification with the specified counit mate.
The existing section-normalized comparison theorem only treats the actual rings
on the canonical pullback; the new statement retains arbitrary coherent ring
presentations and a chosen Cartesian square. The parent DAG records the split.
No existing statement, definition, exported attribute or public import was changed.
The private transfer uses local transparency settings and a two-step specialization
to the native module-category instances; this avoids expensive conversions without
changing an imported construction or any public interface.

## Proved and sorry left

One of the five original holes was reduced, by declaration name:
`AlgebraicGeometry.Scheme.RingedRestrictionExchange.open_comparison`.
Its derived half is proved in Lean from the ordinary half and the existing
chain-unit and K-injective preservation theorems. This is a decomposition,
not a sorry-free proof of the entire open-comparison assertion.

Four original holes remain untouched, all attached to
`lem-sf-ringed-restriction-exchange-open-descent`:

- `AlgebraicGeometry.Scheme.RingedRestrictionExchange.open_sectionwise`
- `AlgebraicGeometry.Scheme.RingedRestrictionExchange.openCube_exists`
- `AlgebraicGeometry.Scheme.RingedRestrictionExchange.open_restriction`
- `AlgebraicGeometry.Scheme.RingedRestrictionExchange.identity_normalization`

One hole is added:
`AlgebraicGeometry.Scheme.RingedRestrictionExchange.ordinary_open_isIso`,
attached to `lem-sf-ringed-ordinary-open-exchange`. Its body is exactly `by sorry`;
the complete geometric proof is in its docstring and node. Thus the delivery
closes one original hole and adds one strictly lower hole: net hole count zero.
No holes occur in definitions or private helpers.

Validation: the final item module compiled without diagnostics in 43.7 seconds
through `lcompile.py`. The new ordinary module compiled in 6.9 seconds. The
diagnostic options and temporary diagnostic modules were removed.

Edge cases: the ordinary section formula and the resolution calculation apply
to the empty open and zero ring. No nonempty-cover or boundedness assumption
was added; the proof resolves an arbitrary derived object.

## No longer needed

No original imports or dependency nodes are removed. In particular,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`
remains necessary: it supplies `rightDerivedFunctorUnitQ_naturality` and
`rightDerivedFunctorUnitQ_eq`, used by the existing cochain comparison helpers.
The original dependencies support the existing proofs and the four untouched
clauses. No module is claimed to be globally pruned; the blueprint unit route
is preserved.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The ordinary comparison supplied by
`ProEtaleOpenRestrictionCounit` fixes actual inverse-image rings and the canonical
fibre product. Applying it to the arbitrary coherent presentations in
`open_comparison` requires the ordinary normalization and transport argument
recorded in the new lemma; it is not a direct application with matching binders.
The derived transfer itself needs no additional geometric lemma.

## New nodes

`lem-sf-ringed-ordinary-open-exchange` records the ordinary open exchange for
arbitrary coherent coefficient presentations. It is the geometric part of step 6
of the existing parent plan, strictly below the original ordinary-and-derived
conjunction. The new module imports the existing ordinary-operation definitions
from `RingedExchangeChainUnit`. No change record is required because no existing
interface or definition changes. Temporary diagnostic modules were removed before delivery.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
