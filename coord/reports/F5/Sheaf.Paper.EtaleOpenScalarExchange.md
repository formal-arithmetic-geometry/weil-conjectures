## What changed

Proved `AlgebraicGeometry.Etale.etaleOpenScalarExchange` in
`Sheaf.Paper.EtaleOpenScalarExchange`, with its signature unchanged.

The proof implements the node's six-step argument. A private categorical helper compares
inverse composites by their transposes under the open adjunction. A second calculation
obtains the pullback/scalar square by cancelling the common composite-map comparison in
the two instances of `scalarPullback_composition`. The published derived open base-change
mate theorem supplies the base-change unit formula.

The open tensor package's restriction identity uses `openScalarRestriction`, whereas the
statement uses `properOpenCoefficientPullbackIso`. A private helper identifies these maps
using the already proved `scalarPullback_eq`, exact-pullback transport, and the published
inverse-mate transport identity. Inverting the tensor package's `q_restricts` identity
then gives precisely the prescribed open-unit formula.

Added proof imports of all declarations of `Sheaf.SixFunctors.EtaleOpenTensorDefs` and
`Sheaf.Paper.EtaleProEtaleScalarMate`, and a proof import of
`WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange`.
Updated the item's DAG proof to record the explicit normalization bridge and its existing
node dependency. All helpers are private and proved; no other library module is changed.
The transparency option is scoped inside the proof blocks; no file-level command is added.

## Proved and sorry left

Closed one of one item holes:
`AlgebraicGeometry.Etale.etaleOpenScalarExchange`
(`lem-pur-etale-open-scalar-exchange`). Zero holes remain in the delivered module.
Zero holes added; zero statements split off.

Validation: the complete module compiled through `lcompile.py` in 8.3 seconds,
with exit code 0 and no warnings.

The proof uses the existing declared `scalarPullback_composition`, as required by the
stage-3 plan. Its proof remains an independent item; this delivery does not claim its
transitive axiom closure is already complete.

## No longer needed

None. All original imports and all four originally declared proof dependencies are used.
No module, declaration, or unit step is withdrawn or bypassed.

## Where the brief, the DAG or earlier work was wrong

The first step of the DAG assumes the open balancing unit formula with the canonical
pullback comparison. The published tensor package initially gives its restriction law
using a separately defined scalar-restriction mate. The delivery proves their equality
explicitly from existing normalization results; it does not assume the two definitions
are definitionally equal. The extra proof dependency records this bridge.

The generic transpose calculation applies to arbitrary categories and uses only unit
naturality, comparison naturality, functoriality, and injectivity of the adjunction Hom
bijection. Consequently the original hypotheses remain sufficient, including empty opens,
zero objects and rings, identity maps, unbounded inputs, and nonflat coefficient maps.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
