## What changed

The unchanged theorem
`AlgebraicGeometry.Scheme.AdicFibreComparison.adic_normalized_fibre_scalar`
is reduced to three genuine parts of the original seven-step argument:

1. `ScalarFibreComponents`: objectwise normalized fibre comparisons, including the
   actual finite quotient, completion-cone, pure-tensor and presented-germ formulas.
2. `ScalarFibreNaturality`: naturality of those specified components on every heart
   arrow, using the integral/fractional lattice argument.
3. `ScalarFibreCoherence`: tensor unit, tensor composition and mixed equations for
   the given components and normalized pullback.

The final proof constructs each natural iso by NatIso.ofComponents, and constructs
its existential heart comparison witnesses using the literal restrictions of the
raw unitor, associator and R.mixed. These restrictions are proved natural from the
original raw naturality equations. The germ and local normalization fields carry
through definitionally. No existing declaration, statement, structure field,
public import or public definition is changed. No source-library file is touched.

The new data module is ScalarFibreComponentData. Its objectwise data exclude
naturality and all coherence. Its coherence structure only asserts equations for
given components. It makes no existence assertion and contains no sorry.
Each remaining step is strictly part of the argument: the construction gives no
naturality or coherence, naturality constructs no components, and coherence
constructs no components or natural transformation. This is a decomposition,
not a completed geometric proof.

Change record: `coord/changes/K4-objectwise-scalar-fibre-reduction.md`.

## Proved and sorry left

Original hole closed: `adic_normalized_fibre_scalar`
(node `lem-per-adic-normalized-fibre-scalar`), by complete assembly from the
three statements. The item's current textual hole count is zero (originally one).

New postponed theorem proofs, one whole-proof sorry each:

- `scalar_fibre_components`, node `lem-per-scalar-fibre-components`.
- `scalar_fibre_naturality`, node `lem-per-scalar-fibre-naturality`.
- `scalar_fibre_coherence`, node `lem-per-scalar-fibre-coherence`.

Thus one upper hole is decomposed into three lower holes; holes closed 1,
holes added 3, net -2. No claim of net sorry reduction or final axiom closure.
There are no other sorry declarations in the delivered files and no postponed
data constructions. The explicitly constructed scalarHeartUnit, scalarHeartComp
and scalarHeartMixed have complete proofs.

Validation: all four new modules and the corrected original item compiled by
lcompile.py, with no diagnostics. The item compiled in 20.3 seconds. The first
item check required an explicit `(k := k)` at the existential construction call;
this was supplied and the final check passed. Delivery runs the independent
preflight and declaration-axiom probe.

## No longer needed

Removed the item's seven direct proof imports:

- Sheaf.Paper.RationalRealizationScalarCoherence
- Sheaf.Paper.AdicTowerReconstruction
- Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
- Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
- Mathlib.Analysis.Normed.Unbundled.SpectralNorm
- Sheaf.Paper.LisseCompletedSystemComparison
- WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm

These declarations remain in the helper nodes' proof plans, where they are used
for the finite-free, fraction or coherence computations. No mathematical
node or module is declared obsolete or withdrawn. In particular the pullback
node and the unit route remain needed. The combined comparison theorem is not
used as a premise: its public import supplies only the existing definitions.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or assigned repair. There was no ready-made theorem in
Mathlib or the adopted source giving the complete normalized scalar comparison.
Read the actual dependency signatures, the current unit and smooth-pullback
blueprint proof, and BS 6.8.4, 6.8.14 and 6.8.15 from the local PDF.

Edge cases: zero lattices use the zero-dimensional complete product; empty bases
supply no geometric-point obligations; identity and repeated coefficient fields
are allowed; arbitrary ramification uses the cofinal source exponent; no
flatness is imposed on quotient coefficient maps. The proof plans never commute
arbitrary tensor products or arbitrary pro-etale stalks with inverse limits.

A whole reachable-DAG audit encountered pre-existing unrelated ring-complex
cycles and an absent old localization-universal-property node. These are not
used to justify any proof and are not changed here; all direct dependencies
of the delivered node records are existing nodes or other delivered nodes.

## New nodes

`def-per-scalar-fibre-component-data` owns ScalarFibreComponents,
ScalarFibreCoherence and the three constructed full-heart restrictions.
It adds only data definitions and properties, no existential axiom.

`lem-per-scalar-fibre-components` records original steps 1--4 and the objectwise
chart comparison: finite stalk tensors, finite-free reduction-cone completion,
localization and the specified presentation formulas. It retains the same
normalized pullback on the selected fibres.

`lem-per-scalar-fibre-naturality` records original step 5: integral naturality,
fractional lattice morphisms, annihilating powers and common refinements.

`lem-per-scalar-fibre-coherence` records original steps 6--7: the fixed raw unit
and associator equations and mixed pullback square, via finite germ formulas,
limit projections and localization. All four nodes inherit the unit and chapter;
no unit or chapter record is changed. Their Mathlib searches were actually run
through msearch (LeanSearch, Loogle/LeanFinder, and grep); blueprint searches for
scalar fibre and finite-free completion found no equivalent blueprint node.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
