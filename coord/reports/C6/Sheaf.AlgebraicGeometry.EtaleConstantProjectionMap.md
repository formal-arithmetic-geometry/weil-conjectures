## What changed

Proved both theorems in `Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap`, with all
existing signatures and definitions unchanged. The normalized constant-presheaf core
is constructed using componentwise identity isomorphisms, as in the existing
`Functor.Monoidal.const` construction. Constant-sheaf flatness follows from the proved
geometric-fiber criterion and `Point.sheafFiberConstantSheafIso`.

Added the proof-only import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat` and recorded the actual
proof route in `def-kun-constant-projection-morphism`.

## Proved and sorry left

Closed 2 of 2 holes, both belonging to `def-kun-constant-projection-morphism`:

- `AlgebraicGeometry.Etale.exists_etaleConstantPresheafCoreMonoidal`
- `AlgebraicGeometry.Etale.etaleConstantSheaf_preservesFlat`

No holes remain in the delivered module. No holes added; no statements split off.
The module compiled cleanly through `lcompile.py`. Separate `#print axioms` checks
for both proved theorems list exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

None. The node had no prior proof dependencies, and no imports were removed. All
original public imports support the existing declarations and remain unchanged.
No new flatness, stalk, tensor-comparison, or coherence lemma is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The definition node had no recorded proof
steps or proof dependencies despite containing two holed theorems. Its updated proof
now records their implementations and the existing geometric-fiber flatness node.
The unit route is unchanged; its realization record assigns no steps to this node.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
