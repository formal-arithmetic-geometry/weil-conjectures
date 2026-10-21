## What changed

Restored the quarantined `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit` as a
public compatibility import of
`WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorUnit`. The adopted source
already completely proves `AlgebraicGeometry.derivedPullback_tensor_unit`.
The original archived module fails to compile because its withdrawn public
comparison-descent import no longer supplies the declarations in its signature;
the compiler reports unknown `Scheme`, `Quiver.Hom`, and `HasDerivedCategory`.
Reusing the complete adopted proof repairs the public interface without creating
a duplicate theorem. No adopted source module is edited.

Updated only the `lean` field of `lem-pc-derived-pullback-tensor-unit`, attaching
it to the existing canonical source declaration and copying its exact signature.
An automated comparison confirms that the old and new signatures differ only
by `IsAcyclicTensorKFlat` versus `IsKFlatTensor`. The two predicate definitions
have identical acyclic-total-tensor bodies. The mathematical statement, all
binders and universes, conclusion, dependency graph, proof steps and unit route
are preserved. The archived module is preserved, not withdrawn.

Read the source proof, the three recorded dependency statements, the unit
record, the parent descent proof, and Stacks `cohomology.tex`,
`section-derived-pullback` and `lemma-pullback-tensor-product` (Tag 079U).
The proof constructs the explicit unit using counit invertibility, obtains both
unit laws on K-flat complexes, and transports those identities along resolutions
using the proved isomorphism transport lemmas. No associativity assumption is
introduced. The unit K-flatness argument uses its right unitor and applies to
zero complexes, empty schemes and zero rings; no boundedness assumption is
added to the input complexes.

The restored compatibility module compiles through `lcompile.py` in 2.4 seconds.
A separate consumer probe compiled in 17.7 seconds and applies the reused theorem
to the entire original statement with the former predicate's explicit definition.
It checks equivalence with the source predicate by `Iff.rfl`; both the original
consumer statement and the reused theorem have exactly the axioms `propext`,
`Classical.choice`, and `Quot.sound`. This scratch probe is outside the delivered
Lean module set.

Change record: `coord/changes/T7-derived-pullback-tensor-unit-rework.md`.

## Proved and sorry left

This is a zero-hole quarantine repair. The archived module has zero `sorry`s;
the restored module has zero. The canonical theorem
`AlgebraicGeometry.derivedPullback_tensor_unit` and its two private transport
helpers have complete proofs. Holes closed: none (0 of 0). Holes added: none.
Split off: none. No new statement or definition is introduced.

## No longer needed

The duplicate implementation at the Sheaf path and its private transport helpers
are replaced by the existing adopted proof. The former public import
`Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent` and private
imports `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitKFlat`,
`Sheaf.Algebra.Homology.KFlatResolution`, and
`WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare` are removed from
this file. The canonical source module imports the corresponding source modules
and uses the same mathematical ingredients. Thus no mathematical dependency
node or target-reachable module is claimed pruned; no module is withdrawn and
no quarantine archive is deleted.

## Where the brief, the DAG or earlier work was wrong

The generic sorry-filling brief describes an earlier state: this item is
already-proved, quarantined sync repair. Its former public import is now an
empty withdrawn module, so restoring the archived implementation verbatim fails.
The complete adopted counterpart is the shortest route to restoration. Its only
theorem-signature spelling difference is the K-flat predicate name; this is not
a weakened or strengthened hypothesis. The node's stale Lean attachment is
reconciled with that canonical counterpart.

A scan of `lean/` and `quarantine/` finds the sole Sheaf-path direct consumer,
quarantined `Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalDescent`, and the
existing canonical consumer
`WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalDescent`. Their unit
calls use the same name, argument order and both unit-law conjuncts. No forced
adaptation is needed. The quarantined parent has separate outstanding sync
repairs, which this delivery does not claim to fix. The sole mathematical DAG
parent is `lem-pc-derived-pullback-monoidal-descent`, and its dependency remains.
`tools/downstream.py` reports `unknown module(s)` for the absent live module,
so the source scan explicitly includes the archive.

Required searches ran through `msearch.py`: LeanFinder returned eight generic
monoidal/Cartesian-pullback results, with no exact supplied-comparison theorem;
Loogle did not resolve the source-specific transport name; grep returned zero
hits. Direct repository search found the exact complete adopted counterpart.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
