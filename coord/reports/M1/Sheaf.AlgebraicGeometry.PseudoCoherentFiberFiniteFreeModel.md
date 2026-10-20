## What changed

Restored and proved `Sheaf.AlgebraicGeometry.PseudoCoherentFiberFiniteFreeModel`,
including `AlgebraicGeometry.Scheme.exists_pseudoCoherent_fiber_finiteFree_model`.
The proof applies the existing local bounded-above pseudo-coherent fibre model and
then the existing bounded finite-free truncation model, composing their fibre-rank
identities. The two direct public imports of the source modules were replaced by a public
import of `Sheaf.AlgebraicGeometry.PseudoCoherentFiberBoundedAboveModel`; this
exposes the same statement dependencies while avoiding duplicate declarations from
the quarantined module graph. The corresponding interface change is recorded in
`coord/changes/PseudoCoherentFiberFiniteFreeModel-imports.md`.

## Proved and sorry left

The declaration
`AlgebraicGeometry.Scheme.exists_pseudoCoherent_fiber_finiteFree_model` is proved.
No `sorry` remains in the delivered module, and no new `sorry` was added.

## No longer needed

The proof does not need separate direct imports of
`WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex` or
`WeilConjectures.AlgebraicGeometry.DerivedFiberBetti`; the retained public
imports provide the declarations used by the statement and proof. The Mathlib
public imports remain because they are part of the restored module interface. Both
declared proof dependency nodes are used, and no DAG nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier quarantined packet retained direct public imports of source modules
whose declarations are already present through the dependency module, causing
duplicate `IsPseudoCoherent` and `derivedFiberBetti` declarations in the current
published graph. The proof and target statement are unchanged; making the
dependency public and removing those two redundant imports resolves the collision.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
