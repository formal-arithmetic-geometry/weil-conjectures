## What changed

Completed the zero-hole retirement assigned by coord/retire-items.tsv.
Withdraw lean/Sheaf/Algebra/Homology/TensorBicomplex.lean using deleted.txt.
Redirect def-weil-pbc-tensor-bicomplex's Lean attachment and implementation plan
to the already retained upstream constructions:
HomologicalComplex₂.tensorBicomplex and tensorBicomplexMap in
WeilConjectures.Algebra.Homology.TensorBicomplexExtension, and ChainComplex.tensorMap
in its publicly imported WeilConjectures.Algebra.Homology.TensorBicomplex.
No upstream file or consumer changes. Change record:
coord/changes/retire-tensor-bicomplex-n1.md.

The server compiled scratchpad/Upstream__probe.lean in 1.2 seconds. It establishes
by rfl that the retained aliases are the original Mathlib expressions and the
retained tensorMap is the old chainTensorMap composite. Axiom inspection of all
three retained declarations reports only propext, Classical.choice and Quot.sound.
Searches used leanfinder, loogle and the launcher's grep service, supplemented
by direct source searches and reading Mathlib's bifunctor construction.

## Proved and sorry left

Original holes: 0. Holes closed: 0. Holes added: 0. Split off: 0.
No sorry remains in any delivered module; this is a duplicate retirement,
not a new theorem proof. All three retained constructions are sorry-free.

## No longer needed

Pruned module: Sheaf.Algebra.Homology.TensorBicomplex, including its duplicate
HomologicalComplex₂.chainTensorMap name. No current source imports it or refers
to chainTensorMap. Its direct imports Mathlib.Algebra.Homology.Bifunctor,
Mathlib.Algebra.Homology.Additive, Mathlib.CategoryTheory.Functor.Currying and
Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic leave with the duplicate;
they remain needed by the retained upstream constructions and are not claimed
as globally pruned. No DAG node or mathematical dependency is withdrawn.
The original node remains attached to the existing upstream definitions.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item with sorry, but the current queue
explicitly marks this module retire with zero holes. The retirement inventory's
single Sheaf consumer has already migrated: its file is absent and the current
upstream FlatResolutionTorComparison already imports TensorBicomplexExtension.
The inventory says the named upstream twin lacks tensorBicomplex and
tensorBicomplexMap; they now exist verbatim in TensorBicomplexExtension.
The chainTensorMap construction is upstream ChainComplex.tensorMap.
No source-library declaration is removed or altered, and the unit route is kept.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
