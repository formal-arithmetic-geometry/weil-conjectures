## What changed

Copied the quarantined module back into the delivery and proved
AlgebraicGeometry.Etale.primeFieldTensorSheaf_preservesZeroMorphisms.
The proof establishes zero preservation componentwise: the mixed tensor map is
zero on each etale object, and the presheaf-to-sheaf functor maps that zero map
to zero. The explicit local instance avoids universe ambiguity in the generic
left-adjoint instance. The devissage theorem remains unchanged.

## Proved and sorry left

Closed primeFieldTensorSheaf_preservesZeroMorphisms (1 of 2 existing
sorries). primeFieldTensor_devissage remains a named sorry, with its full
source and eight-step proof plan in the module docstring. No new sorry was
added.

## No longer needed

Removed the route-pivot imports `Sheaf.ConstructibleSheaf.GaloisCoverModuleDescent`,
`Sheaf.Paper.ConstructibleFiniteMonodromyFiltration`, and
`Sheaf.RingTheory.FiniteAlgebraExternalTensorFiltration`; the retained proof does
not use their declarations and the current route marks them as pruned. No DAG
nodes were changed.

## Where the brief, the DAG or earlier work was wrong

No statement or DAG error was found. The prior proof hole's generic
infer_instance route is universe-sensitive for this mixed tensor; the
componentwise proof avoids that elaboration issue.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
