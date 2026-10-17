## What changed

Added the explicit-monoidal transport theorem integralResidue_tensorRoute_model_transport, then proved the assigned integralResidue_tensorRoute_model by specializing it to residueExchangeOrdinaryPullMonoidal. The module compiles.

## Proved and sorry left

- Proved AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorRoute_model.
- One sorry remains in integralResidue_tensorRoute_model_transport. It is a strictly more general statement with the ordinary monoidal structure supplied explicitly; its docstring records the transport argument and its DAG node is new-integral-residue-tensor-route-transport.

## No longer needed

The attempted direct generic normalization route and its imports are not used: Sheaf.Paper.IntegralResidueTensorRouteGeneric, WeilConjectures.CategoryTheory.ModuleObjects.Symmetric, WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits, and WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution. No existing DAG node was removed. The public intermediate declaration is recorded in coord/changes/integral-residue-tensor-route-model.md.

## Where the brief, the DAG or earlier work was wrong

The direct route in the prior attempt assumed that rewriting the named irreducible exchange functor would transport its dependent monoidal instance. Lean rejects that rewrite because the instance is part of the dependent expression. The explicit-monoidal transport split makes that dependency an argument and gives the target a real specialization proof.

## New nodes

- new-integral-residue-tensor-route-transport

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
