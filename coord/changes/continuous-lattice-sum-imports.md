# AlgebraicGeometry.ProEtale.continuous_lattice_sum

## Reason

The statement and proof use continuous functions, ordinary tensor products and the
recorded coefficient ring. The previous imports exposed the full integral derived
coefficient interface, general ringed-site module categories and cochain sheaf
tensor monoidal structures, none of which this sectionwise theorem needs.

A local irreducibility annotation keeps `Padic.coefficientExtensionIntegers`
folded while elaborating this module. Profiling the tensor statement showed
expensive scalar-instance inference through its DVR witness construction.
The definition itself, its data, and every consumer's reduction behavior are unchanged;
the annotation is local to this file. The private tensor-coordinate constructor
has a proved pure-tensor equation and uses abstract scalar types. The private
coordinate constructors are also locally irreducible, with proved evaluation
and pure-tensor equations used by the proof. These attributes expose no new API
to importers and alter no public definition. The private algebraic helpers use
commutative rings, and the continuity/tensor helpers use topological commutative
rings; no normed-field structure is needed in their signatures. This avoids
repeated normed-instance searches inside the general coordinate argument.

## Old

```lean
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.ContinuousIntegralCoefficients
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
```

The old file has no local irreducibility annotations or tensor-coordinate helper.

## New

```lean
public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Topology.ContinuousMap.Algebra
```

```lean
attribute [local irreducible] Padic.coefficientExtensionIntegers
-- The existing theorem declaration follows, unchanged in signature.
```

All existing public declaration signatures and the actual inclusion definition are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ContinuousLatticeSum | U4 | Uses the smaller imports directly. |

`python3 tools/downstream.py Sheaf.Paper.ContinuousLatticeSum` reported zero
current downstream Lean modules. Its DAG parents and blueprint unit route remain
in place; this change does not withdraw the item or any dependency module.

## Status

landed 20261021T120739-L-3942576 2026-10-21 (merge of deliver/U4/Sheaf.Paper.ContinuousLatticeSum)
