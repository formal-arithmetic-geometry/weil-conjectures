# Representation.continuousCoefficient_subquotients

## Reason

Prove the existing theorem without changing its signature, and remove unused public imports.
The finite coefficient-ring theorem is not used by this proof about E-vector spaces.
The finite-dimensional topology API is needed only inside the proof.

## Old

```lean
public import Sheaf.RepresentationTheory.LAdic
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Algebra.Exact.Basic
```

The theorem's existing signature is unchanged; its old proof was `by sorry`.

## New

```lean
public import Sheaf.RepresentationTheory.LAdic
public import Mathlib.Algebra.Exact.Basic

import Mathlib.Topology.Algebra.Module.FiniteDimension
```

The same theorem now has a complete proof with four private proved helpers.
No public declaration or definition has changed its signature or meaning.
The coefficient-extension definitions remain available through LAdic.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RepresentationTheory.ContinuousCoefficientSubquotients | Y9 | Existing theorem proved; unused public imports pruned. |

`tools/downstream.py Sheaf.RepresentationTheory.ContinuousCoefficientSubquotients
--uses Representation.continuousCoefficient_subquotients` finds only the declaration in
its own module; no external Lean proof currently invokes it by name. The single direct
importer is `Sheaf.Paper.CoefficientHeartClosure`, which imports this module for its
planned proof dependency. Its declarations and definitions do not use either removed
public interface, so no adaptation is necessary. No other module is delivered or changed.
The downstream import closure contains 302 modules at the resumed check; their statements retain the same
objects because all existing declarations and definitions are unchanged.

## Status

landed 20261019T034408-L-428663 2026-10-19 (merge of deliver/Y9/Sheaf.RepresentationTheory.ContinuousCoefficientSubquotients)
