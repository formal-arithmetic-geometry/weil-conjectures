## What changed

The assigned module now proves `tensorComparison` by obtaining a normalized
restriction tensor isomorphism from `tensorComparison_exists` and applying
`tensorComparison_compatibility`. Two new Sheaf modules state the strictly
simpler existence and compatibility parts of the original tensor-coherence
argument. The direct `ExactFunctor` proof import was removed from the assigned
module, and the exploratory ring-isomorphism transport import was removed from
both split modules because the split statements do not mention it.

## Proved and sorry left

The original `AlgebraicGeometry.Scheme.CoefficientTensorTransport.tensorComparison`
hole is closed by a real Lean proof combining the two strictly smaller
statements. No definitions contain `sorry`. The delivery adds exactly two
named proof holes:

* `AlgebraicGeometry.Scheme.CoefficientTensorTransport.tensorComparison_exists`
  (`lem-pbc-coefficient-restriction-tensor-comparison-existence`), whose proof
  is the existence of the normalized restriction tensor isomorphism.
* `AlgebraicGeometry.Scheme.CoefficientTensorTransport.tensorComparison_compatibility`
  (`lem-pbc-coefficient-restriction-tensor-comparison-compatibility`), whose
  proof is the compatibility equation for that isomorphism.

This is a decomposition of one upper proof obligation into two strictly
simpler source-level steps.

## No longer needed

The direct proof import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` and the
exploratory `Sheaf.Algebra.Homology.RingIsomorphismTensorTransport` imports are
not needed by the delivered reduction and were removed. The original node's
three long proof steps are represented by the two new nodes; no declared DAG
dependency was discarded from those new proof plans.

## Where the brief, the DAG or earlier work was wrong

The original node bundled existence of the restriction tensor comparison and
its pullback compatibility into one theorem. The available declarations did
not expose a short direct proof of that bundle, so the node needed two
strictly simpler intermediate statements. No target statement or definition
was changed.

## New nodes

`dag/nodes/sec-proper-base-change/lem-pbc-coefficient-restriction-tensor-comparison-existence.json`
records the existence reduction and its module
`lean/Sheaf/Paper/ProEtaleCoefficientTensorComparisonExists.lean`.

`dag/nodes/sec-proper-base-change/lem-pbc-coefficient-restriction-tensor-comparison-compatibility.json`
records the compatibility reduction and its module
`lean/Sheaf/Paper/ProEtaleCoefficientTensorCompatibility.lean`.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
