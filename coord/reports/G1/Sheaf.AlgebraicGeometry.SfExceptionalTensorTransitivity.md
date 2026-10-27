## What changed

Proved both theorems in `Sheaf.AlgebraicGeometry.SfExceptionalTensorTransitivity`,
keeping all existing public declarations, signatures, definitions and imports.
Added a private proof import of
`Sheaf.AlgebraicGeometry.SfEtaleCompactProjectionCoherence` and proved private
helpers for adjoint transposes, the composite-projection diagram, naturality,
projection associativity, tensor-unit
coherence and the normalization of the etale derived right adjoint.

The composition proof follows the node's eight-step plan: transpose along the
composite adjunction, use projection associativity and compositor compatibility,
and identify the scalar counit. The restriction proof applies the normalized
etale comparison, contracts the unit factor, and cancels the comparison
isomorphisms. No definition, target statement or source-library file changed.

## Proved and sorry left

Closed both original holes:

- `AlgebraicGeometry.Etale.sfExceptionalTensorTransitivity`.
- `AlgebraicGeometry.Etale.sfExceptionalTensorEtaleRestriction`.

Both realize `lem-sf-exceptional-tensor-transitivity`. No `sorry` remains in the
item module; no holes or modules were added. These proofs use the existing stated
projection coherence and normalized etale theorems as intended by stage 3.
This is two holes closed, zero added, with no decomposition.

## No longer needed

None. No original import, declared dependency, node or module was pruned. The
proof uses all six existing proof dependencies, and follows the unit's route.
Redundant trial imports of `Mathlib.CategoryTheory.Adjunction.Basic` and
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure` were removed; both are
already available through existing public imports.

## Where the brief, the DAG or earlier work was wrong

No statement or route defect was found. As the node already explains, the
additional tensor-invertibility hypothesis in the final consequence is
unnecessary under the universal hypothesis on the first tensor map; it is
retained verbatim. Concrete tensor-unit rewrites require care because the
coefficient-ring monoidal instance and constant complex involve expensive
definitional comparisons; the private abstract-coefficient coherence helpers
keep those comparisons out of the calculations.

Validation: the complete module compiled through `lcompile.py` in 32.1 seconds
with exit code 0. All seven original public signatures and five definition bodies
were compared with the shared source and are unchanged. The final module has no
development options, axioms or new public declarations; every line is at most
100 characters.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
