## What changed

Filled two proofs in `Sheaf.Paper.ConstantGeometricStalkUnit` using existing proved
constructions. `integralChainUnit_existsUnique` reuses the arbitrary-map strict Roos
candidate, its generator equations, its zero shifted component and its uniqueness
lemma from `ConstantWeilStructure`. `finiteUnit_canonicalWeil` identifies intrinsic
multiplication with the tensor pullback regular-module map by left-adjoint uniqueness,
then applies the existing finite tensor-unit triangle in degree zero. The shared
adjunction equation is factored into the proved private helper `finiteUnitHom_tensor`,
which also supplies the existing `finiteUnitHom_isIso` proof. Local reducibility
attributes around the two new proofs prevent unnecessary unfolding of large
comparison constructions; these attributes end with their proof sections.
Elaboration runs synchronously
(`Elab.async false`) to avoid scheduling overhead in this large module. All linters
and kernel checking remain enabled, and no time limit is raised.

Added private proof imports (`import all`) of `ConstantWeilStructure` and
`CanonicalCoefficientPullbackReduction`. Updated the owning node's proof descriptions
to record these concrete arguments. No definitions or declaration signatures changed.

## Proved and sorry left

Closed 2 of the original 6 holes, with no added holes:

- `WeilConjectures.ConstantGeometricStalkUnit.integralChainUnit_existsUnique`.
- `WeilConjectures.ConstantGeometricStalkUnit.finiteUnit_canonicalWeil`.

Four original holes remain, all owned by `lem-zl-constant-geometric-stalk-unit`:

- `WeilConjectures.ConstantGeometricStalkUnit.integralChainUnit_isIso`.
- `WeilConjectures.ConstantGeometricStalkUnit.finiteOperator_unit`.
- `WeilConjectures.ConstantGeometricStalkUnit.integralOperator_unit`.
- `WeilConjectures.ConstantGeometricStalkUnit.rationalOperator_scalar`.

This is a partial proof delivery, not a decomposition: no split-off statements or
new sorries were introduced. The existing remaining proofs retain their source and
complete natural-language proof docstrings.

Validation: the server compiled the final module cleanly in 47.4 seconds, below
the unchanged 60-second limit. The delivery tool also runs its axiom and hole probe.

## No longer needed

None. No imports, nodes, modules, unit steps or source-library declarations are
withdrawn. The new proofs use constructions in the existing declared dependencies;
the planned finite, integral and rational operator arguments remain needed.

## Where the brief, the DAG or earlier work was wrong

The strict candidate and its uniqueness proof in `ConstantWeilStructure` already
apply to arbitrary scheme morphisms, although the public
`constantWeilChainUnit_existsUnique` theorem restricts to isomorphisms. Reusing those
proved private helpers avoids rebuilding that argument. The existing finite
coefficient triangle also supplies the tensor computation required by Step 3.
The unit route is unchanged.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
