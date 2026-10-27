## What changed

Replaced the hole in `sfAffineBaseP1TraceAdjunction` by a construction of an
adjunction from the explicit diagonal-kernel unit and inverse-projection trace
counit. The proof transports the left adjoint to the supplied identity/proper
compactification, proves its projection equation, and deduces the required
coefficient-unit equation from compactification projection right unitality.
The existing theorem signature and both existing definitions remain unchanged.
No adopted source-library file is changed.

Three smaller argument steps are stated in new modules. `SfP1CoordinateIntegrals`
asks only for the coefficient pullback and the two degree-zero diagonal integral
identities in standard-chart coordinates; it asserts no adjunction or triangles.
`SfDiagonalKernelIntegrals` constructs all its comparison, unit and counit maps
explicitly, and asks for their triangles given the two integrals. The latter
statement works for any proper morphism and a pulled-back even shifted line.
None of these theorems chooses data for a public definition: all new definitions are
actual composites of already constructed canonical maps. The existential datum
is eliminated only in a theorem proof.

The adjunction is constructed directly from its component triangles, retaining
the specified counit by construction. Private helpers prove the unit normalization calculation generically,
before specializing to module coefficients. This avoids comparing the two
definitionally equal derived monoidal instances at concrete coefficients.
Compilation and the delivery tool provide the final validation.

## Proved and sorry left

Closed the existing direct hole in
`AlgebraicGeometry.Etale.sfAffineBaseP1TraceAdjunction`
(node `lem-sf-affine-base-p1-trace-adjunction`). Its proof is complete from the
three new statements. This is a decomposition, not a net mathematical closure:
one old hole closed and three lower holes added, for net minus two holes.

The only holes added and left by this packet are:

- `AlgebraicGeometry.Etale.sfCompactificationKernelTransport`
  (`lem-sf-compactification-kernel-transport`).

- `AlgebraicGeometry.Etale.sfP1CoordinateIntegrals`
  (`lem-sf-p1-coordinate-integrals`).
- `AlgebraicGeometry.Etale.SfDiagonalKernel.triangles`
  (`lem-sf-diagonal-kernel-integral-triangles`).

There is no `sorry` in the assigned module or any new definition, and each new
hole is a named public theorem with source, a full proof in words and its node.

## No longer needed

No node or module is claimed globally pruned. The unit's projective-line route,
its supported diagonal, both coordinate integrals and both triangles remain.
The assigned module no longer directly imports:

- `Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals` and
  `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: these are proof inputs of
  `SfP1CoordinateIntegrals`.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer` and
  `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalCartier`: the existing integral
  theorem supplies the normalized supported class and the Cartier witness.
- `Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`,
  `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons` and
  `Sheaf.Paper.RingedProjectionTensorComposition`: these belong to the generic
  coordinate-contraction and diagonal-kernel proof, not the final assembly.
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`: its canonical symmetry is
  used by the new kernel construction and is available through that import.

These dependencies remain in the lower proof plans and/or import closure.
The direct proof dependency `lem-weil-pbc-adjunction-of-natural-bijection` is
removed: the component-triangle constructor of `CategoryTheory.Adjunction`
builds the adjunction directly, so no separate Hom-bijection theorem is used.
This does not assert that this node is globally unreachable.
All public imports of the assigned module are retained. The added proof imports
are the coordinate-integral reduction, compactification transport reduction and
existing compactification unitality module.

## Where the brief, the DAG or earlier work was wrong

The earlier plan is mathematically retained. Its coordinate reindexing from
`ULift (Fin 2)` to `Option (ULift (Fin 1))`, the identification of trace exchange
with the two chart traces, and compatibility of the diagonal source comparison
are substantial Lean transport steps, rather than direct applications of the
integral theorem. They are isolated in `sfP1CoordinateIntegrals`. Existing
`ordinaryFiniteP1_diagonal_unit` and `exists_ordinaryFiniteP1Adjunction` impose
Noetherian hypotheses and cannot directly prove the assigned arbitrary-affine
statement. The new generic triangle statement includes the pulled-back
rank-one, even-shift hypotheses needed for the second contraction; it does not
assert such a result for arbitrary kernels.

Edge cases checked mathematically: the zero coefficient ring, N = 1, the empty
base, identity proper morphism, and arbitrary integer even shifts. None of the new
statements assumes boundedness, constructibility or Noetherianity. A zero trace
cannot satisfy the integral hypotheses except in the zero category.

The inherited blueprint creation chain has a null ancestor; the new nodes record
that inherited situation and the exact current blueprint proof place explicitly.

## New nodes

`lem-sf-p1-coordinate-integrals`, module
`Sheaf.AlgebraicGeometry.SfP1CoordinateIntegrals`, isolates step 1 of the original
plan: trace/diagonal transport and both constant-object integrals.

`lem-sf-diagonal-kernel-integral-triangles`, module
`Sheaf.AlgebraicGeometry.SfDiagonalKernelIntegrals`, isolates steps 2--4: explicit
unit and counit and the two triangle calculations from normalized integrals.

All three inherit the item's chapter and unit. The existing node's proof,
proof_deps and proof_origin follow the written reduction. No statement,
definition or interface repair and hence no change record is needed.

`lem-sf-compactification-kernel-transport`, module
`Sheaf.AlgebraicGeometry.SfCompactificationKernelTransport`, isolates canonical
transport of an already supplied adjunction with specified counit and its
projection equation. It does not assert triangles or unit normalization. The
latter is proved in the assigned module using compactification right unitality.
The direct attempt at transport was retained in the scratchpad; Lean repeatedly
unfolded compactification and projection constructions and exceeded the limit.
This statement is the canonical transport step in the source, with its full
calculation recorded in the docstring, and leaves that step to a later worker.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
