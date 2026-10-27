## What changed

Replaced the single proof hole in `lisseLattice_constant_reductions` by a proof of
compatible global bases, their integral limit basis, and its ordinary rationalization.
The theorem's signature is byte-for-byte unchanged. All added helpers are private and
proved. The returned duplicate helper declarations are removed. Proof-only `import all`
imports reuse `lift_iso_square_zero`, `scalarCokernel_zero`, and `scalar_square_zero`
from `Sheaf.SixFunctors.IntegralLisseTowerLocalBases`, and `free_isFiniteLocallyFree`
from `Sheaf.SixFunctors.IntegralLisseTowerEffective`. These are existing proved private
lemmas; neither module’s main theorem is applied. Their files are unchanged.

The global lifting step uses the already-proved sectionwise coefficient quotient
API. It lifts finitely many generator images over the terminal object X and restricts
them to every object. Thus it does not assume that arbitrary sheaf epimorphisms are
surjective on global sections. Both N and the standard free sheaf are integral lisse,
so the same module completeness theorem identifies both limit cones. The scalar
extension is constructed sectionwise from finite free coordinates, then sheafified;
its pure tensor formula is proved using unit naturality and the adjunction triangle.
The proof includes rank zero and the empty scheme without additional assumptions.

Updated the existing node's proof, proof dependencies and proof origin to this route.
No public statement, definition, source-library declaration or unit route changed.
Preflight requested a record of the added module commands; it is included at
`coord/changes/lisse-lattice-constant-reductions-proof-commands.md`. The attributes
are local, helpers private, and no consumer adaptation is needed. The source-only
consumer scan reports zero downstream modules; the future parent DAG attachment
is retained.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.lisseLattice_constant_reductions`.
Original holes: 1. Holes closed: 1. Holes added: 0. Holes remaining in the item: 0.
No split-off statements or other modules with holes are delivered.

The repaired full module was recompiled on the project server on 2026-10-23
(exit code 0, 42 seconds). The four returned duplicate declarations are absent; their
calls resolve through the two existing helper modules. An explicit `#print axioms` check
reported exactly `propext`, `Classical.choice` and `Quot.sound`; the diagnostic command
was then removed. The public theorem signature was compared verbatim with the live
source and is unchanged. All Lean lines meet the 100-character limit.

## No longer needed

The proof no longer needs these direct proof dependencies and imports:

- `Sheaf.Paper.TotallyDisconnectedCoefficientRealization`, node
  `lem-sfb-totally-disconnected-coefficient-realization`: the continuous coefficient
  model already has a proved sectionwise quotient API; no new GL-valued continuous
  matrix realization is required.
- `Sheaf.SixFunctors.IntegralSquareZeroMatrixLift`, node
  `lem-sfb-integral-square-zero-matrix-lift`: the square-zero inverse correction is
  proved directly for the sheaf-module endomorphisms.
- `Sheaf.SixFunctors.IntegralLisseCoefficientLimit`, node
  `lem-sfb-integral-lisse-coefficient-limit`: module completeness applies directly to
  the finite free sheaf. This node remains a transitive dependency of the proved
  completeness theorem; no claim is made that it is globally unnecessary.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: ordinary extension
  of scalars only needs the sectionwise tensor/sheafification interface.

Removed the obsolete matrix-lift and coefficient-limit top-level `tool_uses` entries,
retaining the module-completeness entry in its original order. The actual cokernel
transition quotient and coefficient quotient nodes are used explicitly. No module
is withdrawn and no source-library declaration is removed. The four duplicate helpers
listed in the return are pruned from this module; their original declarations remain
in their existing modules and are used directly. The two helper modules are retained
as proof imports and are not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The return at head `77f2b9e5136` correctly identified four duplicate private helper
statements: `free_finiteLocallyFree`, `lift_iso_square_zero`, `scalarCokernel_zero`,
and `scalar_square_zero`. The retained repair removes all four and calls the existing
lemmas instead; the finite-free call uses the existing name `free_isFiniteLocallyFree`.
The DAG now records reuse of these two helper modules, and the proof-command change
record describes the actual imports. The unused private universe parameter was removed.

No false statement or interface repair was necessary. The previous DAG proof plan
was longer than needed: global finite-generator lifting and a categorical square-zero
calculation replace continuous GL matrices, and module completeness applied twice
replaces the separate coefficient-limit/finite-product argument.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
