## What changed

Completed `SheafOfModules.basedSheafTensorEvaluation` without changing its signature or
`basedTensorProductSections`. All helpers added to the item are private and proved.
The two reused helpers in
`Sheaf.Paper.FiniteFreeScalarExtension` remain private and are accessed by `import all`.

The proof evaluates the given basis isomorphism and uses `TensorProduct.piScalarRight`
to construct mutually inverse sectionwise coordinates. Naturality of these coordinates
identifies the tensor presheaf with the finite product of the input sheaf, so it is already
a sheaf. Its sheafification unit is therefore an isomorphism. Composing coordinates with
the inverse unit constructs the required natural isomorphism; the basis hypothesis `he`
identifies its inverse with the specified finite sum. The unit supplies theta, both
naturality assertions and its uniqueness on pure tensors. Applying theta in every degree
constructs the unbounded complex isomorphism.

Restriction preserves finite limits and colimits through the forgetful functors to
abelian sheaves. Faithfulness and the ShortComplex exactness API prove the image/kernel
criterion, including pairs whose zero composite was not assumed. Finite powers preserve
finite limits and colimits via the finite biproduct comparison between lim and colim.
Reflection by restriction transfers that exactness to tensor extension. For ordinary
modules, the supplied basis gives freeness and hence flatness, so Mathlib supplies
finite-limit preservation directly; the extension/restriction adjunction supplies
additivity and colimit preservation.

Added private proof imports of the proved forgetful-sheafification instance module,
Mathlib's ModuleCat.Descent, TensorProduct.Pi, Adjunction.Additive and
Preadditive.LeftExact. Added a proof-only import of
`Sheaf.Paper.FiniteFreeScalarExtension` and reused its existing `sectionProduct_ext`
and `changeMap_tmul` through `import all`, deleting the duplicate private declarations
from this item. The source module is unchanged. Updated the
item node's proof, proof dependencies and proof origin to match these arguments.
No new node is introduced.
The item's public interface, all definition data, and all unit statements and steps are unchanged.
No declaration visibility or source-module interface changes; consumers need no edits.
The added local elaboration commands are documented in
`coord/changes/based-tensor-evaluation-proof-local-commands.md`; downstream inspection
found no external Lean consumer requiring adaptation.

## Proved and sorry left

Closed the one original hole: `SheafOfModules.basedSheafTensorEvaluation`
(node `lem-pur-based-sheaf-tensor-evaluation`). Zero holes remain in the item; zero
holes were added elsewhere, and no theorem was split off. This is a proof, not a
redistribution of the original hole.

The rank-zero case is included by the finite tensor/product equivalences and finite
biproduct comparison. No nonzero-ring, positive-rank, boundedness or additional flatness
hypothesis was introduced. The main theorem signature is byte-for-byte unchanged.

## No longer needed

Removed the original private import
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.

The proof does not need `lem-weil-pbc-module-sheaves-colimits-forgetful` as a theorem:
Mathlib's evaluation and the proved forgetful instances directly supply the needed
interfaces. Removed that proof dependency and its obsolete tool-use entry. It also
does not need `lem-sfb-kernel-cokernel-finite-exactness`: preservation is transported
through composites and natural isomorphisms instead of reconstructed from kernels and
cokernels. Neither corresponding module is withdrawn, and no source-library declaration
was removed.

Removed the duplicate private `SheafOfModules.sectionProduct_ext` and
`SheafOfModules.changeMap_tmul` from the item. The proof now imports
`Sheaf.Paper.FiniteFreeScalarExtension` and uses these already proved lemmas there.
Its complete scalar-extension theorem is not used: the item needs the already-sheaf
comparison and explicit inverse formulas. `Sheaf.Paper.FinitePowerComplex` and
`Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction` are not directly used.
No module is withdrawn.
All original public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The original plan's one-object-site specialization is unnecessary: the ordinary-module
clause follows directly from finite freeness, flatness and the Mathlib adjunction. The
finite-power exactness step is shorter using the existing finite-biproduct colim/lim
comparison. The node now records these routes.

The sandbox contained a substantial unfinished proof from earlier work. Its initial
compile exposed missing visibility of the private forgetful-instance import, a dependent
rewrite through image subobjects, and elaboration issues in the coordinate and complex
comparisons. These were repaired in the saved proof. Broad rewrites through finite products
were replaced by explicit congruence and associativity arguments; private coordinate
constructions are irreducible. The chain equation explicitly fixes the sectionwise
morphisms and site universe. Explicit reflection constructors avoid broad instance search.
The returned proof had compiled in 35.3 seconds. The final repair compiled
`BasedTensorEvaluation` cleanly in 47.4 seconds, exit code 0, with no warnings or holes.
The unchanged source module is reused from the published build.
The local unused-variable linter setting preserves the original statement binder names.
Compile-service failures were retried according to the brief.


The return at `6e723177f0e` correctly identified the two duplicate private helper
statements. Their binders and meanings agree. They could not be reused by import alone
because the originals were private. Lean's existing `import all` mechanism permits reuse
of the original private names without modifying their source module. Both copies are
removed. The original-source visibility attempt hit the compile timeout, so no source
refactor is retained: the packet contains only the item, its route node, the existing
proof-local command change record, and this report.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
