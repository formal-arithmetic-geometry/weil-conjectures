## What changed

Filled `SheafOfModules.exists_scalarDualEvaluationDescent` without changing its
statement or any existing public definition. All added helpers are private and
proved; local-surjectivity instances are confined to their proofs. The evaluation morphism is constructed explicitly, first extending
`x ↦ α(φ(x))` through the constant-module sheafification and ordinary scalar
extension, then restricting this morphism to each slice and extending in `φ`.
No object is selected from an unproved existence statement.

The key generator-extensionality argument works for arbitrary source modules:
locally lift a scalar-extension section through its sheafification unit, use
scalar-extension extensionality, then locally lift the constant-module factor through
its own sheafification unit. Naturality and separatedness descend generator
equality through these two covers. Applying this argument to internal-Hom
sections proves uniqueness and the equality test; the two generator formulas
prove contravariant naturality.

Removed four unused proof imports. The proof uses the existing Mathlib
module-sheafification adjunction and existing scalar-extension lifting API;
it reuses the proved scalar-extension API through the private proof import
`Sheaf.Paper.ScalarExtensionBinaryCoherence`. Updated the item's node's proof,
proof dependencies, proof origin and obsolete tool-use entries to follow this
direct universal-property argument.

Validation: the complete item compiled without errors or warnings in 57.6 seconds
through `lcompile.py`, within the 60-second single-file limit. The statement,
all five existing public definitions and their docstrings remain unchanged.

## Proved and sorry left

Closed the one original hole:
`SheafOfModules.exists_scalarDualEvaluationDescent`
(node `lem-sfb-scalar-dual-evaluation-descent`). This proves all three clauses:
unique existence with the formula after every restriction, contravariant
naturality for every linear map, and the generator equality criterion.

Holes closed: 1. Holes added: 0. Sorries left in the item: 0. No split-off
statements or new modules.

## No longer needed

Removed proof imports:

- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`;
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`;
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`;
- `Mathlib.CategoryTheory.Sites.CoverLifting`.

Removed this proof's dependencies on
`lem-pc-sites-module-sheafification-tensor`,
`lem-pc-sites-module-sheafification-bilinear-extension`,
`lem-sfb-localized-site-tensor-restriction`, and
`lem-weil-pbc-site-constant-restriction`. The first three obsolete tool-use
approvals were also removed, leaving the module-sheafification interface
approval. The construction directly uses the recorded scalar extension and
its adjunction; slice equality uses covering image sieves rather than an
isomorphism transporting tensor sheafification to slices. Thus no comparison
with a separately constructed raw constant-tensor presheaf is needed.

`def-pur-sheaf-tensor-product` is no longer a proof dependency, but remains a
statement dependency through the specified scalar realization. These are
item-level dependency removals: no source-library declaration or module is
withdrawn, and no claim is made that these nodes are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The original five-step plan is mathematically valid but takes an unnecessary
comparison-and-bilinear-extension detour. Two ordinary linear extensions,
followed by restriction into the existing internal Hom, give the same map.
The generator-extensionality argument is proved for arbitrary `M` and `V`, so
its use with `M = W*` in the naturality clause is justified. The existing
public statement and definitions are retained verbatim. The route still
supplies the scalar-dual evaluation ingredient of the constructible internal
Hom unit; no unit-level step is bypassed.

No active return or rework entry for this item was present on resumption.
The first preflight requested a change record for the proof elaboration commands;
`coord/changes/B6-scalar-dual-evaluation-proof-context.md` records them and the
consumer search. The private global instance was replaced by a proof-local `have`.
To reduce elaboration of scalar-extension terms, the final proof reuses the proved
`scalarExtensionLift`, `scalarExtensionLift_tmul`,
`scalarExtensionSection_naturality` and `scalarExtension_map_tmul` API.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
