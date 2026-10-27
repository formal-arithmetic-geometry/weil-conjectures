## What changed

Decomposed `AlgebraicGeometry.ProEtale.SpTensorTranspose.tensor_transpose_evaluation`
into the two independent arguments in the blueprint: naturality of the actual tower
projection/counit map and its transpose, and evaluation of the specified maps at one
positive coefficient level. The main module derives naturality of the oriented gamma
map by tensor bifunctoriality and transpose naturality, then combines all clauses.
Its theorem statement is unchanged.

Moved the existing six source/word definitions, with unchanged names, types and bodies,
to `Sheaf.Paper.TowerTensorTransposeWords`, publicly reexported by the item. This avoids
a cycle when the smaller finite-evaluation theorem uses those words. The two new theorem
imports are private. No adopted source-library file or target statement changes.

The change record is `coord/changes/H9-tensor-transpose-evaluation-words.md`.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.SpTensorTranspose.tensor_transpose_evaluation` is replaced by
a complete proof from the two smaller theorems. Its gamma-naturality clause is proved by
mapping equality of product arrows through the tensor bifunctor and composing with the
transpose-naturality equation.

This is a decomposition, not a net proof: one hole closed, two holes added, net -1.
The packet leaves exactly these two named theorem holes:

- `AlgebraicGeometry.ProEtale.SpTensorTranspose.tensor_transpose_tower_naturality`,
  node `lem-sp-tensor-transpose-tower-naturality`.
- `AlgebraicGeometry.ProEtale.SpTensorTranspose.tensor_transpose_finite_evaluation`,
  node `lem-sp-tensor-transpose-finite-evaluation`.

Every remaining hole is exactly `:= by sorry`, in its own new module, with the source
and full proof in words. There are no holes in definitions.

## No longer needed

Removed the item's explicit private proof import
`Sheaf.Paper.PurityDiagonalDualizingObject`: the finite orientation is
supplied as a hypothesis; this item does not construct it. Its mathematical statement
dependency is retained. All original public imports remain publicly available through
the shared words module.

No old mathematical node or module is withdrawn or globally pruned. The original
proof dependencies remain needed by the two smaller lemmas. The parent node now records
those two direct proof dependencies; the smaller nodes record the original underlying
projection, tower evaluation and adjunction dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The supplied definitions give the planned
ordinary tower maps, and the argument uses them without detecting equality through
finite evaluation. The finite natural-index convention remains exponent n+1, including
n=0. The two smaller statements were checked on zero inputs and maps and on d=0;
all arguments are categorical equations and require no nonzero-object assumption.

The attempted direct naturality proof exposed lengthy realization, tensor-structure
and full-subcategory elaboration calculations. Mathlib supplies the abstract Hom
naturality equations, but not the geometric tower evaluation theorem. The decomposition
retains these calculations explicitly as the two next items rather than replacing an
actual map by an arbitrary isomorphism or assuming faithfulness of evaluation.

## New nodes

`def-sp-tensor-transpose-evaluation-words` records the six unchanged constructions moved
to the shared definitions module. It introduces no second mathematical definition.

`lem-sp-tensor-transpose-tower-naturality` states only the naturality of the
projection/counit map and its transpose. It requires neither a chosen orientation nor
finite coordinates nor smoothness. Its proof uses projection, symmetry and unitor
naturality and the actual compact-support Hom equivalence.

`lem-sp-tensor-transpose-finite-evaluation` states only the per-level evaluation
conclusions, with all the normalized unit, tensor, pullback and orientation data. It
omits the three naturality claims. Its source proof evaluates the specified composite,
then the unit transpose, then tensors the orientation. Both lemma nodes are strictly
smaller than the item, and the main module supplies the tensor-composition argument.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
