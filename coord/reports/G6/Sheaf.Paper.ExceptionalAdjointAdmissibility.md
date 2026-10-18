## What changed

Proved `WeilConjectures.exceptionalCoefficientRestriction_isRightAdjoint` by specializing
`pbcDerivedScalarAdjunction` to the sheafified map induced by the actual ring map
`φ.ulift`. Added its module `Sheaf.Paper.BoundedConstructibleTower` as a proof-only import.
All existing signatures, definitions, and public imports are unchanged.

## Proved and sorry left

Closed 1 of the original 2 holes:
`WeilConjectures.exceptionalCoefficientRestriction_isRightAdjoint`.
Its proof uses the existing declared derived scalar adjunction; that declaration's
own proof remains work in its existing module, not a new hole in this delivery.

The original hole `WeilConjectures.exceptionalFiniteSupportExtensionMap_isIso` remains
unchanged (node `def-weil-exceptional-adjoint-admissibility`). No holes added and no
split-offs. The item now contains exactly 1 `sorry`.

Validation: the retained adjunction proof compiled through `lcompile.py` in 6.5 seconds.

## No longer needed

None. The existing public imports support the definitions and their signatures.
No declared proof dependencies were supplied by the item's definition node.
The remaining support comparison still needs the projection formula argument, so
none of that argument's dependencies are declared pruned.

## Where the brief, the DAG or earlier work was wrong

The item node is a definition with empty `proof` and `proof_deps`, although its module
also contains two auxiliary existence/isomorphism theorems. Consequently there is no
numbered DAG proof for the support comparison to translate directly. The scalar
adjunction theorem already declared in `BoundedConstructibleTower` suffices for the
first hole. The invertible restriction square alone does not make its scalar mate
invertible; the second hole requires the exactness/coproduct/free-resolution argument
in its docstring. Existing étale finite-constant projection lemmas inspected impose
a different site, boundedness, or geometric hypotheses, so they cannot be applied
directly to this arbitrary ambient pro-étale input.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
