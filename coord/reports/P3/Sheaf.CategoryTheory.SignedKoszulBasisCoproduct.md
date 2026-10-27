## What changed

Proved both remaining obligations in `Sheaf.CategoryTheory.SignedKoszulBasisCoproduct`.
The one-factor proof identifies the recursive tensor with its two-term factor by the
right unitor, checks the supported basis maps are isomorphisms, and constructs the
singleton or empty coproduct universal property.

The successor proof tensors the supplied tail coproducts with each head term and
reindexes tail subsets by `Fin.succ`, adjoining zero in head degree -1. Private proved
helpers check the cardinality, zero-membership, tail preimage, and inverse reindexing.
The actual recursive basis maps are identified with these normalized tensor legs.
`HomologicalComplex.mapBifunctorDesc` constructs the coproduct desc, and the total-tensor
and mapped-tail uniqueness properties prove uniqueness. Unsupported head degrees are
handled by the zero-object property.

Updated the base and successor DAG proof descriptions to record these arguments. The
existing induction proving `isColimit_ringedNegativeKoszulBasis_succ` is retained.
The module compiled cleanly through `lcompile.py` in 29.2 seconds.

## Proved and sorry left

Closed both original holes:

- `CategoryTheory.isColimit_ringedNegativeKoszulBasis_base`
  (`lem-cbc-signed-koszul-basis-coproduct-base`).
- `CategoryTheory.isColimit_ringedNegativeKoszulBasis_step`
  (`lem-cbc-signed-koszul-basis-coproduct-step`).

Two holes closed, zero holes added or split off. No `sorry` remains in the module.
All added private helpers are proved. No statement, definition, or public interface
was changed.

## No longer needed

None. The public import `Sheaf.CategoryTheory.SignedKoszulCompletionModel` is required
by the statements and definitions used in both proofs. Both proof nodes retain their
dependency on `def-cbc-signed-koszul-completion-model`, and the general induction retains
the base and successor dependencies. No modules or nodes are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The one-factor recursive object includes tensoring with the empty tensor O[0]; it is
identified with the two-term factor by the right unitor rather than by definitional
equality. This identification also fixes the precise basis normalization. The theorem
statements and the planned induction route are correct; both remaining steps can be
proved directly from the existing constructions and Mathlib universal-property APIs.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
