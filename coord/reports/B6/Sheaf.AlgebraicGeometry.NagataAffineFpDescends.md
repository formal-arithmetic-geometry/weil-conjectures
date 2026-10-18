## What changed

Proved `AlgebraicGeometry.nagata_affine_fp_descends` in
`Sheaf.AlgebraicGeometry.NagataAffineFpDescends` without changing its signature.
Added the proof-only import `Mathlib.RingTheory.FinitePresentation`.
The first conjunct applies `Algebra.FinitePresentation.iff` to the stored stage quotient
presentation and uses `Submodule.fg_span (Set.finite_range E.relationMap)`.
The second composes `E.tensorPresentation` with `E.presentation.symm` and identifies its
underlying homomorphism with `E.beta` using `E.beta_eq`.
Updated the existing node's proof and proof origin to describe this implementation of
the current blueprint proof. The unit's approximation and descent route is preserved.

The single-file compile through `lcompile.py` passed without errors or warnings.
LeanFinder found the generic finite-presentation presentation results; Loogle found
`Algebra.FinitePresentation.iff` and `.equiv`. Source searches in Mathlib, WeilConjectures,
and Sheaf confirmed that the stored quotient presentations already supply all the data.
No new intermediate statements or assumptions are necessary. Empty variable/relation
families and zero rings are covered by the same finite-range argument and equivalences.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.nagata_affine_fp_descends`
(node `lemma-nagata-affine-fp-descends`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.

## No longer needed

None. No imports, declared proof dependencies, nodes, or modules were pruned.
`def-nagata-affine-fp-descent` remains the sole project proof dependency. The tensor
quotient identification is already a field of that datum, so it needs no separate proof
or import in this module.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error found. The DAG described the tensor quotient
identification as a calculation in this lemma; the existing descent structure already
retains that equivalence and the comparison equation, allowing their direct use here.
No definition, public import, statement, or consumer was changed.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
