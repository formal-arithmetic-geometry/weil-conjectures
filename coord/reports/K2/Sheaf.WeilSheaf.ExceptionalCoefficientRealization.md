## What changed

Replaced the body of `WeilConjectures.NativeCoefficientCohomology.exceptional_realization`
with an ordinary-adjunction argument. All three modules are checked individually in import order
through the remote compiler; the final check passed without warnings: LeftModels 16.8 s, RightMate 6.6 s,
and the parent 28.5 s (after restoring the interrupted proof and normalizing forget_obj). The target signature and existing public imports
are unchanged. No adopted source-library file was changed. A private endpoint equation and a local
irreducibility attribute for `IsoAlgebra.mapOfNatIso` prevent expensive quotient
unfolding during composition. This reduced the parent compile from over 60 seconds
to 29.1 seconds; the remaining unused-section-variable warning was then corrected.

`ExceptionalRealizationLeftModels` states the remaining geometric construction separately:
ordinary source coefficient realization, native ordinary-forgetting models, the normalized left
compact-support comparison, and its scalar-reference and Frobenius equations. It assumes
no new exceptional right comparison or right-action equation.

`ExceptionalRealizationRightMate` proves that the actual right mate is invertible.
The proof identifies the reference right mate by its counit, transports it through
coefficient equivalences, cancels the invertible coefficient mate, and reflects
invertibility. A private categorical calculation and pair-lift helper in the parent transpose the normalized
left Frobenius equation to prove equivariance of this actual right mate. Its point-unit
specialization then yields the required isomorphism of ordinary derived Frobenius pairs.
No fullness or faithfulness of derived native forgetting is asserted.

## Proved and sorry left

Original hole closed by decomposition:
`WeilConjectures.NativeCoefficientCohomology.exceptional_realization`.

One hole added and left:
`WeilConjectures.NativeCoefficientCohomology.exceptional_realization_left_models`
(node `lem-sf-exceptional-realization-left-models`).
Its module contains the statement, source, full construction in words, and matching node.
There is no sorry in a definition, private helper, or the right-mate theorem.

The fully proved new theorem is
`WeilConjectures.NativeCoefficientCohomology.exceptional_realization_right_mate_isIso`.
This is a decomposition of one original hole into one strictly earlier left-construction
hole, not a net reduction of the hole count. The right-adjunction transport and action
calculation are complete Lean proofs rather than restatements of the target.

## No longer needed

No existing module or node is withdrawn. No original public import is removed.
The parent's former realization, scalar-counit, and native-exceptional dependencies are
now used through the left construction or the proved right-mate argument; they remain
needed. No global pruning is claimed. The parent does not import unused realization
lemmas merely to reproduce the old dependency list.

## Where the brief, the DAG or earlier work was wrong

No target statement defect was found. The existing ordinary-realization family and native
forgetting package use the fixed PadicAlgCl and section-module presentation, whereas this
item uses the arbitrary Qbar and native geometric-fibre presentation. The missing scalar
and geometric transport must be normalized on the left; an arbitrary underlying right
isomorphism alone would not identify the prescribed inverse-exchange mate action.
The delivery exposes that normalization and proves the right comparison from it.

The remaining statement is strictly about the left construction. Its reference package
already has an independently supplied right comparison, but no new right-comparison
obligation is hidden in the statement. The reference equality quantifies over supplied
adjunctions because the package interface exposes its left comparison through that
argument; its construction chooses the same fixed left comparison for all of them.
Identity and empty models satisfy the same unit/counit equations, and smoothness is never
introduced.

## New nodes

- `lem-sf-exceptional-realization-left-models`: normalized ordinary realization and left
  comparison; one named theorem with sorry.
- `lem-sf-exceptional-realization-right-mate-isIso`: invertibility transported from the
  reference counit; fully proved.

The original node's proof, proof dependencies, and proof origin follow this reduction.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.WeilSheaf.ExceptionalCoefficientRealization": "a750e1a8a7d9bc9752c1ea734c90dd61fb940426", "Sheaf.WeilSheaf.ExceptionalRealizationLeftModels": "3b583c22bf1a8b5413fd777b51bdbb3a45e938d4", "Sheaf.WeilSheaf.ExceptionalRealizationRightMate": "19d69cc4a1a63d562b594a0cbb67c939ebcb68b7"}, "results": {"Sheaf.WeilSheaf.CoefficientCohomologyComparison": {"hash": "8851649984ed02b08dbdd34a874e0cde349aaece", "status": "OK"}}, "seconds": 43, "time": "2026-10-28T15:54:26+0800", "transitive": 0, "version": 1}
```

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
