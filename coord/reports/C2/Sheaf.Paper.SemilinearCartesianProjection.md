## What changed

Replaced the hole in `Sheaf.Paper.SemilinearCartesianProjection` by a complete Lean
assembly of the projection formula. The statement and every public import stay
unchanged. Added private proof imports of `SystemSingleDerivedEvaluation`,
`SystemDerivedEvaluation`, `SystemEvaluationTopos`, and the new below-level
factorization module.

The actual sequence-site evaluations jointly detect isomorphisms: the proof derives
their comparison with strict evaluations and reflects along the derived equivalence.
For any given L and adjunction, upper-level vanishing is proved by transporting
`systemSingleDerivedAbove` through `Adjunction.leftAdjointUniq` and that equivalence.
Closed tensor preserves zero because its tensorRight functor is a left adjoint.
Below the source vertex, the new factorization identifies the evaluated arrow with
an isomorphism followed by tensor of the identity and the actual reduction. Only
here is cartesianness used, to make that reduction invertible.

This is a decomposition with a proved assembly, not a net reduction in holes.
Both delivered modules compile individually in under 11 seconds on the server.
No existing module besides the item, definition, instance, statement, or public
interface was changed.

## Proved and sorry left

Closed the one original hole, by declaration name:
`WeilConjectures.SemilinearSections.semilinearCartesianProjection`
(node `lem-coef-semilinear-cartesian-projection`). Its entire proof is now Lean.
The private lemmas `evaluation_detects` and `singleton_above` are fully proved.

Added one hole:
`WeilConjectures.SemilinearSections.semilinearProjectionBelowFactorization`
(node `lem-coef-semilinear-projection-below-factorization`), the whole proof of one
public theorem in its own new module. Thus the item has zero remaining sorries;
one original hole is closed and one strictly smaller computation is split off.
Net hole change: zero.

The remaining theorem asserts a morphism factorization at one q ≤ n for arbitrary
M. It assumes neither cartesianness nor invertibility of any reduction, and proves
neither upper-level vanishing nor joint detection nor invertibility of the system
projection. Those parts of the original argument are implemented in the item.
It is not the original isomorphism claim under a new name or repackaged hypothesis.
The edge cases q = n, n = 0, zero rings, zero P or M, and the empty site all obey
its tensor-unit, zero and local-generator formulas. Its existential isomorphism is
used only inside a proof of IsIso; no definition chooses arbitrary data from it.

## No longer needed

No original Lean import was removed, and no module is claimed globally pruned.
The item directly uses the new factorization, system-derived evaluation,
ringed-sequence equivalence, singleton derived extension/evaluation and the
additivity facts in SystemEvaluationTopos.

Original item dependencies `lem-pur-derived-change-of-rings`,
`lem-pur-system-evaluation-kflat`, `lem-pur-system-singleton-scalar-extension` and
`lem-weil-pbc-site-derived-tensor-descent` are now dependencies of the smaller
factorization rather than direct steps of the item. They remain needed there.
`lem-weil-pbc-adjunction-of-natural-bijection` is not used: existing normalized
adjunctions and Mathlib's `Adjunction.leftAdjointUniq` suffice. No replacement
adjunction is constructed from natural Hom bijections.

## Where the brief, the DAG or earlier work was wrong

The listed lower statements provide singleton evaluation, transposes, K-flat
representatives and tensor descent, but none states the below-level compatibility
of the unit-defined projection with tensor of the reduction. The new theorem
isolates exactly that missing calculation. Searching found no shorter theorem
closing it; generic projection theorems for other categories do not normalize
this map. `SystemTensorReductionFormula` assumes full semilinear Data, including
the cartesian Hom comparison that consumes this item, so using it here would be
circular. No mathematical statement or unit route is disputed or changed.

## New nodes

`lem-coef-semilinear-projection-below-factorization`, in
`Sheaf.Paper.SemilinearProjectionBelowFactorization`, is the scalar/tensor
reassociation and pure-tensor equality in step 2 of the old plan. Its statement
specifies both endpoints and the actual morphism equation for arbitrary M. The
source and full representative proof are recorded in its docstring and node.
Blueprint searches for singleton and cartesian projection found no matching
blueprint statement. There are no change records because no existing public
interface changed.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
