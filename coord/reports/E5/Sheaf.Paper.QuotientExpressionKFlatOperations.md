## What changed

Repaired quotientExpressionKFlatOperations to require the actual quotient-input
identifications P, κ and transition compatibility hκ. The sole parent,
QuotientExpressionKFlatNormalization, already has these data and forwards them;
its public statement is unchanged. The change is recorded in
coord/changes/E5-quotient-expression-input-transitions.md and audited in the node's
statement_change.

The combining proof uses general categorical helpers to avoid unfolding concrete
coefficient witnesses; both backward transparency options are true. It handles
inputs by uniqueness of composite left adjoints,
then inducts on Generated using three local constructor lemmas. It identifies
derived adjuncts with the localized ordinary ones through unit_model, proves the
normalization Hom bijection, and derives both scalar-section formulas in
AdjointModel. Tensor comparison witnesses use the prescribed model, and operation
transition and adjunct equations come from the constructor lemmas.

Validation: lcompile.py --all compiled all five sandbox modules successfully,
including the adapted caller against the repaired theorem. The corrected main
module also passed a separate clean compile in 20.5 seconds. The caller's public
signature and public imports were compared verbatim with the current source.

## Proved and sorry left

Original item: one hole. The original statement is false and is not claimed
proved. The corrected quotientExpressionKFlatOperations has a complete combining
proof, with zero local holes. This is a statement repair and decomposition, not a
net proof of the old statement. Three new public holes remain:

- WeilConjectures.StrictQuotient.strictUnitOrdinaryAdjoint
  (lem-pur-strict-unit-ordinary-adjoint).
- WeilConjectures.StrictQuotient.strictTensorAdjointConstructor
  (lem-pur-strict-tensor-adjoint-constructor).
- WeilConjectures.StrictQuotient.strictPullbackAdjointConstructor
  (lem-pur-strict-pullback-adjoint-constructor).

Each is a local constructor step, independent of Generated and of the other
constructors. None restates the main result or its inductive normalization
conclusion. Their docstrings give the balanced tensor and inverse-image arguments
and edge cases. No definition contains a hole and no arbitrary witness is chosen
from a new existence hole.

## No longer needed

The main proof does not invoke the strict tower existence theorem, general
sheaf-ring derived coefficient adjunction theorem, or successive-derived-quotient
normalization theorem. These old proof dependencies are removed from this node:
lem-pur-quotient-expression-strict-kflat-towers,
lem-pur-sheaf-ring-derived-coefficient-adjunction,
lem-pur-quotient-operation-adjoint-factorizations,
lem-sfb-successive-derived-quotient-normalization, and
def-coef-normalized-dvr-tower (the last remains a statement dependency).
The operation-factorization theorem remains a source/dependency for the local
constructor lemmas. This does not assert those modules are globally unused, and
no upstream declaration or module is withdrawn.

Removed proof-only imports: Sheaf.Algebra.Homology.ChangeOfRingsKFlat,
Sheaf.Algebra.Homology.KFlatTotalTensorModel,
Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction,
Sheaf.Paper.KFlatScalarComparisonNormalization,
Sheaf.AlgebraicGeometry.ProEtaleConstantExact, and
Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap. The existing public imports are
retained for consumers.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old statement): Good is a property of individual levels and
cannot imply invertibility of arbitrary horizontal maps. The zero-transition
rank-one example in the change record disproves the old generalization. The
previous split discarded hκ although the parent already proves it. Restoring
that input compatibility follows the source's actual quotient transitions.
The DAG proof now records the real input-adjunction argument, constructor
induction, and localization-unit calculation instead of invoking a tower
existence theorem for unrelated chosen models.

## New nodes

lem-pur-strict-unit-ordinary-adjoint, in StrictUnitOrdinaryAdjoint.lean: the
rank-one unit's ordinary quotient adjunct is invertible, degreewise.

lem-pur-strict-tensor-adjoint-constructor, in StrictTensorAdjointConstructor.lean:
actual tensor transitions, invertibility propagation for ordinary adjuncts, and
the pinned derived tensor adjunct equation.

lem-pur-strict-pullback-adjoint-constructor, in
StrictPullbackAdjointConstructor.lean: horizontal naturality, finite evaluation
models, exact-derived computation, and the pinned scalar-change adjunct equation
for a single inverse-image constructor.

Change record: coord/changes/E5-quotient-expression-input-transitions.md.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
