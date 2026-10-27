## What changed

The assigned theorem now has a complete proof from two strictly smaller statements:
the scalar/open quotient square on explicit K-flat tensor models, and the identity
between each finite component of the given strict comparison and that tensor model.
The assigned module constructs a flat-term K-flat representative, transports
completeness, substitutes the component identities, and transports the square to
the original object using naturality and cancellation. Its original signature is
byte-for-byte unchanged, and both original public imports remain.

The new model definitions are concrete composites of specified isomorphisms. The
ordinary tensor comparison is applied degreewise with isoOfComponents, avoiding
any new existence choice. No shared definition or source-library file is changed.

## Proved and sorry left

Closed: WeilConjectures.integralOpenReductionQuotientSquare (the sole original hole).

Added and left, each with its own source, full proof in words, module and DAG node:

- WeilConjectures.integralOpenTensorRepresentative.
- WeilConjectures.integralOpenTensorQuotientModel.

This is a decomposition: one upper hole is replaced by two proper subarguments.
It is not claimed as a net hole reduction or a proof free of sorry dependencies.
The isomorphism definitions and the completeness/naturality transport helpers
contain no holes. The latter helpers passed an isolated compile.
Validation: lcompile.py --all compiled all three delivered modules successfully
(exit 0). The generic naturality and completeness transport helpers also passed
an isolated compile. No profiling or tracing options remain in the delivered files.

## No longer needed

No existing module or declaration is withdrawn. Neither original public import is
removed. All original mathematical dependencies remain in the two new proof plans:
K-flat resolution is used directly by the parent; the strict comparison and scalar
calculus enter the finite-component identity; RingedOpenScalar and scalar calculus
enter the tensor quotient square. The new nodes make these two separate checks
explicit instead of leaving them as an implicit final gluing step.

The finite-component plan uses the first identity in each reduction presentation
and the prescribed finite tensor components. It does not need AugmentedPresentation,
the presentation quotient-arrow clause, or the unit/counit fields of r. These are
fields of retained shared interfaces, not declarations being withdrawn. A trial
private proof import of DerivedExactSquareComposition was removed when that
subargument was left as its own statement; its existing factorization lemma is
recorded in that statement's proof plan. A redundant MapDerivedCategoryMate import
was removed from the new representative module; the new quotient-model module
imports it publicly because its statement uses the exact derived square.

The unit sk-def-sf-operations has no realized statement or proof step bypassed by
this reduction. No existing node is pruned.

## Where the brief, the DAG or earlier work was wrong

No existing statement was changed or disputed. The old node's final step combines
finite-component identification with a scalar-model quotient calculation. These
are now separate explicit obligations. The attempted full finite-component proof
was not completed: conversions between the equivalent system-category expressions
and their functor instances prevented completion within a compiling short proof.
The delivered theorem records the exact finite-component statement, its source,
and the full localization-and-cancellation argument for the next worker.

No forced adaptations or change records are needed.

## New nodes

lem-sf-integral-open-tensor-representative records alpha_n = beta_n(Q), with no
quotient transition. beta is explicitly constructed from the degreewise ordinary
tensor comparison, the finite K-flat models, and exact-localization factors.

lem-sf-integral-open-tensor-quotient-model is the scalar/open quotient square for
this explicit beta on K-flat complexes. It has no reduction calculus, strict
comparison r, or completeness assumption. Its proof is the ordinary generator
calculation followed by normalized scalar localization. These are different
proper parts of the parent argument, not copies of its conclusion.

Searches: LeanFinder returned ordinary adic-completion transition lemmas;
LeanSearch returned algebraic naturality and generic quotient transformations;
Loogle for restrictScalars and extensionByZero returned no hits. Local rg found
the StrictModel, scalar calculus and RingedOpenScalar APIs, but not the specialized
identities. The finite-scalar ordinary quotient comparison uses a different
condensed finite-local-model setting; the scalar-extension quotient transition
uses a change of coefficient field, not an open extension. Blueprint searches for
open extension scalar restriction and reduction transition returned zero nodes.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
