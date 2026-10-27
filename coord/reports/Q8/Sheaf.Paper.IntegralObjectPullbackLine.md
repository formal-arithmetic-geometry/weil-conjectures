## What changed

Replaced the proof of `WeilConjectures.integralObjectPullbackLine` with an explicit
composition of representative, strict tower, Roos and regular augmentation
isomorphisms. Both original public imports and the theorem signature are unchanged.
The proof adds private imports of `LineUnboundedDerivedTensor`,
`ConstantScalarUnitQuasiIsomorphism`, and the new
`Sheaf.Paper.IntegralObjectPullbackQuotientBasis` module. A proved private helper
constructs an auxiliary finite-field datum whose characteristic differs from l;
it uses a larger prime and the algebraic closure of its prime field, independently
of X or W.

The new theorem provides finite quotient chain isomorphisms and their consecutive
transition equations. The upper proof constructs a natural isomorphism of strict
towers with `NatTrans.ofOpSequence` and `NatIso.ofComponents`, maps it through the
existing Roos functor and localization, and composes it with the existing inverse
regular scalar augmentation for the identity coefficient extension. No assumption
about completeness is added to L and no geometric finiteness assumption is used.

Proof-local fixed-size sheafification and site-smallness instances resolve ambiguous
universe parameters without changing any public interface.

The parent node's proof and dependencies now follow this argument. The new node
has its finite-level proof, source and exact Lean signature. Both modules compiled
in import order (6.5 s and 58.7 s under load); an unchanged proof with temporary
profiling compiled in 8.9 s, with 2.95 s of tactics and 2.33 s of type checking.
The profiling options were removed before delivery. Both added private proof
imports were checked with import_direction.py and do not close a cycle.

## Proved and sorry left

Closed the original textual hole in `WeilConjectures.integralObjectPullbackLine`
(node `lem-pur-integral-object-pullback-line`), from the named finite-level lemma.
There are zero textual holes left in the item module.

Added one hole: `WeilConjectures.integralObjectPullbackQuotientBasis`, node
`lem-pur-integral-object-pullback-quotient-basis`, in its own module. This is a
one-for-one decomposition, not a net proof. The residual obligation contains only
finite coefficient scalar extension and compatibility with quotient transitions.
It has no completed derived pullback, Roos construction, derived localization,
local freeness, or invertibility hypothesis. The upper proof supplies all those
remaining steps using existing declarations; the residual is strictly a part of
the original argument.

## No longer needed

No original Lean import was removed and no module is withdrawn. The existing
public imports are retained because the statement uses their definitions.

The original direct proof dependency `lem-pur-completed-line-complete`
(`Sheaf.Paper.CompletedLineComplete`) is not needed: the already proved
`regular_scalar_unit_quasi_isomorphism` gives exactly the regular Roos inverse,
without a detour through the legacy finite-field completeness predicate.
The direct dependency `lem-pe-roos-cone-calculus`
(`Sheaf.Algebra.Homology.RoosConeCalculus`) is also not needed: the existing
`integralOperationsRoosFunctor.mapIso` transports strict tower isomorphisms.
Neither module is claimed to be globally unused.

The direct dependency `lem-sfb-proetale-object-inverse-image-restriction` moves to
the residual finite quotient basis lemma, where its ordinary module comparison is
actually required. It is not pruned from the mathematical dependency graph.

## Where the brief, the DAG or earlier work was wrong

No target or existing statement was changed. The original plan is mathematically
appropriate, but the cited completeness theorem has an auxiliary finite-field
presentation and does not directly expose the strict regular augmentation inverse.
The existing identity-scalar augmentation theorem avoids that interface mismatch.

The current blueprint was read at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/sk-def-sp-tate-twist-locally-free.proof.md`,
Proof (3). Its compatible reductions of one integral basis are preserved. The unit
`sk-prop-an` has no realized nodes to bypass. Whole-blueprint searches for
"quotient basis" and "inverse image basis" found no duplicate of the finite
quotient compatibility lemma. The ancestor script returns None because the
original node's created.item is a module; its existing blueprint.from explicitly
names `det-def-sp-tate-twist-locally-free`, and the new node preserves that actual
source ancestor through the parent.

Edge cases of the residual statement: X and W may be empty; the regular object
can be zero on an empty site; no cancellation of a nonzero scalar is used. The
exponent starts at one. The coefficient projection can be nonflat, since the
residual construction is ordinary scalar extension. A single fixed slice basis
is used at every level, so transition compatibility is asserted before any
localization. No unit or augmentation normalization beyond the original object's
isomorphism conclusion is required.

## New nodes

`lem-pur-integral-object-pullback-quotient-basis`:
`Sheaf.Paper.IntegralObjectPullbackQuotientBasis`, declaration
`WeilConjectures.integralObjectPullbackQuotientBasis`. This isolates the compatible
finite quotient bases, before Roos, derived localization and completion. It is
needed by the actual tower isomorphism constructed in the item proof. Its source
is Stacks Tag 04J0 (localization of ringed sites), the normalized object inverse
image comparison, and the compatible integral basis argument in blueprint Proof
(3). Its proof dependency on the ringed-site localization result is a generic
module-sheaf tool; the maintainer may record the corresponding tool use if needed.
No existing declarations or interfaces change, so there is no change record and
no consumer adaptation.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
