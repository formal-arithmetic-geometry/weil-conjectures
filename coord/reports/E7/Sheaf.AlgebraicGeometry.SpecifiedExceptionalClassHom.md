## What changed

Proved `AlgebraicGeometry.ProEtale.specifiedExceptionalEtale_boundedBelow` in
`Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`. Added the proof-only import
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded`.
The existing quasi-compact-target étale boundedness instance supplies the finite-amplitude
argument. The canonical lower-shriek comparison transports its adjunction to the literal
specified compactification, and `Adjunction.rightAdjointUniq` identifies the right adjoints.
Comparison direct image preserves the input lower bound; boundedness transfers along the
inverse component of the right-adjoint isomorphism.

The theorem signature and the Hom equivalence definition are unchanged. Updated the Step 4
implementation explanation and dependencies of `thm-sf-ambient-adjoint-class`; the other
clauses, the unit route, and their dependencies remain in place.

Validation: the item compiled successfully through `lcompile.py` (8.8 seconds, no warnings).
The added import is acyclic. The two additional node dependencies have no path back to the
item node. The proof does not identify the supplied compactification with the opaque
compactification extracted from `HasCompactification`.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.ProEtale.specifiedExceptionalEtale_boundedBelow`
(node `thm-sf-ambient-adjoint-class`). No holes remain in the item module. No holes were added
and no theorem was split off. The existing `specifiedExceptionalHomEquiv` definition now
uses the proved boundedness lemma.

## No longer needed

No imports, nodes, or modules are withdrawn. The specified-compactification boundedness
proof does not separately invoke the raw dimension, left-exactness, enough-injectives,
extension-by-zero, and total-derived-amplitude lemmas of Steps 3-4: the existing
`Etale.hasBoundedBelowUpperShriek` instance packages that argument. Those dependencies
remain relevant to the broader node and its reexported quantitative/existence interface,
so this delivery makes no claim that they are globally prunable. All three original public
imports retain the recorded interface; the sole added import supplies the canonical
unbounded compactification comparison used by the proof.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The DAG did not mention the already
available quasi-compact-target boundedness theorem as an implementation shortcut for this
specified-compactification obligation; Step 4 now records it. This uses the ordinary étale
adjunction and its canonical compactification comparison exactly as the unit requires.
Finite coefficients and compact target are already hypotheses. Empty schemes, the zero
complex, the zero coefficient ring, and arbitrary choices of the specified right adjoint
require no additional case split: object-property transport along the canonical isomorphism
covers them uniformly.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
