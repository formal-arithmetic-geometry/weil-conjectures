## What changed

Reduced the four-stage compactification comparison to a finite witnessed coefficient
step and two higher single-refinement steps. The combining proof is
explicit: cancel one invertible comparison, compose with the second, and use functoriality;
the higher-stage comparison cocycle identifies that composite with the recorded rho.
The finite calculation retains both supplied origin witnesses and their tensor transport.

Extracted identitySquare, higherLaw and finiteLaw byte-identically to the new public
ProjectionCompactificationData module and re-exported them from the original module.
Added the local refinementLaw predicate. No target, original signature, definition body,
namespace or visibility changes. The data-interface extraction was checked byte-for-byte. Consumer census and extraction are recorded in
coord/changes/J2-projection-compactification-local-interface.md.

Returned-delivery repair (C-ea930, head ea930b07e44): the reviewed proof is retained.
The change record now reproduces the complete new definitions instead of referring to
the Lean module. Its current-source consumer census and the three byte-identical
extractions were checked again. The delivery script rebuilds this packet on the current
sheaf-dag tip and runs compilation and preflight before pushing.

## Proved and sorry left

Original textual holes: 1, WeilConjectures.FixProjectionCompactification.comparison.
Its body is replaced by a complete proof from named statements. The finite coefficient
part is now a named step whose complete proof plan uses the existing finite_descent.
Its direct Lean specialization exposed expensive hidden category-instance normalization;
the step remains a public theorem for that finite clause alone, not the full theorem.

New holes: 3, exactly the following public theorems, each with a source, full proof in
words and its own DAG node:

- WeilConjectures.FixProjectionCompactification.finiteCompactificationProjection
  (lem-sf-finite-projection-compactification-square).
- WeilConjectures.FixProjectionCompactification.integralRefinementProjection
  (lem-sf-integral-projection-refinement-square).
- WeilConjectures.FixProjectionCompactification.fieldRefinementProjection
  (lem-sf-field-projection-refinement-square).

This is a decomposition, not a sorry-free proof: one upper hole closed and three smaller
coefficient steps added. No sorry in data, private helpers or the combining proof. No axiom.
The original module has zero textual holes after the reduction. Its theorem signature
was compared byte-for-byte with the original and is identical.

The common-refinement cancellation helper is proved generically and used by the
higher-stage assembly. No sorry is hidden inside that assembly.

## No longer needed

Removed proof imports from the item module:

- Sheaf.Paper.PullbackTorAmplitude
- Sheaf.Paper.FiniteCoefficientTensorCtf
- Sheaf.Paper.ProEtaleConstructibleOrigin
- Sheaf.Paper.ExchangeProjectionSuppliedDomains
- Sheaf.Paper.RefinementComparisonIsomorphism
- Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization
- Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
- WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
- Sheaf.Paper.DerivedPullbackTensorIso
- Sheaf.SixFunctors.IntegralCompactificationSystemRealization
- Sheaf.SixFunctors.ProperOpenProjectionMate
- Sheaf.Paper.IntegralResidueTor
- Sheaf.SixFunctors.OpenTensorNormalization
- Sheaf.Paper.SfIntegralDirectImageConstructible
- Sheaf.Paper.IntegralOperationsPreserveConstructible
- Sheaf.Paper.CompletedOpenExchangeTransport
- Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients

These modules are no longer direct proof dependencies of this item. Several remain
needed transitively by existing finite_descent or by the new integral and coefficient
transport steps; no global deletion or withdrawal is claimed. All old public imports
remain public to preserve consumers. No module is withdrawn.

Original direct DAG proof dependencies replaced by the shorter route:

- lem-sf-pullback-tor-amplitude
- lem-sf-tensor-ctf
- lem-sf-proetale-constructible-origin
- def-exchange-projection
- def-sf-refinement-comparison-isomorphism
- lem-sf-proper-open-comparison-site-normalization
- lem-cbc-strict-tower-proper-open-calculus
- fix-prop-adjunctions
- lem-pur-derived-pullback-tensor-iso
- lem-sf-integral-compactification-system-realization
- lem-sf-proper-open-tensor-compatibility
- lem-coef-integral-residue-tor
- lem-sf-open-tensor-normalization
- lem-sf-integral-direct-image-constructible
- lem-pur-integral-operations-preserve-constructible
- lem-weil-pbc-finite-type-over-noetherian
- lem-weil-pbc-locally-noetherian-quasi-separated
- lem-cbc-completed-extension-zero-comparison
- fix-lem-exchanges
- def-weil-algebraically-closed-coefficients

The finite pullback, tensor, origin and normalization work is already incorporated in
the existing finite_descent statement, so repeating it here is unnecessary. Integral
bounds, system realization and coefficient transport are delegated to the two genuinely
local refinement steps. Their needed dependencies remain in those new nodes. Removed
obsolete top-level tool_uses approvals for the dependencies no longer used directly.

## Where the brief, the DAG or earlier work was wrong

The previous landing failed before merging because tools/batch_land.py expects a
reviewer's override for the delivered change record to have the basename
J2-projection-compactification-local-interface.change.md; the rejected override was
J2-projection-compactification-local-interface.md. The repository record remains at its
required coord/changes path, with the full replacement text now in this packet. Any
future reviewer override must use the .change.md alias. No launcher or landing tool
was changed.

The original nine-step plan does not mention the existing
Sheaf.SixFunctors.ProjectionRefinementDescent.finite_descent, which supplies precisely
the finite witnessed local refinement equation. It replaces repeating steps 1--5.
No false statement was found. The remark unit has no fixed proof steps, so the route
change bypasses no required unit step. The new local square is strictly narrower than
independence of arbitrary compactifications and the parent genuinely derives the latter
by two-square cancellation and the cocycle; it is not application of a renamed conclusion.

## New nodes

- lem-sf-finite-projection-compactification-square: only the finite coefficient clause
  of the four-stage statement. Its complete proof uses the existing finite_descent
  rho/tau normalization and elementary cancellation, with both supplied witnesses.
- def-sf-projection-single-refinement-law: the local predicate and extracted unchanged
  data interface. The node records every public definition hosted by its new module.
- lem-sf-integral-projection-refinement-square: realize the intrinsic system tensor/counit
  equation for one proper refinement in integral coordinates. It retains only the local
  refinement assertion, with uniform bounded constructible domains.
- lem-sf-field-projection-refinement-square: transport the integral local square through
  scalar localization, then a common finite coefficient field, retaining denominators
  and the scalar identity/cocycle. It has no arbitrary-pair comparison conclusion.

All follow the compactification-independence sentence of the latest blueprint
prop-sf-pf-coherence.proof.md. LeanSearch and LeanFinder returned unrelated affine and
profinite projection results; Mathlib grep found no match. Local search found finite_descent, which is the finite step's proof dependency. Existing ambient system refinement and integral expression-realization
lemmas do not state the operation-datum coordinate integral/field square. Blueprint
searches over all chapters found no matching local-step blueprint node.

All delivered dependency IDs exist. A read-only traversal of the combined current DAG
reported existing remote dependency cycles; a separate check found zero cycles
involving any delivered node. This broad graph check is not a claim that the current global DAG is acyclic.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
