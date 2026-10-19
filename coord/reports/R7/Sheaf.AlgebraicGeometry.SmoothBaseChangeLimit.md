## What changed

Proved `AlgebraicGeometry.smoothBaseChange_of_inverseLimit` in
`Sheaf.AlgebraicGeometry.SmoothBaseChangeLimit`, with the exact original signature.
Both private helpers are proved: `single_smooth` transports the
existing module-valued smooth theorem through the proved abelian/module
coefficient equivalence; `single_limit` explicitly constructs the four inverse diagrams, their
limit cones, constant coefficients and coherence, and applies the existing
`higherDirectImage_baseChange_of_limit` theorem. Negative degrees vanish.

The final proof extends the sheaf result to the given complex with the existing,
proved `DerivedCategory.Plus.isIso_app_of_forall_homology`. Its two lower-bound
conditions are proved here using derived direct-image vanishing and exact inverse
image. Algebraically closed stalks suffice by the proved field-extension stalk
isomorphism. The extra finite-stage qcqs assumptions remain in the signature;
the argument only needs qcqs for f. No definition, public declaration or target
statement is changed; no consumer adaptation or change record is needed.

Updated the item's node proof, proof dependencies and proof origin to this route.
The containing unit `sk-prop-sf-kunneth-ordinary` has empty realized statement and
step lists. The sheaf smooth-base-change/continuity route is preserved; the
complex comparison uses finite truncation induction instead of explicit spectral
sequence objects. The original docstring describes the source's spectral sequence
argument; an inline comment identifies the implementation's truncation route.

Searches: msearch LeanFinder for smooth base change along limits returned only
smooth/etale stability and ring-theoretic results; Loogle on Smooth and IsIso found
only normalization pullback; msearch grep found scheme/ring smooth stability.
Local searches found the proved `PlusDevissage` tool. The existing limit exchange
modules over Spec k have field-base and additional limit-qcqs hypotheses, so
cannot prove this arbitrary-scheme statement.

## Proved and sorry left

Closed 1 original hole: `AlgebraicGeometry.smoothBaseChange_of_inverseLimit`
(node `lem-kun-0f09`). Added 0 holes; split off 0. There are zero `sorry`s in the
delivered Lean file, including all private helpers. The proof uses the existing
public continuity theorem `AlgebraicGeometry.higherDirectImage_baseChange_of_limit`
(node `lem-kun-0ezt`), whose own proof remains a separate project item. This is a
proof from existing declarations, not a claim that its transitive axioms are
already closed. Single-file remote compilation succeeded; final dry-run results
are recorded by the delivery tool.

## No longer needed

Removed proof imports:
- `Sheaf.AlgebraicGeometry.DerivedCategories` (re-export and unused);
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`;
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`;
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`;
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Affine` (only the affine base-change API already available from the retained imports is needed);
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`;
- `Sheaf.AlgebraicGeometry.HypercohomologyConvergenceStatement`;
- `Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`;
- `Sheaf.AlgebraicGeometry.TruncationExchangeAbutment`;
- `Sheaf.AlgebraicGeometry.TruncationExchangeCouple`;
- `Sheaf.CategoryTheory.ExactCoupleMorphism`;
- `Sheaf.CategoryTheory.FiniteFiltrationInduction`;
- `Sheaf.Paper.KunBcMapOnCohomology`;
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem` (its theorem is
  used through the stronger proved single-object consequence in `.Derived`).

The proof no longer needs nodes `def-weil-pbc-hypercohomology-filtrations`,
`lem-weil-pbc-truncation-couple-morphism`, `lem-kun-bc-map-on-cohomology`,
`lem-sp-couple-morphism`, `lemma-weil-pbc-hypercohomology-convergence`,
`lemma-weil-pbc-exact-couple-abutment`, and
`lem-sp-finite-filtration-induction`. Their five obsolete top-level tool-use
approvals are removed without reordering or adding approvals. The node retains
`sbc-thm-smooth-base-change`, affine permanence, continuity and the cohomology
isomorphism criterion. No claim is made that these removed modules are globally
unreachable: other parents may still use them.

## Where the brief, the DAG or earlier work was wrong

No mathematical or signature defect found. The explicit spectral-sequence plan
was longer than necessary because the source library already proves the generic
bounded-below truncation comparison. Its reuse avoids all of the exact-couple
interfaces, some of whose source declarations are currently commented out after
an upstream sync. The degreewise continuity lemma has the correct orientation:
its direct-image leg is the constant f, and its coefficients are constant F on X.

Edge cases: nonempty directed I ensures both constant cones and the constant
coefficient cocone have the required universal properties. The construction
constructs the pullback limit directly from its universal property and makes no quasi-compactness assumption on S.
For a zero sheaf or empty scheme the same additive arguments apply. Negative
cohomology is handled separately before the nonnegative continuity application.
Positive annihilators are transported individually; no uniform exponent or
assumption about the characteristic of S is introduced.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
