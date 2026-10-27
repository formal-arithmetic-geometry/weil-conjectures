## What changed

Proved `WeilConjectures.coefficientLocalizationScalarUnit` in
`Sheaf.Paper.LocalizationScalarUnit`, preserving its statement verbatim. Added three
proved private helpers: comparison of the two specified scalar/pullback isomorphisms,
localization with the actual exceptional counit, and its specialization to the finite
coefficient rings. The latter two reuse the adopted source library's finite-stage
localization implementation, rather than the unfinished all-stage package.

The support-to-exceptional isomorphism is constructed using the natural Hom bijection.
Its inverse equations and counit equation are proved explicitly before transporting
the triangle. Scalar exactness follows from the triangulated-left-adjoint theorem,
since restriction of scalars is induced by an exact functor. The direct-image clauses
use the existing etale-origin theorem and naturality. The final equality follows from
`unit_mateEquiv`, after identifying the actual named comparison maps by conjugate and
iterated-mate identities.

Updated the node's proof, dependency list and proof origin to match this route. The
imports of `FiniteCompactSupportConstructibility` and
`ProEtaleFixedScalarRestrictionDirectImage` expose existing private, proved adapters;
their large public theorems are not invoked. Compiled the complete proof with `lcompile.py` (12.9 seconds); the sole style
warning was removed before delivery. No definition, source-library file,
public declaration signature or consumer is changed. No module is withdrawn.

## Proved and sorry left

Closed the original one hole in
`WeilConjectures.coefficientLocalizationScalarUnit`
(node `lem-coef-localization-scalar-unit`). Zero holes remain in the item module;
zero holes are added elsewhere and zero statements are split off. The three private
helpers are completely proved. Existing imported theorem holes remain assigned to
their existing nodes, as intended by stage 3.

## No longer needed

Removed these unused imports:

- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`.
- `Sheaf.Paper.SfLocalizationAllStages`.
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion`.
- `Sheaf.SecSmoothPurity.DirectImageScalarOperations`.

The open-subscheme Noetherian lemma
`lem-weil-pbc-noetherian-open-subscheme-noetherian` is unnecessary: U has its own
given finite-type structure morphism. The general ringed-topos pullback theorem
`lem-weil-pbc-ringed-topoi-derived-pullback` is unnecessary: the scalar functor is the
left adjoint of exact restriction. The intrinsic comparison definition
`def-sp-constant-scalar-pullback-comparison` is unnecessary: the fixed-module
comparison is directly identified with the published `finiteClosedScalarPullIso`.
Removed the latter two obsolete entries from this node's `tool_uses` list.

The finite localization argument and exact closed direct image remain needed, via
the adopted source implementation. Removing a direct import does not withdraw its
module: several are still imported by `FiniteClosedShriek` or other consumers. No
whole-library module is claimed to be globally pruned by this packet.

## Where the brief, the DAG or earlier work was wrong

The planned all-stage theorem packages an intrinsic constructible adjunction but
does not directly provide the literal fixed-module exceptional-counit equation in
this item's statement. The existing source finite-stage Hom equivalence supplies
the missing normalization, and the proof verifies it explicitly. An arbitrary
isomorphism between the two right-adjoint values would not suffice.

The original plan's general ringed-topos exactness theorem is stronger than needed.
Mathlib's exact-adjoint argument applies directly to the actual scalar functor.
The unit route is preserved: no closed-shriek coefficient-change theorem is used.
The unit record has no realized statement or step that this implementation bypasses.

The import cleanup is recorded in
`coord/changes/S5-localization-scalar-unit-imports.md`.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
