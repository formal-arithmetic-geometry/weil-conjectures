## What changed

Repaired the return for head `02d45607e0e`: removed the duplicate private
`CategoryTheory.limitModelPointIso_hom_π`. Its only consumer, the naturality proof
of `limitModelIso`, now uses Mathlib's
`IsLimit.conePointUniqueUpToIso_hom_comp` directly. The duplicate statements in
`StrictRoosShiftLocalization` and `InjectiveTowerRoosShifts` are private and cannot
be imported; their underlying Mathlib theorem supplies precisely the needed rule.
No renamed wrapper or new theorem replaces the removed declaration. Compared the
retained proof against current shared source; the public statement is unchanged.

Proved `CategoryTheory.normalizedRoosShiftComparison` with its existing signature.
The proof imports `Sheaf.CategoryTheory.StrictRoosShiftLocalization`, uses the
signed chain and localized inclusion equations, and transports the coherent shift
along the supplied natural isomorphism using Mathlib's `Functor.CommShift.ofIso`.
Normalization then identifies the unit shift square on all complexes.

Private proved helpers construct the natural isomorphism between the degreewise
ordinary-limit complex and the ordinary limit of complexes. The existing
`ringedStrictTowerHomotopyLimitIndependentCoefficients` supplies a universal pair
whose unit is invertible on all K-injectives. Uniqueness of right derived functors
transfers that computation to the supplied pair. The resolution isomorphisms are
explicit composites of the unit with the inverse image of the resolution map.
Naturality and cancellation give the final equation for every K-injective
resolution, without an injective-term assumption or a choice of resolution.

The generic private assembly and unit-transfer helpers avoid expanding concrete
sheaf and cone constructions during elaboration. The module compiles with zero
`sorry` tokens; the public theorem signature was compared verbatim with the source.

Updated the existing node's proof, proof dependencies and proof origin to follow
this argument. No public signature, definition, or public import changes. The static scanner
requires a record for the private section-variable and elaboration-option commands:
`coord/changes/M9-normalized-roos-shift-private-context.md`. The sole current consumer
is `Sheaf.Paper.IntegralImmersionPullbackNormalization` (unclaimed); it needs no edit.
The original delivery compile passed before this record was requested by preflight.
The generic assembly now uses the supplied abelian instance directly. The proved
private `normalizedRoosUnitIso` handles the concrete unit computation, with explicit
universes in its final use. The final theorem scopes stricter type transparency
and directly applies the assembly. The full proof compiled on the project server
in 48.3 seconds with profiling; the final file removes that diagnostic option.

Searches: LeanFinder found generic derived-category shift instances; Loogle found
`Functor.CommShift.ofIso` and its component and compatibility lemmas; the Mathlib
text search found right-derived uniqueness and derivability criteria. Repository
searches found the existing signed localization theorem and the total derived-limit
unit computation, used here rather than restating them.

## Proved and sorry left

Closed one hole: `CategoryTheory.normalizedRoosShiftComparison`
(`lem-a1-normalized-roos-shift-comparison`). Zero holes remain in the item;
zero holes added and zero statements split off. All private helpers are proved.
The imported `CategoryTheory.strictRoosShiftLocalization` remains a stated
proof dependency; this delivery does not claim to prove that separate theorem.

## No longer needed

Removed the redundant private projection lemma
`CategoryTheory.limitModelPointIso_hom_π`; Mathlib already supplies its content.
No existing public import is removed. The original proof import of
`RingedStrictTowerHomotopyLimitIndependentCoefficients` is retained and used.
The proof does not require `lem-a1-total-limit-shift-resolution-change` or its
module `Sheaf.CategoryTheory.TotalLimitShiftResolutionChange`: every-resolution
compatibility follows from normalization and naturality of the transported shift.
It does not require `lem-pur-injective-tower-roos-shifts` or its module
`Sheaf.CategoryTheory.InjectiveTowerRoosShifts`: arbitrary K-injectives suffice.
It uses the supplied normalized comparison directly, so it does not apply the
existence theorem `lem-weil-strict-roos-comparison`; its module remains publicly
imported exactly as before. Removed the two obsolete top-level tool-use approvals
for that existence theorem and the injective-term resolution theorem from this
node. No module is withdrawn; no source-library declaration is removed.
The affine-line unit's statement and proof route remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The returned packet duplicated a private projection lemma already present in two
library modules. This retry uses the existing generic Mathlib theorem directly.

The DAG's injective-term resolution and comparison-formula detour is unnecessary
for this Lean statement: the supplied normalization holds on every complex, so
conjugation followed by unit naturality proves the requested square directly.
The theorem's existing docstring records the older valid argument; its statement
is preserved. The ordinary-limit models in the two supplied interfaces are
naturally isomorphic rather than definitionally identical; this is proved
explicitly in the private helpers.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
