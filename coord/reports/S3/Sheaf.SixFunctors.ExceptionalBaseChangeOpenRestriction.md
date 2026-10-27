## What changed

Constructed `openRestrictionGraphIso`, `openRestrictionCompactSupportIso`, and
`openRestrictionExceptionalIso` in
`Sheaf.SixFunctors.OpenRestrictionCompactSupport`. They are actual isomorphism data:
the graph construction compares the chosen compactification with the restriction
of the original one, proper/open interchange moves the open extension through the
proper image, and the open compositor finishes the support comparison. Conjugating
this comparison gives the exceptional comparison. No isomorphism is selected from
an unproved existence theorem.

Replaced the item's proof by a formal mate calculation from the compact-support
cube, the two mate/conjugation pasting identities, `mateEquiv_hcomp`, and the existing
identification of the open exchange mate with the inverse pullback-square iso.
The remaining pullback face is proved by pasting and cancellation. After evaluation
at K, functorial preservation and cancellation of isomorphisms finish the argument.
All original hypotheses and the conclusion are retained, including the absence of
quasi-compactness assumptions on the open immersions and on f and p.

## Proved and sorry left

Closed the original direct hole in
`AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_baseChange_of_open_restriction`
(node `lem-asd-exceptional-base-change-open-restriction`).

Added one direct hole:
`AlgebraicGeometry.Etale.openRestrictionCompactSupport_cube`
(node `lem-asd-open-restriction-compact-support-cube`, new module
`Sheaf.SixFunctors.OpenRestrictionCompactSupportCube`). This is exactly the support
cube equation before exceptional adjunction transposition, with the support
comparison explicitly constructed in the other new module. It assumes no hypothesis
about the exceptional base-change map and concludes no invertibility result.

Counts: one original hole closed; one lower hole added; zero holes remain in the
item module. This is a decomposition, with net hole reduction zero. The comparison
construction and all formal mate transposition and invertibility cancellation are
proved. The new definition module contains zero holes.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`;
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`;
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`;
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`;
- `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange`.

Their geometric work remains below the constructed support comparison or the
support-cube obligation, or is already imported by the public canonical-map API.
No whole node or module is claimed globally pruned. The updated item node delegates
the geometric equation to the support-cube node; its formal proof uses the existing
mate-pasting, open-exchange and exceptional-adjunction nodes. Existing upstream
declarations and all their signatures, attributes and public imports are untouched.

## Where the brief, the DAG or earlier work was wrong

The dependency interface for unbounded compact-support composition has been
strengthened since the original split: `SfGraphCompactSupportComposition` now
exposes the actual graph construction. The old direct import of
`LowerShriekComposition` alone exposed only existence without qc and could not be
used to form this cube equation. The new proof uses the specified graph data.

The upstream open exceptional-base-change theorem requires quasi-compactness of
both vertical morphisms; the composition compatibility API requires quasi-compact
open factors. Neither applies directly to this item's hypotheses. No such assumption
has been added. The remaining geometric cube coherence is stated explicitly rather
than inferred merely from isomorphic endpoints.

The source is the current blueprint's `prop-asd-smooth-base-change.proof.md`,
coherences (i) and (iii). The new lower theorem has a complete proof in words and
covers empty schemes, zero coefficients, identity opens, and unbounded complexes.
The unit record `sk-prop-sf-cbc` is unchanged.

## New nodes

`def-asd-open-restriction-comparisons`: attaches all three completely constructed
comparison isomorphisms in `Sheaf.SixFunctors.OpenRestrictionCompactSupport`.

`lem-asd-open-restriction-compact-support-cube`: the compact-support-only equation
from coherence (i). Its module has one public named theorem with proof `by sorry`.
The item proves the exceptional transposition and cancellation from this equation.
Both nodes record the LeanFinder, Loogle, LeanSearch, and Mathlib grep searches;
the searches found only generic mate and open-immersion facts, which do not state
this geometric cube. No existing interface was changed, so there is no change record.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
