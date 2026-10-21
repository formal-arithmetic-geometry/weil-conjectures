## What changed

Completed `CategoryTheory.signedDerivedInternalHom_exact` in
`Sheaf.CategoryTheory.SignedDerivedInternalHomExact`, preserving its full signature,
visibility, hypotheses, universes and both prescribed shift normalizations.

The private proof constructs the signed mapping-cocone comparison for ordinary
internal Hom, checks its inverse and all three triangle squares, converts the
existing coherent ordinary shift structure to the triangulated opposite convention,
and descends it through localization. K-injective representatives provide the
comparison isomorphism. The complete ordinary-to-derived source normalization
identifies the descended components at 1 and -1. The final argument transports
localized cone triangles to arbitrary distinguished triangles.

Added proof imports for the existing, completely proved cone-summand calculations
in `SignedDoubleHomCone` and the Mathlib mapping-cocone/opposite-triangle APIs.
The summand and linearity lemmas of the former are used; no bidual conclusion is assumed.
All new helpers are private and proved. The ordinary-Hom functor is presented by
explicit object/map fields to reduce elaboration overhead; its private naturality
proof is adapted. See `coord/changes/Q2-signed-derived-internal-hom-ordinary-dual.md` and
`coord/changes/Q2-signed-derived-internal-hom-negation.md`. The latter records
the unchanged negation homomorphism being exposed as a private abbreviation.
The node's proof, dependency list and proof origin now describe the actual argument.

Validation: the complete theorem compiled with no warnings and
`#print axioms CategoryTheory.signedDerivedInternalHom_exact` reported only
`propext`, `Classical.choice` and `Quot.sound`. Performance refactors then reused
existing linearity lemmas and binary biproducts, kept the Hom functor irreducible,
and replaced the expensive concrete shift-addition conversion by a generic formula.
The refactored construction portion compiled in 38.6 seconds; delivery preflight
checks the final complete packet, including every declaration's axiom dependencies.

## Proved and sorry left

Closed the original hole in `CategoryTheory.signedDerivedInternalHom_exact`
(node `lem-coef-signed-derived-internal-hom-exact`): 1 of 1 original holes.
No holes added, none split off, and no `sorry` remains in the item module.
No other Lean module is changed.

## No longer needed

No original proof dependency is removed, and no node or module is withdrawn.
All declared dependencies remain needed for the K-injective comparison, Hom-complex
calculus, normalized source shifts and derived cone-triangle presentation.
No original import is removed. The new proof uses the existing proved
`lem-sf-double-hom-cone-comparison` summand API and the stated route of the parent
unit; it does not bypass that unit or require a new bidual lemma.

## Where the brief, the DAG or earlier work was wrong

No disputed mathematical statement. The existing node's plan was correct but
left the localization and cone-sign glue to this item. This delivery supplies
that glue rather than repeating the earlier split. The generic shift-convention
conversion and explicit private functor fields keep the concrete sheaf proof
within the per-file compilation constraint. The public statement is unchanged.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
