## What changed

Proved the native direct-evaluation coefficient transition using the ordinary section
square and naturality of unit-normalized derived squares. The ordinary evaluation is
moduleEvalP followed by compactSupportDirectModel. Its section formula gives the ordinary
transition square directly. The localized adjunction-mate normalization gives the native
evaluation's derived unit equation. Comparing K-injective resolution equations identifies
the scalar comparison with the inverse of the specified sfDerivedImageRestriction.
The existing normalized_transition theorem then gives the desired equation.

The assigned module and its DAG node changed. The ordinary section square and scalar
normalization steps live in the new modules
Sheaf.Paper.CompactSupportOrdinaryDirectTransition,
Sheaf.Paper.CompactSupportOrdinaryDirectEvaluationSections,
Sheaf.Paper.CompactSupportOrdinaryDirectLeftSections,
Sheaf.Paper.CompactSupportOrdinaryDirectRightSections,
Sheaf.Paper.CompactSupportScalarDirectNormalization, and
Sheaf.Paper.CompactSupportRawDirectNormalization.
The ordinary square uses separate proved left and right section formulas. This splits
the elaboration work across files after profiling showed repeated coefficient-category
comparisons inside the combined proof. Local irreducibility of the sequence-functor
constructors prevents expansion of their ring actions during these comparisons.
The new modules keep the section calculations and K-injective resolution calculation
separate after local abstraction of the sheafification and derived-functor constructions. Original public
declaration signatures, definitions, and public imports remain unchanged. The remaining
helpers are private and proved. Updated the nodes to describe the proof actually used.

## Proved and sorry left

Closed: WeilConjectures.compactSupportNativeDirectTransition (the module's one original hole).
Also proved: WeilConjectures.compactSupportOrdinaryDirectEvaluation_sections,
WeilConjectures.compactSupportOrdinaryDirectTransition,
WeilConjectures.compactSupportOrdinaryDirectLeftSections,
WeilConjectures.compactSupportOrdinaryDirectRightSections,
WeilConjectures.compactSupportScalarDirectNormalization, and
WeilConjectures.compactSupportRawDirectNormalization.
Added holes: none. Remaining holes in the delivery: none. This is a proof, not a decomposition.
Validation: all seven delivery modules compile against the delivered dependencies.
The extracted unit-normalization module takes 11.0 s and the final transition takes
48.5 s with serialization; the other files take 11.0–36.2 s. Every file is below 60 s.

## No longer needed

The planned dependency lem-pur-system-pushforward-restriction-transition, implemented in
Sheaf.Paper.SystemPushforwardRestrictionTransition, is not used by this proof. Its
simultaneous direct-image square lives in different coordinates; the ordinary identity on
sections and generic normalized-square naturality give the required square directly.
Removed this proof dependency and both references to it from the assigned node's proof.
No original public import was removed, and no upstream module or declaration was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous DAG route was mathematically plausible but required unnecessary transport
through the simultaneous system pushforward coordinates. The new route uses the already
proved tools lem-sbc-unbounded-exact-adjunction-square and
lem-pur-derived-square-normalization-naturality. There is no statement correction or change
to the meaning of the native evaluation or scalar comparison. In particular the proof does
not assume preservation of K-injectives by evaluation or scalar restriction, and applies
also when the levels coincide and for noncartesian systems.

## New nodes

lem-weil-compact-support-scalar-direct-normalization records the unit equation for the
inverse of sfDerivedImageRestriction, proved in
Sheaf.Paper.CompactSupportScalarDirectNormalization. It is strictly the scalar comparison
step of the parent proof and contains no sorry. Its proof compares the specified
K-injective resolution equation with the existing all-complex normalized comparison.
lem-weil-compact-support-ordinary-direct-transition records the ordinary section square,
proved in Sheaf.Paper.CompactSupportOrdinaryDirectTransition. It uses the two section formulas below and contains no sorry.

lem-weil-compact-support-ordinary-direct-evaluation-sections records the constructed
ordinary comparison and its section normalization, proved in
Sheaf.Paper.CompactSupportOrdinaryDirectEvaluationSections. The proof is the specified
normalization of moduleEvalP followed by the identity section map of
compactSupportDirectModel. It contains no sorry.
No change record is needed: no existing shared definition or statement changed.

lem-weil-compact-support-ordinary-direct-left-sections and
lem-weil-compact-support-ordinary-direct-right-sections record the independently proved
section formulas for the two sides of the ordinary square. Both give the horizontal
restriction of M, and neither has a hole. Their modules split a self-contained section
calculation so each file remains within the compile-time limit.

lem-weil-compact-support-raw-direct-normalization records the generic native evaluation
unit equation. Its proof is extracted unchanged from the assigned module after profiling
identified it as the largest individual type-checking cost. The public theorem is proved
in Sheaf.Paper.CompactSupportRawDirectNormalization and has no hole. The final file uses
it only for the native comparison's unit equation; its public interface is unchanged.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
