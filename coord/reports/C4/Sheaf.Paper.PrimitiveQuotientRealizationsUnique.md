## What changed

Restored the quarantined item from its recorded archive and repaired the pullback
part of `WeilConjectures.primitiveQuotientRealizations_unique`. It now chooses a
coherent strict reduction presentation before applying the two normalization
fields, which require the new whole-derived-tower coherence hypothesis. The
scalar-extension part and the existing theorem signature are preserved.

Added the proof-only import `Sheaf.Paper.CoherentPrimitiveReductionPresentation`
and its fully proved theorem
`WeilConjectures.coherentPrimitiveReductionPresentation`. Its construction uses
the existing ordinary quotient adjunction, canonical derived-limit unit, derived
adjunction comparison helpers, and normalized finite-mate comparison. Uniqueness
of left adjoints transports the comparison to the arbitrary given calculus S.
The ordinary unit supplies the strict tower map; the derived counit factorization
proves its entire-tower equation. Equality transports on section types prove the
required generator formula. Thus finite derived evaluations are not used to
detect equality of entire tower maps.

The existing item gains only a proof import; the new helper publicly imports
the model interfaces needed for its signature. Local irreducibility of the standard
derived-category implementation prevents unnecessary elaboration of its chosen
models. A private general derived-transpose identity and a proved equality-transport
cancellation avoid expanding coefficient constructions in diagram calculations.
No shared definition, instance, attribute, signature or public import is changed. No other existing module is adapted.

## Proved and sorry left

This is the assigned zero-hole compile repair. The archived item has 0 `sorry`
bodies; 0 old holes are closed and 0 holes are added. Its declaration
`WeilConjectures.primitiveQuotientRealizations_unique` is restored with a complete
proof. The new declaration
`WeilConjectures.coherentPrimitiveReductionPresentation` also has a complete proof,
with no split-off obligation. Every private helper is proved. There are no
`sorry` bodies in either delivered module. Existing project dependencies remain
available exactly as stated, including their existing unfinished proofs; this
delivery does not claim to close those dependencies.

## No longer needed

None. No original proof-dependency node or import is removed. Both well-definedness
modules still supply the generator-extensionality and localization lemmas used by
the uniqueness proof. The existing realization-model interfaces and evaluation
calculus remain needed. The new coherent-presentation construction adds its
stated dependencies; no module is withdrawn and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The recorded rework error is genuine: the archived pullback proof applies
normalization to `SY.reductionModel` without the coherence premise introduced by
the whole-system presentation repair. An arbitrary finite presentation does not
supply that premise. The replacement constructs a coherent presentation instead
of weakening the interface or treating finite evaluations as conservative.
The item's DAG proof is updated to name that construction.

The existing public derived-adjunction package carries extra geometric and
coherence hypotheses. Its already proved resolving-class helpers and canonical
constant-limit-unit helpers do not require those hypotheses, and suffice for this
construction for every scheme and every given calculus. They are reused through
proof-only `import all`; no existing declaration is generalized or changed.

## New nodes

`lem-trf-coherent-primitive-reduction-presentation`, module
`Sheaf.Paper.CoherentPrimitiveReductionPresentation`, declaration
`WeilConjectures.coherentPrimitiveReductionPresentation`: a good complex admits a
strict finite reduction presentation whose comparison has the prescribed entire
derived-tower transpose. This is the missing presentation substep of uniqueness,
not another uniqueness assertion. The construction handles zero complexes and
n = 0 using the same adjunction identities and has independent site and
coefficient universes. Its source, proof steps, dependencies, Lean signature and
three Mathlib searches are recorded in the new node. No change record is needed:
this packet changes no existing statement or definition.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
