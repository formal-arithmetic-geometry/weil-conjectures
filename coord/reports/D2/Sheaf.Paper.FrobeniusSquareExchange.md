## What changed

Replaced the proof hole in `WeilConjectures.FrobeniusExchange.modelScalarMap_isIso` with a
two-case proof for the retained `SupportModel`. In the compact case,
`sfCompactSupportCoefficientExchange_isIso` supplies invertibility of the specified
whole-system coefficient exchange. The two surrounding `compactRealization` maps are
components of isomorphisms. Functoriality preserves their invertibility.
`ObjectProperty.isIso_hom_iff` lifts invertibility to the full constructible subcategory,
and `NatIso.isIso_of_isIso_app` gives the natural-transformation result. The direct case
uses the analogous component result in the new module
`Sheaf.Paper.DirectImageCoefficientExchangeInvertible`. The component instances are
installed before applying the natural-transformation isomorphism theorem. The compact
component is proved by the hom of its actual three-isomorphism composite, with the
existing middle-component proof passed explicitly to `asIso`.

Local irreducibility settings keep pullback, exchange and scalar constructors from being
repeatedly expanded in later proofs. In particular the tensor composition constructor
stays opaque, using its pure-tensor API. The private `localizedFunctor_comp` proof now
performs tensor induction directly, avoiding a large conversion through the generic
helper. These settings are local to the module; they do not alter exported reducibility
attributes or definition bodies.

Added proof-only imports of that new module and
`Sheaf.Paper.CompactSupportCoefficientExchangeInvertible`. Existing public signatures,
definition formulas, exported attributes and original public reexports are unchanged. The
independent finite-origin section is now publicly reexported from
`Sheaf.Paper.FrobeniusWitnessedCompactification`. Its existing coherence obligation moves
with it, without adding or closing a hole. Updated the item's DAG proof and dependencies
and added the node for the new direct-image obligation.

This is a partial delivery: the completed assembly genuinely disposes of the
compact-support branch using its existing declaration. The new obligation has no Frobenius
maps, support recipe, compactification comparisons, rational localization, or stage
system. It asks only for one realized direct-image coefficient component.

Validation before the structural split: the full module compiled cleanly in 42.7 seconds,
but delivery preflight subsequently took 63 seconds and refused the packet. After local
opacity and tensor-proof improvements, this motivated the self-contained finite-origin
extraction. The final split was accepted by `lcompile.py`, as were both unchanged direct
importers: `Sheaf.Paper.FrobeniusGeometricExchange` and
`Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence`. All final checks
returned exit code zero and no warnings. Temporary consumer copies were removed
after verifying that they still matched the current source. The new direct-image
module also passed the earlier complete sandbox batch. No consumer adaptation
was needed.

## Proved and sorry left

Closed the existing hole in `WeilConjectures.FrobeniusExchange.modelScalarMap_isIso` (node
`def-weil-operation-exchange-coefficient-descent`). This is a decomposition, not a net new
proof: one existing hole closed and one new hole added.

The three original obligations still open across the packet are:

- `WeilConjectures.FrobeniusExchange.intrinsicCompactificationCoherence`
  (`def-weil-frobenius-witnessed-compactification`, relocated unchanged).
- `WeilConjectures.FrobeniusExchange.stageBeta_coherence`
  (`def-weil-operation-exchange-coefficient-descent`).
- `WeilConjectures.FrobeniusExchange.stageExchange_compatible`
  (`def-weil-operation-exchange-coefficient-descent`).

The one new hole is:

- `WeilConjectures.directImageCoefficientExchange_isIso`
  (`lem-weil-direct-image-coefficient-exchange-invertible`).

The two stage holes remain in the assigned module. The original
`intrinsicCompactificationCoherence` hole moves unchanged to
`Sheaf.Paper.FrobeniusWitnessedCompactification`; its relocation is neither a closed hole
nor an added hole. The packet has four holes altogether: those three original obligations
and the one new direct-image obligation. The imported existing compact-support component
theorem also still has its previously registered hole; this delivery does not add or alter
it. No hole is inside a definition, no axiom is added, and no statement is weakened.

## No longer needed

Removed the now-unused private helper `genericLocalizedHom_comp` after replacing the
specialized composition proof with direct tensor induction. No module or DAG dependency is
withdrawn. The finite-origin section is relocated to a new module solely to meet the
compile limit; every public declaration is reexported. The existing definitions and public
reexports remain available to consumers. Both new proof-only imports are used by the two
branches. The other original proof imports remain used by the previously completed
linearity and rational scalar localization arguments.

## Where the brief, the DAG or earlier work was wrong

The original model coefficient-invertibility proof plan did not exploit the already stated
compact-support component theorem. That half of the argument can be discharged without new
theory. There is no matching direct-image component statement for this actual system
realization: project searches find other completed direct-image scalar comparisons, whose
identification with this normalized whole-system mate still needs proof. The new lemma
isolates that step.

The direct-image proof plan uses finite freeness of the completed coefficient extension.
It does not claim that quotient-ring inclusions are flat or that `systemDirectScalar` is
invertible on all systems. To identify the realized map, compare the adjuncts after the
normalized scalar reduction counits; the equality must precede finite evaluation. The
docstring and DAG spell out this normalization.

Checked edge cases of the new statement: for the identity coefficient embedding it is the
completeness/tensor-unit comparison; on a zero input or empty source both objects are
zero; ramification changes the quotient presentations but does not remove finite freeness
of the completed coefficient extension. No scheme map is required to commute with
Frobenius in this lower assertion.

During work the shared snapshot restored the finite-origin section inside this module and
withdrew its extracted module. Rebased on that current source and restored every
declaration and its DAG attachment, including the existing
`intrinsicCompactificationCoherence` obligation. The earlier extracted module is not
imported. Later delivery preflight exceeded 60 seconds even after local definition
improvements. A new self-contained extraction now retains the current section, including
the unchanged coherence obligation, as `FrobeniusWitnessedCompactification`.

The unit's statement and its realized steps are unchanged. The compact-support component
result is a tool from the unit `sk-def-sf-operations`, which the owning unit already
cites. The new direct-image node inherits the item's chapter/unit.

## New nodes

`lem-weil-direct-image-coefficient-exchange-invertible`, in `dag/nodes/sec-six-functors/`,
records the single direct-image component assertion in
`Sheaf.Paper.DirectImageCoefficientExchangeInvertible`. Its proof plan uses finite-free
completed scalar comparison, the ordinary direct-image coefficient law, strict-system mate
normalization and the projection-normalized Roos comparison. The lemma is strictly one
branch of the argument for the old hole; the compact branch and the
subcategory/natural-transformation assembly are proved in Lean in the assigned module.
LeanFinder, LeanSearch and grep searches are recorded with their actual results. The
extraction node `def-weil-frobenius-witnessed-compactification` owns the 34 relocated
finite-origin declarations in `Sheaf.Paper.FrobeniusWitnessedCompactification`. Their
names, types, construction formulas, completed proofs and the original coherence hole are
preserved. The change record is `coord/changes/D2-frobenius-witnessed-split.md`. No other
existing module is edited.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
