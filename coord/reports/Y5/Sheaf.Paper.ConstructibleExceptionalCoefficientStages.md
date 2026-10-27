## What changed

Replaced the hole in `WeilConjectures.ConstructibleExceptionalCoefficients.exists_coefficient_stages`
by a complete Lean assembly of two proper subarguments: finite/integral ring-stage assembly,
then field-stage completion of that fixed input. The theorem's signature and its public import
are unchanged. Its proof imports `ExceptionalRingStageAssembly` and
`ExceptionalFieldStageCompletion` privately.

The new `ExceptionalRingStageAssemblyData` module defines the ring-only partial datum and two
explicit constructors. `extendOperation` uses the four cases of the existing stage index;
`complete` keeps every ring scalar, mate and realization from the supplied ring-only datum.
Neither constructor chooses an existential witness or contains a postponed proof. The other two
new modules each state one remaining theorem, with its source and full proof plan.

The final normalization assembles the five field normalization families and the inherited ring
left-shift equations. Its common-transition equation is proved from
`common_morphism_normalized`, by specializing the representative arrow to identity, simplifying
functor maps of identity, and cancelling the inclusion comparison and its inverse. It is not a
new assumption in either split theorem. The calculation is isolated in the proved private generic
lemma `representativeAction_transition`, with explicit functor-object reduction and identity
rewrites. No existing definition or other existing module changes.

Verification: all three new modules compiled through `lcompile.py`; the final item compile
passed without warnings in 5.4 seconds. Debug/profiler options were removed. The item signature
was compared verbatim with the shared source, and the DAG proof-dependency unions were checked.

## Proved and sorry left

This is a decomposition: one upper hole is closed and two strictly smaller holes are added
(net holes closed minus holes added: -1), not a complete proof of coefficient-stage existence.

- Closed: `WeilConjectures.ConstructibleExceptionalCoefficients.exists_coefficient_stages`
  (`lem-sf-constructible-exceptional-coefficient-stages`), by the explicit assembly and
  representative-arrow calculation described above. No `sorry` remains in the item module.
- Proved constructions, with no postponed data or proof:
  `WeilConjectures.ConstructibleExceptionalCoefficients.RingStageAssembly.extendOperation` and
  `WeilConjectures.ConstructibleExceptionalCoefficients.RingStageAssembly.complete`.
- Added and left with exactly `by sorry`:
  `WeilConjectures.ConstructibleExceptionalCoefficients.exists_ring_stage_assembly`
  (`lem-sf-ring-stage-assembly`). This constructs only finite/integral operations and ring
  scalar data; it has no rational/closed operation or field comparison in its conclusion.
- Added and left with exactly `by sorry`:
  `WeilConjectures.ConstructibleExceptionalCoefficients.exists_field_stage_completion`
  (`lem-sf-field-stage-completion`). This receives the ring-only datum and produces only its
  rational/closed extensions and field comparisons. The resulting full record uses the given
  ring operations, scalars and mates definitionally, so the lemma does not reconstruct the
  original obligation under a renamed hypothesis.

## No longer needed

No preexisting public or private import is removed, and no module or mathematical dependency is
withdrawn. The six original proof dependencies remain needed below the two split statements:
finite operations, finite scalar mates, system transport, integral reconstruction and integral
scalar mates feed the ring-only statement; field descent feeds field completion. The latter also
records the projection cocycle, open tensor normalization and scalar-unit dependencies used to convert the normalized input
to the field-descent interface. The item's direct DAG dependencies now name the two actual
subarguments and their explicit data constructor. No compactification-refinement node is used.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or change of unit route is proposed. The existing `exists_system` is
not an independent shortcut: its proof uses coefficient construction, which imports this item.
The adopted source's `exceptionalInverseImage_coefficientStages` is only its finite-stage
assertion and requires absolute separatedness; `boundedConstructibleIntegral_exceptionalAdjoint`
also requires absolute separatedness and is stated on ordinary etale ambient categories. Neither
supplies this item's unrestricted geometric hypotheses and normalized four-stage record. The old five-step plan compresses
several interface transports into prose: globally shared scalar restrictions, transport between
the reconstructed integral adjunction and its prescribed realization, and the conversion from
that presentation to field descent's prescribed linear input. Those transports are the precise
remaining work, not an absence of the six dependency declarations. The new statements separate
the ring and field portions without changing the required coefficient categories or geometric
hypotheses.

Edge cases were checked at the statement level: empty schemes use zero operations; residue
levels remain positive; identity and composite coefficient maps retain their literal maps and
tensor unitors/associators; nonflat quotients are included; no absolute separatedness or
ambient closed-coefficient adjunction is added. For arbitrary supplied ring data in the field
lemma, its integral-left isomorphism transports linearity, and normalized q is fixed by the
faithful inclusion; these justify the prescribed linear input and its left scalar cocycles.
Raw localization is taken on the original integral left functor so identity localization q
is possible without replacing that supplied operation.

## New nodes

`def-sf-ring-stage-assembly-data` owns the finite/integral partial datum and its explicit
four-case extension/assembly constructors in `ExceptionalRingStageAssemblyData`.

`lem-sf-ring-stage-assembly` is original steps 1--4 only, using the five existing finite,
system and integral declarations. Its sole theorem is in `ExceptionalRingStageAssembly`.

`lem-sf-field-stage-completion` is original step 5 with the required presentation transports,
raw localized action and common representative action made explicit. It receives ring data and
constructs only the field extension, in `ExceptionalFieldStageCompletion`.

The whole blueprint and Lean trees were searched for ring-stage assembly and field-stage
completion; no equivalent existing node or declaration was found. LeanFinder, Loogle,
LeanSearch and Mathlib grep searches were made with `msearch.py` and are recorded in the new
nodes. The source was read locally: Zheng, Lemma 5.22, Proposition 5.24, Construction 5.25,
Proposition 5.26 and Constructions 6.2/6.6. No change record is needed because all existing
interfaces and definitions are preserved.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
