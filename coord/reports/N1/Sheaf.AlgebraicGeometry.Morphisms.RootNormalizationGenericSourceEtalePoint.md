## What changed

Replaced the single sorry in
`AlgebraicGeometry.Scheme.root_normalization_generic_source_etale_point`
with a compiling proof combining two strictly separate local calculations.
All original public imports and the original theorem signature are unchanged.
Added proof-only imports of RootNormalizationGenericStalkFlat,
RootNormalizationGenericStalkUnramified, FiniteFlatTargetLocus and
FormallyUnramifiedStalkNeighbourhood.

The private proved helper `etale_neighbourhood_of_fibre_flat_stalks` constructs
the open target flat locus F, proves flatness of the restriction by transporting
stalk maps, chooses an unramified source neighbourhood B, and intersects B with
the inverse image of F. It proves flatness and formal unramifiedness of this
intersection by explicit factorizations through the two restrictions. Finiteness
over a locally Noetherian scheme supplies finite presentation, so Mathlib's
flat/unramified criterion yields the required etale neighbourhood.

New modules, one named public theorem per module:
`Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationGenericStalkFlat` and
`Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationGenericStalkUnramified`.
The flatness calculation is stated for an arbitrary finite etale punctured cover
of the explicit root algebra, with no Galois or ramification hypothesis. The
unramifiedness calculation retains the original G-torsor, group-order unit,
root extension and compatible cartesian comparison. Neither new conclusion
asserts etaleness or an open neighbourhood. The original node now records this
assembly and its four actual proof dependencies. No existing interface changes,
forced adaptations, target changes or definition changes occur.

## Proved and sorry left

Holes closed: 1 of 1, by declaration name:
`AlgebraicGeometry.Scheme.root_normalization_generic_source_etale_point`
(node `lem-sbc-root-normalization-generic-source-etale-point`).
Its body and the private neighbourhood helper contain no sorry.

Holes added: 2, each a whole proof `:= by sorry` in its own new module:
- `AlgebraicGeometry.Scheme.root_normalization_generic_stalk_flat`
  (node `lem-sbc-root-normalization-generic-stalk-flat`).
- `AlgebraicGeometry.Scheme.root_normalization_generic_stalk_unramified`
  (node `lem-sbc-root-normalization-generic-stalk-unramified`).

This is a decomposition, not a completed Abhyankar calculation: one upper hole
closed and two strictly simpler local holes added, net -1 before any pruning.
The new docstrings and nodes give their hypotheses, source locations and complete
natural-language proofs. Existing spreading lemmas are used as declarations;
no changes to their modules are included.

## No longer needed

No original imports removed and no original nodes or modules pruned: the original
node had no proof dependencies and its public imports are required by its statement.
No import of RootNormalizationGenericSourceEtale or the strict-hensel generic-etale
assembly is used, since those depend on this item. No purity, global etaleness,
strict henselization, or standard cyclic-chart splitting theorem is needed for the
neighbourhood assembly. These are alternatives not imported, not claimed pruning.
The former rejected core and its node remain outside the delivery inventory in
scratchpad/rejected; they are not dependencies of this delivery.

## Where the brief, the DAG or earlier work was wrong

The original node's single step has no named dependencies despite hiding both the
DVR/Abhyankar calculation and the spreading argument. This delivery makes that
argument into Lean at its outer level and exposes precisely the two remaining
local calculations. The unit `sk-prop-input-spreading` and its realized fields
are untouched; its tame root-extension route is preserved.

The previous candidate discarded the original root and tame hypotheses and was
false for the quadratic cover t=s^2 at zero. The present flatness lemma allows
that example: the map is flat, so no unramifiedness is concluded from it. The
new unramifiedness lemma requires the actual group-order root base change. For
the order-two torsor over D(t), after t=r^2 the quadratic generic algebra splits
as the two factors s=r and s=-r (characteristic different from two), whose
normalizations are unramified. Thus the previous counterexample does not satisfy
the new unramified statement without the required root extension.

Edge checks: n>0 is explicit in the flatness lemma and follows from the group
instance in the original theorem; n=1 gives the DVR normalization calculation
and, for the unramified assertion, a trivial torsor. Empty covers/fibres make the
pointwise conclusions vacuous. A unit g is excluded by the domain quotient
hypothesis. Wild ramification is excluded only in the unramified lemma by hG,
where it is needed; flatness over a DVR does not require tame ramification.
An arbitrary finite branched normalization is never assumed unramified.

Searches used msearch.py (LeanFinder, Loogle and grep, with both new statements
also queried through LeanSearch); LeanSearch returned HTTP 500, recorded as
unavailable. Read the local Mathlib and source-library stalk and normalization
interfaces. Existing generic-etale wrappers are circular for this item, and the
trait-section statements have genuinely different hypotheses. Checked the
sources [09EB](https://stacks.math.columbia.edu/tag/09EB),
[0BRM](https://stacks.math.columbia.edu/tag/0BRM),
[0EYG](https://stacks.math.columbia.edu/tag/0EYG),
[0307](https://stacks.math.columbia.edu/tag/0307),
[0539](https://stacks.math.columbia.edu/tag/0539),
[00RC](https://stacks.math.columbia.edu/tag/00RC) and
[02GF](https://stacks.math.columbia.edu/tag/02GF).

Compiled the new modules in dependency order and the original module against
them using lcompile.py. The assembly compiles without warnings. The delivery tool
ran its axiom probes and printed `OK (dry run)`: compilation and preflight pass,
with the independent second-reading section to be supplied by the second reader.
No forbidden axioms or hollow definitions were introduced. The two new theorems
remain sorry dependencies; this is a decomposition, not an axiom-free final proof.
The mechanical signature comparison reports no changed original signatures;
verbatim node signatures, proof-dependency unions and 100-character lines pass.
Nothing pushed.

## New nodes

The delivery adds `lem-sbc-root-normalization-generic-stalk-flat` in
`RootNormalizationGenericStalkFlat.lean`; its node and Lean statement are
listed above, and it isolates the finite torsion-free DVR flatness calculation.
It also adds `lem-sbc-root-normalization-generic-stalk-unramified` in
`RootNormalizationGenericStalkUnramified.lean`; its node and Lean statement are
listed above, and it isolates the tame root-extension unramifiedness calculation.

## Second reading by N1

1. **Signatures and visibility.** Compared the delivered item and both new modules
with the repository and checked the declarations verbatim. Verdict: existing
signatures and public imports are unchanged; the two added statements are
explicitly split-off public theorems.

2. **Compilation and axioms.** Compiled all three modules with `lcompile.py` in
dependency order. The item proof has no `sorry`, definitions contain no holes,
and the only remaining holes are the two named split-off theorems. The assembly
uses no forbidden declarations; the split-off theorems necessarily expose
`sorryAx` until their nodes are proved. Verdict: compile and axiom checks pass
under the stated open dependencies.

3. **Truth and strength of statements.** Read both new statements against their
docstrings and the source tags. The flatness statement makes no tame or
unramified claim, while the unramified statement retains the torsor, invertible
group order, root extension, and cartesian comparison hypotheses. Edge cases
`n = 1`, empty fibres, and branched covers without the root extension were
checked in the report. Verdict: each is a strict, needed reduction and neither
restates the parent target.

4. **Proof route and pruning.** The parent proof follows the unit route: pointwise
flatness and unramifiedness, the finite flat target locus, and a formally
unramified source neighbourhood are assembled by the flat-plus-unramified
criterion. Imports are proof-only where appropriate, and no old proof dependency
was silently dropped. Verdict: route and dependency records agree with the code.

5. **DAG and unit agreement.** Checked all three node records, verbatim Lean
statements, proof dependencies, provenance, chapter, and unit. The parent node
realizes the same `sk-prop-input-spreading` route, with the two new nodes and the
two existing neighbourhood/locus nodes recorded as uses. Verdict: DAG agrees
with the delivered Lean.

Changed during second reading: added this review section only; no Lean code,
statements, definitions, imports, or DAG records were changed.

`lem-sbc-root-normalization-generic-stalk-flat`:
`dag/nodes/sec-smooth-base-change/lem-sbc-root-normalization-generic-stalk-flat.json`.
Generic-root-divisor DVR identification and torsion-free integral closure imply
flatness at all normalization stalks in that fibre. Its Lean record contains the
verbatim signature and its planned dependencies include stalk normalization base
change and the Mathlib finite torsion-free DVR freeness leaf.

`lem-sbc-root-normalization-generic-stalk-unramified`:
`dag/nodes/sec-smooth-base-change/lem-sbc-root-normalization-generic-stalk-unramified.json`.
This isolates the tame DVR ramification elimination: the degree formula makes
every component index divide |G|, the root extension has that index, Abhyankar
makes normalized indices one, and separable residues imply formal unramifiedness.
Its Lean record contains the verbatim signature. No change record is required:
no existing definition or statement was changed.
