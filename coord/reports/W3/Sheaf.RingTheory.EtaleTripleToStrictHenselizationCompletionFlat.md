## What changed

Closed the only hole in `Sheaf.RingTheory.EtaleTripleToStrictHenselizationCompletionFlat`.
The proof first transports the scheme residue-field separable closure to the local-ring
residue field, then applies the existing
`Algebra.strictHenselization_completion_flat_over_base` over R. Mathlib's
`Algebra.FormallyUnramified.flat_of_restrictScalars` transfers this flatness to each
étale triple algebra. The original theorem statement is unchanged. The second reader replaced the unused public
`StrictHenselizationTriples` import with `Sheaf.AlgebraicGeometry.EtaleResidueTriples`,
which supplies the statement directly.
Removed the proof import `Sheaf.RingTheory.EtaleTripleStrictHenselizationIdentification`;
added proof imports `Sheaf.RingTheory.EtaleResidueTriplesStrictHenselization` and
`Mathlib.RingTheory.Unramified.Finite`.

Added and fully proved the comparison theorem
`AlgebraicGeometry.Scheme.etaleResidueTriples_colimit_isStrictHenselization` in a new
module. It constructs the universal algebra cocone directly from the given ring cocone.
The inverse pointing construction uses Mathlib's actual `SpecToEquivOfField`, without
choosing data from an unproved existence result. The field-point decomposition and
the identity triple also cover arbitrary characteristic, K equal to the residue field,
and the identity étale stage. No Noetherianity is required for this comparison.

Updated the original DAG proof to the scalar-restriction route and recorded the
comparison and the exact Mathlib flatness lemma as new nodes. The unit's realized
statement and steps are untouched. Single-file and sandbox compilation passed without
warnings. The returned duplicate `spec_map_point` declaration was removed; its three uses now
inline the existing two-line calculation, so no duplicate theorem statement is introduced.
No existing definitions, theorem signatures, or other modules were adapted.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.etaleTriple_to_strictHenselization_completion_flat`
(node `lem-sc-etale-triple-to-sh-completion-flat`): 1 of 1 original holes.

Also fully proved:
`AlgebraicGeometry.Scheme.etaleResidueTriples_colimit_isStrictHenselization`
(node `lem-sc-etale-triples-colimit-is-strict-henselization`), including all private
construction helpers. The other new node records an already proved Mathlib theorem.

No `sorry` remains in either delivered module; no holes were added or split off.
The imported theorem `Algebra.strictHenselization_completion_flat_over_base`
(node `lem-sc-strict-henselization-completion-flat-over-base`) now has a proof in the
repository, but its compiled proof still rests on upstream `sorryAx`. The original
flatness theorem therefore still rests on upstream holes; its own hole is closed.
This delivery does not prove those dependencies. The new comparison uses only
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed proof import and dependency:
`Sheaf.RingTheory.EtaleTripleStrictHenselizationIdentification`
(`lem-sc-etale-triple-strict-henselization-identification`).

The original proof also no longer requires these planned nodes and declarations:
`lem-weil-pbc-lfp-affine-opens-finite-presentation`,
`lem-weil-pbc-finite-type-algebra-noetherian`,
`lem-weil-pbc-localization-noetherian`,
`lem-weil-pbc-localization-flat`, and
`lem-weil-pbc-flat-ring-map-comp`.
The corresponding Mathlib declarations are
`LocallyOfFinitePresentation.finitePresentation_appLE` (Morphisms.FinitePresentation),
`Algebra.FiniteType.isNoetherianRing` (RingTheory.FiniteType),
`IsLocalization.isNoetherianRing` (RingTheory.Localization.Submodule),
`IsLocalization.flat` (RingTheory.Flat.Localization), and `RingHom.Flat.comp`
(RingTheory.RingHom.Flat). These were not explicit proof imports of the original module;
`RingTheory.RingHom.Flat` remains a public import needed for the statement. They are pruned from this
node's proof route, not asserted unreachable from every other target.
The second reader also removed the unused public import
`Sheaf.RingTheory.StrictHenselizationTriples`; its theorem is unused, and the triple
diagram is supplied directly by `Sheaf.AlgebraicGeometry.EtaleResidueTriples`.
No assertion is made that this module is globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The planned route through S_q and its completed strict henselization is mathematically
valid but unnecessary. The base-flatness theorem already suffices because every étale
algebra is formally unramified and essentially of finite type. The missing connection
between the two existing strict-henselization encodings was a colimit comparison,
which is proved here rather than left as a new hole.

## New nodes

`lem-sc-etale-triples-colimit-is-strict-henselization`: fully proved universal-cocone
comparison in `Sheaf.RingTheory.EtaleResidueTriplesStrictHenselization`, sourced to
Stacks Tag 04GW. Its signature includes the structural and residue-map compatibility
needed to ensure the two encodings refer to the same R-algebra.

`lem-sc-unramified-flat-of-base-flat`: an exact Mathlib match, already proved as
`Algebra.FormallyUnramified.flat_of_restrictScalars` in
`Mathlib.RingTheory.Unramified.Finite`; no new Lean module or hole.
Both nodes record actual LeanFinder/Loogle/grep searches; LeanSearch returned HTTP 500
and is recorded as unavailable. Blueprint searches found no duplicate.



## Earlier second reading (a previous round; superseded)

Repair check: the duplicate private `spec_map_point` declaration identified by reviewer X-7dda8
was removed from `Sheaf.RingTheory.EtaleResidueTriplesStrictHenselization`; all three call sites
use inline proofs of the same calculation, and both sandbox modules compile. The import cleanup and
public-import adaptation remain recorded in
`coord/changes/EtaleTripleToStrictHenselizationCompletionFlatImports.md`.

## Second reading by W3

1. **Unchanged interface: pass.** Diffed the existing module against the repository
   and checked its theorem signature byte for byte with a script: identical.
   Only its proof, proof imports, and the recorded public import replacement changed.
   The latter has the existing change record
   `coord/changes/EtaleTripleToStrictHenselizationCompletionFlatImports.md`.
   The comparison module is new. No other existing Lean module is delivered or adapted.
2. **Proof and data: pass.** Both delivered modules compiled with `lcompile.py --all`,
   without warnings. Scratch copies with `#print axioms` show only `propext`,
   `Classical.choice`, and `Quot.sound` for the comparison; the original flatness
   theorem additionally has upstream `sorryAx`. Source scans found no local `sorry`,
   forbidden declarations, or kernel bypasses. Read every construction helper and
   the cocone factorization and uniqueness proofs. `pointedAsTriple` obtains its
   prime and embedding directly from Mathlib's proved `SpecToEquivOfField`;
   no arbitrary witness of an unproved existence theorem is chosen.
3. **New statements and searches: pass.** No statements are split off with holes.
   The comparison is a real categorical subargument, with no Noetherianity or
   completion assertion, and all its helpers are proved. Checked the identity triple,
   arbitrary characteristic, and the case of a separably closed residue field with
   identity embedding. For arbitrary `p`, the compatibility hypothesis forces the
   prescribed residue map; no extra point is silently selected. Independent LeanFinder
   search for a universal pointed-etale cocone found no comparison theorem. Independent
   Loogle search `Algebra.FormallyUnramified, Module.Flat` confirmed the exact theorem
   and all its assumptions; read the local Mathlib source. Grep of both library roots
   found the existing `IsStrictHenselization.triples_presentation`, whose conclusion is
   the opposite direction and does not supply this comparison. Its underlying
   category-equivalence helper is private. The formerly duplicated `spec_map_point`
   declaration is absent; its uses are short inline calculations.
4. **Route and pruning: pass.** Base-completion flatness plus unramified scalar
   restriction avoids the old localization argument. All six removed nodes from the
   original `proof_deps` are accounted for under `No longer needed`; the two removed
   module imports are also recorded. Both public imports of the new module supply
   its statement; the new unramified and comparison imports of the item are private.
   Read `dag/units/sk-thm-br.json`: this auxiliary node does not replace the unit's
   Brauer-injection/Tsen step, and its `realized` record stays untouched. The sole
   direct importer `PointedEtaleCompletionStageFlat` compiled unchanged in the scratch
   set against the delivered modules, confirming the public-import cleanup locally.
5. **DAG agreement: pass.** The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. For all three nodes, checked that `proof_deps` is exactly the union
   of step uses. The two new nodes give sources, search records, provenance, chapter,
   unit, blueprint linkage, and actual Lean declarations. Checked the cited sources
   online because the literature texts are absent on this machine:
   [Stacks 04GW](https://stacks.math.columbia.edu/tag/04GW) for residue triples and
   [Stacks 06LJ(c)](https://stacks.math.columbia.edu/tag/06LJ) for completion flatness.

Changes in this reading: replaced the item's stale localization-route docstring with
its actual residue-field transport, colimit comparison, and scalar-restriction proof;
appended this review. The Mathlib leaf correctly has no `lean.file`: its source file
is identified by `mathlib_match`, and no existing Mathlib file is delivered.
No proof term, theorem signature, or definition needed repair.
