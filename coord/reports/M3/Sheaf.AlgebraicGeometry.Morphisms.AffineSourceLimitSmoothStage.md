## What changed

Proved `AlgebraicGeometry.Scheme.exists_smooth_stage_of_affine_source_limit` with its
existing signature unchanged. The proof builds finite affine charts over finite affine
base charts, restricts the system by base change to each base chart, applies affine
diagram descent, passes to one common cofiltered stage, and glues by source locality.
Empty covers work because cofiltered categories have lower bounds for empty finite sets.

Added two proved modules:

- `Sheaf.AlgebraicGeometry.Morphisms.AffineDiagramSmoothStage`: global sections convert
  affine pullbacks to ring pushouts and affine limits to filtered ring colimits.
- `Sheaf.RingTheory.SmoothPushoutFilteredColimitStage`: the existing smooth-algebra
  descent theorem supplies a smooth model; `exists_iso_of_isPullback` compares it with
  the original finitely presented model at a later stage. Pushout cancellation
  identifies that later model with the prescribed stage pushout.

The proof follows the original 0CAQ plus 01ZM route. Sources read online:
[0C0C](https://stacks.math.columbia.edu/tag/0C0C),
[0C0B](https://stacks.math.columbia.edu/tag/0C0B), and
[0CAQ](https://stacks.math.columbia.edu/tag/0CAQ).
The unit's limit-reduction step is retained; no unit or chapter record changes.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.Scheme.exists_smooth_stage_of_affine_source_limit`
(node `lem-sbc-affine-source-limit-smooth-stage`).

Also proved both new declarations:
`AlgebraicGeometry.Scheme.exists_smooth_stage_of_affine_diagram`
(node `lem-sbc-affine-diagram-smooth-stage`) and
`CommRingCat.exists_smooth_pushout_stage`
(node `lem-sbc-smooth-pushout-filtered-colimit-stage`).

No sorry remains in any delivered module; zero holes added. This closes one hole
from existing dependencies, rather than leaving a decomposition. The proof uses the existing `Algebra.exists_smooth_algebra_of_filteredColimit`,
which has since been proved in the shared library. Fresh scratch-copy axiom checks
for all three delivered public theorems show only `propext`, `Classical.choice`
and `Quot.sound`, with no `sorryAx`.

All three modules compile in import order. The final delivery dry run runs the
standard axiom probe and preflight. No definitions, existing signatures, public
imports of the original module, or modules held by other groups were changed.

## No longer needed

Removed the original module's direct proof import of
`Sheaf.RingTheory.SmoothAlgebraFilteredColimitDescent`, replacing it with
`Sheaf.AlgebraicGeometry.Morphisms.AffineDiagramSmoothStage`.
The removed module is still used transitively by the new ring proof, so it is not
pruned from the targets' closure. No planned node or module is globally pruned:
0CAQ, 01ZM, global-sections continuity and smoothness locality all remain needed.
The old direct proof dependencies now used through the new helper modules are
`lem-weil-pbc-limit-global-sections-colimit`,
`lem-weil-pbc-smooth-algebra-filtered-colimit-descent`, and
`thm-pd-spreading-out`. Each remains a transitive proof dependency; none is
unneeded globally. `def-sbc-smooth-morphisms` remains a direct dependency.

Second reading reduced the new modules' public imports: affine-transition limit
continuity is a plain proof import, with `Filtered.Basic` public for the cofiltered
hypothesis. The ring module publicly imports `Ring.Basic` and the pushout-square
definitions instead of all ring colimit constructions. Its proof obtains the
colimit constructions through the existing descent dependency. No module leaves
the targets' import closure. No unused proof imports remain.

## Where the brief, the DAG or earlier work was wrong

Repair of the landing return: removed the private declarations `smooth_snd_comp`
and `smooth_snd_source`, which duplicated private helpers in
`Sheaf.AlgebraicGeometry.Morphisms.AffineLimitSmoothStage`. That module imports this
item, so importing it back would create a cycle; its private declarations are also
not available to importers. Both use sites now directly apply the existing Mathlib
pullback-pasting identities and smoothness instances, without redeclaring either
statement. No signature, import, dependency, or mathematical route changed.

The proof plan was usable. The base and source chart gluing missing from its Lean
interfaces is now written. No mathematical statement was corrected or disputed.

LeanSearch returned Internal Server Error for both actual queries, recorded as
unavailable. LeanFinder, Loogle, Mathlib grep, and project-source searches found no
exact eventual-smoothness theorem. Blueprint searches for smoothness and 0C0B/0C0C
found no duplicate of the two new statements. `blueprint_refs.py ancestor` returned
None for the item's module-valued creation chain; the new records preserve the
existing item's explicit nearest ancestor and extend its `via` chain.

The source comparison theorem elaborates quickly when the two pullback objects,
their projections, and the limit lifts are supplied explicitly. This fixes the
initial heartbeat exhaustion without increasing the heartbeat or time limits.

## New nodes

`lem-sbc-affine-diagram-smooth-stage` records the proved affine-diagram translation
of the fixed-model ring theorem. It includes the affine source and affine target
hypotheses; no Noetherian or nonempty-spectrum hypothesis is needed.

`lem-sbc-smooth-pushout-filtered-colimit-stage` records the proved ring continuity
step. The input map is finitely presented, all stage and limit squares are actual
pushouts, and the algebra structures are compatible with the colimit cocone.
Filteredness supplies a stage even for zero rings. Pushout uniqueness handles
arbitrary choices of the displayed pushout objects. No change record is needed.


## Earlier second reading (a previous round; superseded)

1. **Interface check: pass.** Compared the original module with the repository by
   `diff` and checked the theorem signature byte for byte by script. Only its proof,
   its direct proof import, and three private proved helpers changed. Existing
   public imports, definitions and signatures are unchanged. The other two modules
   are new, and every public theorem matches its node's verbatim Lean statement.
   No change record or forced adaptation is needed.
2. **Proof and axioms: pass.** Read all three complete proofs and compiled them in
   import order through `lcompile.py`, without errors or warnings. A textual scan
   found no `sorry`, axiom declaration, unsafe/opaque declaration, extern or
   implementation override. Scratch-copy `#print axioms` checks for all three
   public theorems showed exactly `propext`, `Classical.choice`, `Quot.sound` and
   inherited `sorryAx`. The existing smooth-algebra descent hole remains open;
   this delivery closes one existing local hole and adds none. The existential
   smooth model is used only inside a theorem proof, never to define public data.
3. **New statements and small cases: pass.** Neither new theorem is split off with
   a hole. The ring theorem assumes actual pushout squares and finite presentation
   of the original map; cancellation gives the correct fixed model at the comparison
   stage. Both affine models satisfy the qcqs hypotheses of the existing comparison
   theorem, and smoothness provides finite presentation of the new model. Checked
   constant/single-object diagrams, identity maps, zero rings and empty spectra:
   no nonzero or nonempty hypothesis is needed. For an empty source cover the
   finite common-stage lemma still supplies a stage, using cofiltered nonemptiness.
   Fresh LeanFinder query `finite presentation algebra smooth tensor product directed
   limit eventually`, Loogle query `"Smooth", "colimit"`, and Mathlib grep for
   eventual smoothness found no exact shortcut. Read the project matches, including
   the NoetherianApproximation affine-model and gluing lemmas: their approximation
   hypotheses are more restrictive and they depend on this eventual-smoothness
   route, so cannot replace these proofs. Verified the cited Stacks tags online.
4. **Route and pruning: pass after repair.** The top proof performs finite base/source
   covers, affine descent, common-stage refinement and source locality. The ring
   helper uses the planned 0CAQ and 01ZM comparison route, with canonical tensor
   product and pullback constructions. Read `dag/units/sk-prop-input-spreading.json`:
   its limit-reduction step is preserved, with no unit/chapter edits. Its existing
   empty `realized` entries predate this work; this item is not the unit's key node.
   The report now lists every old direct proof dependency removed from the top
   node, distinguishing transitive use from global pruning. Removed proof-only
   public exposure of affine-limit and ring-colimit constructions in the new modules.
5. **Nodes: pass.** Read all three node records and checked the Lean signatures and
   equality of `proof_deps` with the union of step `uses`. The recorded proof steps
   match the actual finite-chart, global-sections, pushout-cancellation and model
   comparison proofs. Both new nodes include source, creation, blueprint ancestry,
   chapter/unit, actual searches, proof origin and Lean records. Existing node edits
   stay within the proof fields allowed for stage 3.

Second reading changed only the new modules' import visibility/minimality and this
report's direct-dependency pruning explanation. No proof, statement or definition
needed repair, and no further holes were introduced.


## Second reading by M3

1. **Interfaces: pass.** Read the repository and sandbox module with `diff -u`.
   Compared the original public theorem signature byte for byte by script: no
   hypothesis, conclusion, visibility or public import changed. The direct proof
   import changes and one private proved helper are the only additions outside
   the original proof. The two other modules are new. No definitions, forced
   adaptations or statement-change records occur.
2. **Proofs: pass.** Read all three complete proofs and compiled the set through
   `lcompile.py --all` in dependency order; all compile without warnings. Scanned
   the delivered Lean for sorry and forbidden declaration mechanisms: none.
   Compiled scratch copies with `#print axioms` for each public theorem: exactly
   `propext`, `Classical.choice`, `Quot.sound`, without `sorryAx`. Removed the
   scratch copies. The existential smooth model is eliminated inside a theorem
   proof, never used to define library data. Confirmed that the returned duplicate
   private lemmas `smooth_snd_comp` and `smooth_snd_source` have been removed and
   their uses replaced by Mathlib pullback-pasting identities.
3. **New statements: pass.** There are two new proved statements and no split-off
   holes. The affine theorem translates the fixed-model ring theorem; the ring
   theorem compares two genuinely finitely presented models using the existing
   `exists_iso_of_isPullback`. Pushout cancellation identifies the later model
   with the prescribed stage square. Checked single-object and constant diagrams,
   identity maps, zero rings, empty spectra, and empty finite covers. Filteredness
   supplies nonemptiness; neither a nonzero ring nor a nonempty scheme is required.
   Fresh LeanFinder search for a finitely presented algebra smooth after extension
   to a direct limit, Loogle `RingHom.Smooth, RingHom.FinitePresentation`, and rg
   searches of Mathlib and both project roots found no exact replacement. The
   finite-type smooth-model search hits do not identify the fixed input model;
   the comparison remains necessary. The NoetherianApproximation results are
   specialized and depend on this module through affine-limit descent. Read the
   cited Stacks tags 0C0B, 0C0C and 0CAQ; their statements support this route.
4. **Route and pruning: pass.** The top proof follows finite base/source charts,
   affine continuity, descent, common-stage refinement and source locality. The
   ring proof retains smooth-model descent and finite-presentation comparison.
   Read `dag/units/sk-prop-input-spreading.json`: the unit's limit-reduction route
   is kept, its pre-existing empty realized entries are unchanged, and this item
   is not its key node. Every old direct proof dependency is accounted for under
   No longer needed; all remain transitively used. No module is globally pruned.
   Proof-only imports are plain imports and the new public imports supply the
   public signatures. The remaining private target-locality helper has no duplicate
   in the library.
5. **Nodes: pass.** Read all three JSON records. Script checks confirm each node's
   verbatim Lean signature and equality of proof_deps with the union of step uses.
   The original node changes only proof, proof_deps and proof_origin. Both new
   records have source, natural-language proof, searches, creation, blueprint
   ancestry, chapter/unit and Lean records. Their steps match the actual Lean
   proof, including pushout cancellation and the affine-model comparison.

This second reading changed only this report: corrected the stale claim that
smooth-algebra descent remains holed, recorded the fresh standard-axiom checks,
and appended this independent review. No Lean proof or interface needed repair.
The delivery closes the one original hole, adds zero holes and prunes no modules.
