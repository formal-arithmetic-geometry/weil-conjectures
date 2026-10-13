## What changed

Proved AlgebraicGeometry.Etale.objectSections_naturality directly by restriction-unit
compatibility, composition-unit coherence, pullback extensionality and terminal
evaluation naturality. The statement is unchanged. Added three private proved
helpers, adapted from the already proved calculations in Sheaf.Paper.EtaleRestrictionPullbackUnitEq
and Sheaf.AlgebraicGeometry.EtaleObjectSections. Generalized terminal evaluation to
restriction along an arbitrary arrow into the terminal object, rather than
redeclaring the existing private pointwise equality. Removed the unused public import of
Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceComparison. Updated the existing
node's proof route and dependencies. Change record:
coord/changes/objectSectionsNaturality-imports.md.

## Proved and sorry left

Closed the one original hole: AlgebraicGeometry.Etale.objectSections_naturality
(node lem-weil-pbc-object-sections-naturality). No sorry remains in this module,
no holes added and no statements split off. Private helpers restriction_unit,
composition_unit and terminalEvaluation_map_eq_res are fully proved. The delivery
probe checks the axioms; the direct proof does not use any holed theorem.

## No longer needed

Removed import Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceComparison:
its strict-local injective constructions and node
 def-weil-pbc-strict-local-injective-source-comparison are unnecessary for this proof.
This does not assert that the module is globally unreachable: the direct importer
SourceStageSectionsNaturality imports it independently.

The theorem AlgebraicGeometry.Etale.etaleObjectSections_baseChange is not needed.
Its module Sheaf.AlgebraicGeometry.EtaleObjectSections stays publicly imported because
it defines etaleObjectSectionsIso, which occurs in our statement; that definition is
why its node remains a dependency. No unit statement or realized step is bypassed:
dag/units/sk-prop-h2.json has empty realized statement and step lists.
The coherence import and the remaining public EtaleObjectSections import are used.

## Where the brief, the DAG or earlier work was wrong

The DAG's proof description is sound but its sole listed dependency is incomplete:
the actual direct calculation needs the restriction/unit comparison and composition
coherence, now named in proof_deps. The base-change theorem is not a prerequisite
for naturality under an arbitrary arrow over X. The strict-local injective source
comparison import was unrelated to this underived statement.

Searches: LeanFinder returned ringed-space residue-field evaluation results, no exact
match. Loogle could not resolve Adjunction.comp_unit_app. Repository search found
proved private restriction/composition-unit helpers in EtaleRestrictionPullbackUnitEq
and terminal-evaluation calculations in EtaleObjectSections; these were reused.

Repair of the returned landing (reviewer X-4f580): import_prune_check.py
correctly rejected terminalEvaluation_eq_res as an exact duplicate of the
private theorem in EtaleObjectSections. An ordinary import cannot access that
private theorem. Replaced the duplicate with terminalEvaluation_map_eq_res:
for every f : S ⟶ T with T terminal, terminal evaluation followed by F(f)
is restriction to S. The old pointwise equality is now only a local calculation
inside that generalized proof. The main proof specializes the generalized
statement at identity arrows. This is a stronger restriction compatibility
statement, not a renamed duplicate. It follows from the terminal adjunction
calculation and Mathlib's Sheaf.ΓRes_map. No new statement is left unproved.
The import-pruning check now passes. The delivery dry run fetches sheaf-dag
and reconstructs the delivery on that current base; no manual git operation
is used. The earlier second reading is superseded by this repair and must be
repeated by the independent reader.

## Second reading by V4

1. Interface: PASS. Compared the delivered module and node with the repository
   by diff. The sole existing declaration, AlgebraicGeometry.Etale.objectSections_naturality,
   has a byte-for-byte identical signature. No definition or target changed.
   The removed public import is declared in objectSectionsNaturality-imports.md;
   the three new helpers are private and proved.
2. Proof: PASS. Compiled the delivered module locally with lcompile.py, without
   errors or warnings. Refreshed the scratch axiom probe from the actual repaired
   file (the old scratch copy still contained the rejected terminal helper).
   Printed axioms for restriction_unit, composition_unit,
   terminalEvaluation_map_eq_res and objectSections_naturality: each uses only
   propext, Classical.choice and Quot.sound. No sorry, forbidden declaration,
   hollow definition, or witness chosen from an unproved existence theorem occurs.
3. Splits and truth: PASS. No statements split off and no holes added. Read all
   helpers: restriction_unit follows from adjoint uniqueness and unit naturality;
   composition_unit is the pointwise coherence identity followed by naturality;
   terminalEvaluation_map_eq_res is terminal evaluation followed by ΓRes_map.
   At an identity arrow the terminal helper reduces to evaluation itself; arbitrary
   arrows satisfy the cone restriction equation. These formulas impose no
   nonemptiness or nonzero-section assumptions and apply also to the empty scheme
   and zero sheaf. The terminal helper is more general than the existing private
   pointwise equality and is fully proved, not a restatement carrying a hole.
4. Route and pruning: PASS. Read EtaleObjectSections, the existing private
   unit calculations, upstream coherence and Mathlib GlobalSections. Additional
   repository searches used ΓRes_map, terminal evaluation, object sections and
   unit_leftAdjointUniq_hom_app. msearch grep found adjoint uniqueness and ΓRes_map;
   LeanFinder found ΓRes_map, ΓRes_naturality and natTransΓRes; Loogle did not
   resolve Sheaf.ΓRes. No shorter applicable public theorem was found. Existing
   matching helpers are private to their modules and cannot be used by ordinary
   imports. The proof opens the original hole and combines genuine smaller
   calculations. EtaleObjectSections is public because its definition occurs in
   the signature; Coherence is proof-only and stays a plain import. No original
   proof_deps node was removed: the object-sections node is still needed for its
   definition, though its base-change theorem is unused. The unrelated strict-local
   import and node are fully listed under No longer needed. sk-prop-h2 has empty
   realized lists, so no realized unit statement or step is bypassed.
5. DAG: PASS. The three proof steps match the two unit calculations, pullback
   extensionality, terminal restriction and final naturality/cancellation.
   proof_deps is the union of their uses, and proof_origin explicitly distinguishes
   use of etaleObjectSectionsIso from the unused base-change theorem. The restriction
   and composition dependency nodes record the actual upstream declarations used.
   No new DAG nodes or unrecorded statement changes are present.

Second reading changed only this report and refreshed scratch verification files;
the repaired Lean proof and node required no further changes. One original hole
closed, zero holes added, zero statements split off.

Downstream check: copied the unchanged repository SourceStageSectionsNaturality
into the item's scratchpad and compiled it in import order against the delivered
ObjectSectionsNaturality. Both compiled without errors or warnings (43.0 s and
11.4 s). Its own public StrictLocalInjectiveSourceComparison import preserves the
removed export, so no forced adaptation is needed.
