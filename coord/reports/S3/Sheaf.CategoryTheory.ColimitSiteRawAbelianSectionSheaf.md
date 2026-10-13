## What changed

Repair of the landing-tool return: removed the duplicate private `arrow_postcomp`
from `ColimitSiteRawAbelianStageRestriction` and added the proof-only
`import all Sheaf.CategoryTheory.ColimitSiteRawStageRestriction` to reuse the
existing private theorem at both call sites. No signature or visibility changed.

Replaced the whole sorry in `Sheaf.CategoryTheory.ColimitSiteRawAbelianSectionSheaf`
by a compiled proof, preserving the declaration's signature and all existing public imports.
Added proof-only imports of `ColimitSiteRawAbelianStageRestriction`,
`FinitePresieveFilteredColimit`, Mathlib's functor-category preservation instances,
the filteredness instances for under categories, and `import all` of
`Sheaf.CategoryTheory.ColimitSiteRawSectionSheaf` to reuse its private helpers.

The proof first forgets abelian groups, derives finiteness of every Q-cover from
hQ and the finite stage covers, and checks stage-image covers. Restriction to a
stage is a filtered colimit of stage sheaves. Forgetting groups preserves that
filtered colimit, so the already proved finite-presieve theorem supplies its
sheaf condition. Preserved pairwise pullbacks transfer the condition to the image
cover. The existing private `isSheaf_of_finite_cover_conditions` theorem upgrades the
cover conditions to the generated Grothendieck topology. The existing private
`finite_map_cover` proves finiteness of image covers. Both are reused through
`import all Sheaf.CategoryTheory.ColimitSiteRawSectionSheaf`; the finite-pullback
cover argument is already in their dependencies.

Added `Sheaf.CategoryTheory.ColimitSiteRawAbelianStageRestriction`, whose theorem
is proved by an abelian adaptation of the existing, proved set-valued stage
restriction construction. The proof explicitly constructs the stage sheaf
diagram, derives identity and composition from adjunction injectivity, and
constructs the comparison cocone from beta and the raw coprojections. It uses
one remaining topology-free Kan comparison theorem in the new module
`Sheaf.CategoryTheory.ColimitStageAbelianKanCocone`. This theorem has no topology,
no G, no sheaf adjunctions, and no finite-cover hypotheses: it asserts that the
explicitly supplied compatible stage-presheaf comparison cocone is colimiting.
It is strictly the raw presentation part of the original argument. The finite
cover descent and all stage diagram/coherence construction are proved separately.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.colimit_site_raw_abelian_section_isSheaf`
(node `lem-weil-pbc-colimit-site-raw-abelian-section-sheaf`).
There are no sorries left in the item's module.

Also proved the new theorem
`CategoryTheory.colimit_site_raw_abelian_stage_restriction`
(node `lem-weil-pbc-colimit-site-raw-abelian-stage-restriction`).
Its comparison depends on the lower theorem listed next.

Added exactly one hole:
`CategoryTheory.colimit_stage_abelian_kan_cocone`
(node `lem-weil-pbc-colimit-stage-abelian-kan-cocone`).
Its whole proof is `:= by sorry`; its docstring and node give the additive
Kan-generator proof, including finite sums, finite additive relation witnesses,
and eventual stage equality. This is a decomposition: one original hole closed,
one lower hole added, net zero new-hole reduction. This delivery does not claim
an axiom-free proof of the import closure.

All three modules compile together, without warnings, using lcompile.py.
The remaining statement was checked on the following edge cases: a singleton
stage gives the usual identity Kan comparison; zero stage presheaves give zero
abelian colimits; an empty stage category has no evaluation conditions and its
presheaf category is terminal. Filteredness excludes an empty index category.
The upper proof handles empty covers using the existing finite-presieve theorem,
and repeated image arrows using a surjection of uncurried arrow subtypes rather
than injectivity. No arbitrary data are chosen from an unproved existence theorem:
D and nu are explicitly constructed; IsColimit nu determines their comparison.

## No longer needed

The duplicate private `CategoryTheory.arrow_postcomp` in the new abelian stage
restriction module is removed; both uses now refer to the existing generic
helper in `ColimitSiteRawStageRestriction`. No additional nodes were needed. The stage-restriction node now cites the
existing set-valued stage-restriction node solely for this private generic helper;
its public set-valued comparison theorem is not used.

No existing imports were removed, and no whole module is claimed pruned from the
target closure. The main node no longer needs direct citations of
`lem-weil-pbc-filtered-colimit-sets-elementwise`,
`lem-weil-pbc-filtered-colimits-commute-finite-limits`, or
`lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`.
The old direct proof dependencies `def-weil-pbc-arrows-functor` and
`def-weil-pbc-category-colimit` are also removed from the main node's proof route:
they occur in its unchanged signature and in the lower stage comparison, rather
than as direct steps of the new sheafness proof. These five old direct dependencies
are replaced at this level by the stage restriction and proved finite-presieve
colimit theorem. The elementwise and adjunction facts remain
needed below the stage restriction, so they are not claimed globally obsolete.
The separate general finite-limits commutation theorem is unnecessary for the
finite-cover descent, which uses the proved elementwise finite-presieve theorem.

The proof imports the set-valued raw-section sheaf module solely for its two
private coefficient-independent helpers. It does not use its main theorem,
separatedness, amalgamation, stage restriction, or Kan comparison declarations. Their construction
is adapted for abelian groups, with the algebraic Kan computation isolated.
It does not import the raw abelian evaluation, stage-image sheaf, inverse-image
comparison, representatives, or zero-detection modules. In particular, the
sheafness proof remains independent of the parent comparison theorem.
Removed all three duplicate private helper declarations from the item:
`finite_map_cover`, `finite_pullback_cover`, and
`isSheaf_of_finite_cover_conditions`. The covering-construction module is now
a transitive dependency of the imported existing helpers, rather than pruned.

## Where the brief, the DAG or earlier work was wrong

The landing-tool return correctly identified another duplicate: `arrow_postcomp`
is coefficient-independent and was already stated word for word in the existing
set-valued stage restriction module. This repair imports that module with
`import all` and reuses its private theorem, rather than reproducing it. The
previous second reading has been removed for fresh independent review.

Repair of the returned delivery: the earlier delivery unnecessarily reproved
three private helpers already in the library. `import all` makes the existing
helpers available without changing their visibility or adapting other modules.
The repaired item compiles with the duplicate declarations removed. The earlier
second reading predates this repair and has been removed for a fresh reading.

No mathematical statement was changed or disputed. The planned general
filtered-colimits/finite-limits result and adjunction theorem alone do not supply
the raw abelian Kan presentation. An abelian comparison is needed: forgetting
groups preserves filtered colimits but cannot be applied directly to arbitrary
Kan-extension colimits. The set-valued generic comparison therefore does not
prove the abelian assertion merely by changing coefficients.

The relevant Stacks TeX files are absent in this clone. Read the source paragraphs
at https://stacks.math.columbia.edu/tag/0A35 and
https://stacks.math.columbia.edu/tag/03CO. The additive raw-Kan expansion is marked
agent-written, since those source paragraphs omit the detailed presentation
verification. The existing ancestry utility returns None for this stage-3 item
because its creation chain uses module names; the new nodes record the inherited
section-comparison ancestor and the intervening raw-sheaf/eventual-zero nodes.
The unit's statement and realized steps are unchanged.

## New nodes

`lem-weil-pbc-colimit-site-raw-abelian-stage-restriction`:
new, proved stage restriction theorem in
`lean/Sheaf/CategoryTheory/ColimitSiteRawAbelianStageRestriction.lean`.
It constructs the diagram and cocone explicitly and uses the lower comparison.

`lem-weil-pbc-colimit-stage-abelian-kan-cocone`:
new topology-free abelian presheaf comparison in
`lean/Sheaf/CategoryTheory/ColimitStageAbelianKanCocone.lean`.
This is the sole remaining hole added by this delivery. Both nodes record the
three search kinds; LeanSearch was unavailable, LeanFinder and source searches
found no exact abelian varying-stage result.

No change record is needed: existing signatures, definitions, visibility and
public imports are preserved; the new modules are imported only by proofs.

## Second reading by S3

1. Interface: compared the main module with the repository version using diff,
   and checked declaration signatures with the delivery parser. The existing
   theorem signature is byte-for-byte unchanged; its docstring, visibility,
   and public imports are unchanged. The only additions to this module are
   proof imports, a declaration-local unused-variable linter setting, and the
   proof. The two other delivered modules are new, not forced adaptations.
   No target, existing definition, or public interface was changed. Verdict: pass.

2. Proof: independently compiled all three modules in import order with
   lcompile.py. Each compiled cleanly. Compiled scratch copies with a separate
   #print axioms for each of the three public theorems: all reported exactly
   propext, Classical.choice, Quot.sound, and sorryAx. The one source-level
   sorry is the entire named theorem colimit_stage_abelian_kan_cocone;
   there are no forbidden declarations or hollow definitions. The stage diagram
   D, its transitions, and the cocone nu are explicit constructions. The
   unproved IsColimit property determines the comparison isomorphism by
   uniqueness of colimits; it does not supply an arbitrary witness used as data.
   Verdict: pass as a decomposition, not an axiom-free import-closure proof.

3. Split statements: read both new theorem signatures and their node statements.
   The stage restriction constructs the stage sheaf diagram, proves theta
   coherence by adjunction injectivity, and verifies the comparison cocone.
   The remaining Kan theorem isolates its colimiting property for arbitrary
   compatible abelian presheaves: it has no topology, finite covers, or sheaf
   adjunctions, and does not merely rename the sheafness conclusion. Its hD and
   hnu prescribe the actual transition and cocone maps, including endpoints
   through Arrow equality. In the singleton-stage identity-functor case it is
   the usual Kan unit isomorphism. For zero presheaves both sides are zero.
   For an empty fixed stage the restriction category is terminal, so every
   specified cocone is colimiting there; the filtered index itself is nonempty.
   Finite sums and finite relation witnesses are essential in the supplied
   additive proof sketch, so forgetting an arbitrary Kan colimit to sets would
   not prove this lemma. Read Stacks Tag 0A35, lemma-compute-pullback-to-limit,
   and Tag 03CO: the general additive Kan presentation verification is an
   agent-written expansion, correctly labelled in proof_origin, not a claim
   that Stacks spells it out. Both new statements are strictly lower tasks, and the only
   remaining one is substantial enough that it cannot be closed in a few minutes.
   Searched again with LeanFinder for “Left Kan extensions on a filtered diagram
   of categories commute with restriction to a fixed stage for additive
   presheaves”; results concerned fixed condensed-site Kan extensions, not this
   comparison. Mathlib grep for filtered/Kan combinations returned no matches.
   Loogle with Functor.IsLeftKanExtension returned an unknown-identifier result,
   so it supplies no negative evidence. Searched lean/Sheaf and
   lean/WeilConjectures for stage/Kan and abelian_stage_restriction: the nearby
   proved Kan cocone and restriction modules are set-valued. The existing
   arrow_transport_comp helper is specialized to Type, so the abelian variant
   is necessary; the generic arrow_postcomp is correctly reused. Verdict: pass.

4. Route and pruning: followed the upper proof downward. hQ and finite_map_cover
   give finiteness of Q-covers, stage restriction gives a filtered diagram of
   sheaves, the forgetful functor preserves its filtered colimit, and
   finitePresieve_isSheafFor_filteredColimit handles the finite cover including
   the empty case. hVpullback supplies exactly the pairwise-pullback preservation
   needed to transfer the condition to the image cover. The reused
   isSheaf_of_finite_cover_conditions then gives the generated-topology sheaf
   condition. Surjectivity of the covering-arrow map handles repeated images.
   The two reused private cover helpers and arrow_postcomp are already proved;
   no set-valued main theorem is applied. Checked all five removed old direct
   proof dependencies against the report's No longer needed section; all are
   listed. No module is claimed globally pruned. Inspected sk-thm-p1.json:
   none of these replacement dependencies bypasses a realized unit step, and
   the unit record is unchanged. Tested removal of the new stage module's
   Grp.FilteredColimits import: its public signature then failed to synthesize
   HasWeakSheafify, so restored it unchanged. The other new imports supply
   statement vocabulary/instances or the actual proof lemmas. Verdict: pass.

5. DAG: checked every delivered node's proof_deps is exactly the union of its
   proof-step uses, and every lean.statement matches its theorem signature.
   The existing node changes only proof, proof_deps, and proof_origin. Both
   new nodes carry the source, proof steps, proof_origin, recorded searches,
   creation record, blueprint ancestry, inherited chapter/unit, and complete
   Lean record. The main node cites the raw-section module for its private
   helpers, and the stage-restriction node cites the set-valued restriction
   module only for its generic private arrow_postcomp, as the Lean actually
   does. Verdict: pass.

Changes in this second reading: added this independent review and search
entries. No delivered Lean or DAG change was necessary; the import experiment
was reverted. Reconfirmed one original hole closed, one lower hole added,
net zero hole reduction, and no whole module pruned.
