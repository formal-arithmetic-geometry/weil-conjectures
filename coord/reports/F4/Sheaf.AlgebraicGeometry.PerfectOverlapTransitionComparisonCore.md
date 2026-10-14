## What changed

Refreshed the item to the H1 correction that landed while this worker was reading the
initial S4 version. The baseline now has one hole: the prescribed stage transition.
Its signature, every existing definition, and the core/coherence theorems are unchanged.

Replaced the stage hole by a complete reduction to `perfect_overlap_hom_continuity`
and the proved categorical `DirectedPerfectHomSystem.lift_iso`. The latter lifts the hom
and inverse separately, transports them to a common stage, and stabilizes both inverse
equations. The stage proof then retains the original functorial transports and both
local-identification equations and recovers the precise prescribed transition by
cancelling its first overlap comparison.

The new Hom-continuity statement asserts all four Hom lifting and eventual-equality
properties for the two overlap objects, together with actual comparison data at every
later stage. It asserts no stage isomorphism. This is a decomposition, not net hole
reduction: the inverse-descent/stabilization portion is now genuinely proved.
Definitions are explicit types, structures and dependent propositions; none chooses
an arbitrary witness from an unproved existence theorem.

All three delivered modules compile without warnings through lcompile.py. Second-reader
compile times after restoring proof dependencies were 1.5 s, 16.7 s and 42.2 s. The dependent Bool comparison must use
`match` so that its return type specializes to the selected overlap object. An early
nondependent conditional caused expensive failed type comparisons; it was corrected.
The structure `TwoOpenTransportData` keeps comparison fields accessible without repeated
expansion of a deeply nested dependent sigma type.

Sources read online: Stacks Tags 09RE (Hom-colimit theorem and open induction) and 09RF
(full faithfulness descending the prescribed overlap isomorphism before gluing).
The library's Hom-continuity API is used as the remaining geometry's stated dependency.
The unit sk-thm-picard-semicon has no realized nodes in this subargument; no unit step
or chapter route is replaced.

## Proved and sorry left

Closed: `AlgebraicGeometry.perfect_overlap_transition_comparison_core_stage`, node
lem-pc-perfect-overlap-transition-comparison-core-stage. The existing coherence and
core packaging proofs remain intact. The item's module now contains no sorry.

Proved new declarations: `AlgebraicGeometry.DirectedPerfectHomSystem.lift_iso` and
`AlgebraicGeometry.iso_comparison_of_conjugated_identity`, node
lem-pc-directed-perfect-hom-iso. The generic theorem needs no nonemptiness assumption:
its limit isomorphism and lifting field already supply stages.

Added exactly one hole: `AlgebraicGeometry.perfect_overlap_hom_continuity`, node
lem-pc-perfect-overlap-hom-continuity, in its own new module. This is Hom continuity
and canonical comparison construction, with no inverse lifting or inverse equations.
It is strictly the part of the argument preceding the now-proved inverse stabilization.
Thus one hole closed and one hole added; net zero, counted as a decomposition.

Edge cases checked in the statement and abstract proof: empty and coincident opens,
zero overlap objects, identity isomorphisms, constant diagrams, and preorders with
non-unique order proofs. Directedness is used only for common upper bounds; all order
proofs are propositionally irrelevant. A singleton directed index with genuine Hom
continuity gives an isomorphism at that singleton, as expected. The canonical family
is an existential theorem witness; no definition extracts it from the new sorry.

## No longer needed

Removed four proof imports from the item:
- Sheaf.AlgebraicGeometry.DerivedPullbackComposition
- Sheaf.AlgebraicGeometry.PerfectDescendMorphisms
- Sheaf.AlgebraicGeometry.DerivedPullbackPerfect
- Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses

The stage proof directly uses only the new Hom-continuity and categorical-isomorphism
nodes. In particular lem-pc-perfect-descend-morphisms and its module are bypassed on
this route: the inverse argument is proved directly from Hom continuity. The composition,
perfect pullback and open restriction nodes remain needed below the new continuity node;
they are not claimed globally unnecessary. The old direct proof dependencies also include def-pc-two-open-comparison-diagram and
def-pc-derived-open-restriction-maps. These remain statement/definition dependencies
and remain imported, but are no longer direct proof steps of the stage theorem. The
new continuity node still needs both. All six old direct proof dependencies are thus
accounted for. Public imports remain required by statements and definitions. No existing Lean module is withdrawn, and no other target branches are
claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The initially read repository version was superseded during the session by H1's repaired
prescribed-transition interface. Work was refreshed before editing; this delivery does
not reintroduce the former arbitrary-overlap coherence claim. No new statement dispute
or interface correction is proposed. The newly remaining statement is stronger than
mere existence of an overlap transition in its Hom-continuity clauses but omits the
inverse stabilization argument; the supplied Lean proof performs that argument explicitly.

Searches: LeanFinder for perfect-complex isomorphism descent returned only general
Grothendieck/category and local-cohomology tools. LeanFinder for directed Hom lifting
returned direct-limit API lemmas, with no exact categorical inverse-stabilization result.
Loogle for CategoryTheory.Functor.mapIso returned mapIso and its functorial laws.
The logged grep query returned unrelated perfect-ring and perfect-group declarations.
Blueprint searches for overlap and Hom continuity found no duplicate of either new node.
LeanSearch was also called for Hom continuity and directed isomorphism lifting; both
requests returned Internal Server Error and are recorded as unavailable, not as no match.

## New nodes

lem-pc-directed-perfect-hom-iso: the generic directed Hom interface and its fully proved
isomorphism lifting theorem, including the elementary comparison cancellation helper.
Module Sheaf.AlgebraicGeometry.DirectedPerfectHomIso. This separates inverse descent
and stabilization from the geometry and does not add any hole.

lem-pc-perfect-overlap-hom-continuity: canonical comparison families and directed Hom
continuity for the four ordered pairs of overlap objects. Module
Sheaf.AlgebraicGeometry.PerfectOverlapHomContinuity. The next worker can prove this by
restricting to the finitely presented compact overlap and using perfect_hom_continuity,
with canonical composition and open-site comparisons. Its complete argument is in its
docstring and DAG steps. No change record or forced adaptation is needed.


## Second reading by F4

1. Compared the entire item against the repository with diff and the declaration
   parser: statement_changed is empty. All three existing theorem signatures and all
   three proposition definitions are byte-for-byte unchanged. The only item edits
   are four proof imports replaced by the continuity import, local heartbeat options,
   and the stage proof. No target, visibility, instance or existing definition changed.
   The existing node changes only proof, proof_deps and proof_origin. Verdict: pass.
2. Compiled all three delivered modules through lcompile.py in import order, without
   warnings (1.5 s, 16.7 s, 42.2 s). Scanned all files: exactly one sorry, in the named
   perfect_overlap_hom_continuity theorem; no forbidden declarations and no data
   holes. A scratch #print axioms check of all structures, proposition definitions
   and theorems shows only the three permitted axioms, with sorryAx only in the new
   continuity theorem and the stage/core theorems that use it. lift_iso uses only
   Quot.sound; coherence uses no sorryAx. The stage proof destructs a Nonempty witness
   inside a proposition: no public definition chooses arbitrary unproved data.
   Verdict: pass, with the one reported geometric hole still open.
3. Read the two new nodes and their Lean modules against Stacks Tags 09RE, 09RF,
   08DW and 0D5S. The geometry uses the compact overlap in the quasi-separated
   finite-presentation base change Yj; its restrictions of A and B are perfect.
   Thus both arguments of every one of the four Hom sets are perfect (in particular
   the target has quasi-coherent cohomology as required by 09RE). E needs no added
   perfectness assumption: its overlap restriction is identified with these pullbacks.
   The new proposition supplies actual comparison families, Hom lifting and equality,
   but no finite-stage inverse. lift_iso genuinely proves that inverse step: it lifts
   both maps, compares both composites to identity, and transports to a common upper
   bound. Its second equality uses a different order proof, valid by proof irrelevance;
   no transport-composition law is silently assumed. Empty/coincident opens and zero
   objects introduce no exception; a constant singleton system reduces to ordinary
   categorical inverse equations. An empty index cannot supply the lifting hypothesis
   for identity. Sources and complete proof docstrings are present. Independent
   LeanFinder search for filtered categorical invertibility, Loogle search for functors
   and IsIso, and Mathlib grep for colimit/full-faithfulness or invertibility found
   preservation/eventual-constant results, not this interface. Repository and upstream
   searches found the existing perfect_hom_continuity and perfect_descend_morphisms:
   the former is the new geometry node's dependency; the latter does not construct the
   simultaneous site comparisons. No duplicate exact statement was found. Verdict:
   a genuine one-for-one decomposition; closing the geometry is not a few-minute task.
4. Read the old proof dependencies, PerfectHomContinuity, PerfectDescendMorphisms,
   DerivedPullbackComposition, DerivedPullbackPerfect, restriction-universe comparison,
   and TwoOpenComparisonDiagram. The direct shorter categorical cancellation helper
   uses Iso.ext and cancellation, with no additional geometric hypothesis. Kept all
   public imports needed by signatures. Restored plain proof imports of the four
   geometry dependencies in the new continuity module, so its stated proof plan remains
   available to its next worker. Expanded No longer needed to account for all six old
   direct dependency nodes, distinguishing retained definition imports from bypassed
   proof steps. The unit sk-thm-picard-semicon has empty realized statement and step
   lists; this lower overlap subargument replaces no realized unit/chapter step.
   Verdict: pass after dependency-import/report repair.
5. Matched the stage node's two steps to obtain data/H, the directed subtype instance,
   H.lift_iso on identity, and iso_comparison_of_conjugated_identity. Matched the generic
   node's three elementary steps to the Lean proof. Matched the continuity node's four
   ordered pairs and exact gamma/theta/tau composites to its dependent Bool API, and its
   proof dependencies to the existing declarations above. New nodes carry source,
   creation, blueprint, chapter/unit, search and verbatim Lean records. No signature
   change record is needed. Verdict: pass.

Changed only the new continuity module's incorrect F1 author credit to F4, restored
its four plain proof-dependency imports, and made the report's pruning accounting
complete. The categorical argument and stage proof required no mathematical repair.
Independent search records are in searches.jsonl; scratch compile/axiom logs are not
part of the delivery. One old hole closed, one new hole added: net zero decomposition.
