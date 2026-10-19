# Stage-1 report — Q116

## Files written

- dag/nodes/sec-six-functors/lem-trf-ambient-thick-closure-equivalence.json: existing statement node, now split into four proof steps; no whole-item Mathlib match.
- citations.json: six verbatim quotations, one for every step/node citation.
- report.md: this report. searches.jsonl records the prescribed search commands.

No new nodes or Mathlib leaves were created. The statement, statement dependencies, source, created fields, chapter, unit and blueprint ancestry are retained. No unit realization fields need changing: this item is a helper, not the unit key statement.

## Attachments

None. I searched the exact blueprint tag and the ambient/thick/equivalence notions in the project declarations under the read-only slopmaster2 WeilConjectures tree. The exact tag has no match. WeilConjectures/Mathlib/CategoryTheory/Triangulated/Generators.lean:106, isIso_app_of_triangEnvelope, extends invertibility of a natural transformation; it does not compare ambient closures. The scheme-specific constructibleFiniteTor_eq_triangEnvelope_ctfGenerators at SixFunctors/Etale/Derived/Stability/Generation.lean:356 is not the abstract assertion here. No declaration found states every clause of this item. The upstream master tree was also searched by the item tag and supplies no attachment.

## WANTED

None. The proof is agent-supplied, as the item source already says. The local blueprint and Stacks definitions are available.

## What changed

The assigned node appeared in the shared repository during the initial read, following the landing of its parent Q96 delivery. I then copied that current unsplit node, retaining its prior searches and ancestry. There was no previous item proof, report, citation file or search log in this item's sandbox to resume. The initial four-step draft was revised before delivery to avoid treating the essential image of a subcategory as literally closed under isomorphisms. The final transport argument uses the full subcategories defined by E(K) belonging to the target closure and G(L) belonging to the source closure. It writes the retract equation and the unit isomorphism explicitly. I also expanded the ambient-versus-relative closure argument to check ambient retracts and isomorphisms via thickness and fullness.

There is no STATEMENT-DISPUTED or source correction. Both functors are assumed exact, so the proof needs no extra shift compatibility for the equivalence unit or counit: they are used only as object isomorphisms. The statement and hypotheses are unchanged.

## Review by Q116

I read the worker brief, delivery-errors B through E, the three blueprint levels in SETUP.md, GOAL.md and dag-sync.md. I opened the item's full statement, the unit sk-lem-sf-ctf-generation and its chapter record, the source master blueprint unit proof, and the parent node's comparison steps. This helper realizes the unit's sentence transporting the assertion to the small pro-etale convention; it does not change the flat-model, strata or Kummer route. The node has no blueprint_update replacing this abstract statement. Its historical master source and precise ancestry are retained. Blueprint searches for the ambient comparison, thick closure and equivalence found no blueprint duplicate of this arbitrary-category assertion.

For the definitions I read Stacks derived.tex, Tag 05RB, definition-saturated, and its following discussion, and Tag 05QL, definition-exact-functor-triangulated-categories. Tag 05RB supplies the terminology, not the full closure-transport theorem. The exact strict/retract-closed convention used by this node is the statement of pur9-def-thick, which I read in full, together with def-weil-triangulated-category, whose statement explicitly defines exact functors as additive functors preserving distinguished triangles with a shift comparison. These are the only cited nodes. The proof is marked by agent, rather than claiming that Stacks states this theorem verbatim.

Step 1 uses exactly pur9-def-thick's intersection definition: each supplied thick ambient subcategory is among the subcategories in that intersection. This is the elementary minimality inclusion, and works for an empty generating class.

Step 2 uses pur9-def-thick's listed closure operations and the induced triangulated structures in the hypotheses. I checked both inclusions. Relative thickness follows by restricting ambient operations. For ambient thickness of the relative closure, the two vertices first force the third into the ambient thick subcategory; fullness and the induced structure then make the triangle available internally. An ambient retract first belongs to the subcategory by its thickness, and its two maps belong internally by fullness. Ambient isomorphisms and shifts are handled explicitly as well. No idempotent is split and no reflection-of-triangles theorem is smuggled in.

Step 3 uses the exact-functor clause of def-weil-triangulated-category and the intersection and closure clauses of pur9-def-thick. For the first inverse image, additivity preserves zero, the given comparison preserves shifts, exactness preserves distinguished triangles, and a functor maps ri=1 to E(r)E(i)=1. These are direct defining checks, not an uncited transport theorem. Thus the first inverse image is thick and contains every generator. For the second inverse image the same check uses the assumed exact inverse G; the equivalence unit GE(S) isomorphic to S puts each image generator there. The second minimality inclusion and GE(K) isomorphic to K give the reverse membership implication. No assertion about arbitrary natural transformations commuting with shifts is needed.

Step 4 combines those inclusions and equalities. Both functors restrict, and fullness of the closures lets their unit and counit components restrict; their triangle identities remain the same equations. This is elementary category restriction. No new mathematical fact is taken from the proof of a cited node. citations.json quotes the actual statement text for every use, including the exact-functor clause through the complete ambient-definition quotation.

I checked the empty class, zero subcategory, identity equivalence, full ambient subcategories, a singleton generator and an already existing retract. The empty class requires no choice of a generator; zero is included by the defining convention. In an ambient category with nonsplitting idempotents, only given retract diagrams occur, so the proof remains valid. Fullness and thickness are both used exactly where ambient operations must become internal. Every final proof step is under 2000 characters; no long step hides a comparison lemma. There are no new statement-only nodes, hollow definitions, cycles, weakened clauses or SGA citations.

I retained Q96's historical searches without claiming to have performed them. The fresh Q116 searches were run with msearch.py under this item's id, using both semantic phrasings, Loogle, LeanSearch and source grep, and I read their returned types and the relevant local sources. Generators.lean:132-184 supplies the envelope and minimality, not this restricted ambient-closure equivalence; Adjunction.lean:184-206 supplies exact equivalences, already assumed here. The isEquivalence_ιOfLE_iff hit concerns inclusions and isomorphism closure, not generated ambient closures. Retract-closure hits and metric-thickening hits do not give the item. Two initial grep invocations included an extra Mathlib/ prefix, returned zero hits and are explicitly recorded as not absence evidence; I corrected the subdirectory and read the 21 and 2 returned hits. All services responded. No search was invented and no build tool was used.

## Not duplicates

No new nodes were created. The item remains distinct from pur9-def-thick (definition and minimality), lem-trf-exact-equivalence-inverse (inverse exactness), and lem-sf-generating-class-determination (isomorphism locus of a natural transformation). Its whole abstract closure-transport assertion is proved here rather than moved into a child.

## Unfinished work

None in the one-level split. The server-only check_dag request passed before the last proof-text refinement. The required full delivery dry run follows; no local checker, compiler, Lake, build or shared-repository git command was run.
