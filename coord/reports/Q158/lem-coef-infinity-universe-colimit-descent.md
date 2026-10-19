## Files written

- dag/nodes/sec-six-functors/lem-coef-infinity-universe-colimit-descent.json: statement, split in five steps; no Mathlib match for coherent colimits of spaces.
- citations.json: verbatim statement excerpts for every proof-step citation.
- No new nodes or Mathlib leaves.

## Attachments

None. Searched /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint id and universe/colimit terminology; the only broad hit concerned ordinary transfinite sheafification, not this statement. Also checked the exact upstream master source read-only, without treating its sorry declarations as finished proofs.

## Sources and wanted material

Read the current item and the main-20261015 ancestor prop-coef-integral-exceptional-adjoint.proof.md, paragraph beginning “For K” and the displayed derived mapping-complex adjunction. This is a foundational lemma extracted many levels below that paragraph, rather than a theorem stated in the blueprint. Read the chapter record sec-six-functors, the unit record sk-prop-sf-biduality-general, SETUP's three levels and tool-lemma rule, GOAL, dag-sync, and delivery-errors B-E. Read Scholze, Six-Functor Formalisms, Lecture II, printed pp.13-15, especially basic facts (2)-(3) on the homotopy category and inverse witnesses. Read the full statements of all three proof dependencies and both statement-definition dependencies. The proof is agent-written from these statements; no SGA route is used.

WANTED: Lurie, Higher Topos Theory, Sections 1.2.10-1.2.12 and 4.2.4, for the item's original background reference; it is not archived in literature/. The proof does not pretend this reference itself states the present universe lemma. All substantive inputs are existing DAG statements.

## What changed and what was wrong

The inherited node had a correct statement and an empty proof. Its existence/preservation input was already a DAG node; no extra general reflection lemma is needed, since the inverse can be lifted in three lines on components of mapping spaces. Preserved the statement, statement dependencies, citations/search records inherited with the node, and the exact historical blueprint ancestry. Added five proof steps, the corresponding proof dependency union, agent proof provenance, and the off-unit generic cocone-calculus tool declaration in split_report.tool_uses. There is no statement dispute, target change, coefficient-category identification, or base-change-morphism change.

The interrupted attempt left only brief markers in this sandbox and no item, report, search log or running Q158 delivery process. Accordingly there was no completed mutation to repeat. This resumed turn accidentally ran a read-only git status in the shared checkout while inspecting state; it made no change. No further direct git command was run, and all written artifacts are confined to the assigned sandbox.

## Mathlib and duplicate searches

Ran the four logged msearch.py searches in searches.jsonl and read their hits. LeanFinder and LeanSearch use different phrasings: general fully faithful infinity-functor reflection, and the universe inclusion of Kan complexes. Loogle found CategoryTheory.Limits.fullyFaithful_reflectsColimits; grep found it at Mathlib/CategoryTheory/Limits/Preserves/Basic.lean:806 and Functor.FullyFaithful.reflectsIsomorphisms at CategoryTheory/Functor/ReflectsIso/Basic.lean:53. Read the surrounding source, including Basic.lean:805-817 and ReflectsIso/Basic.lean:49-60: they require ordinary Category instances and ordinary Cocone/IsColimit. They are useful analogies, not one-line specializations to coherent diagrams indexed by arbitrary simplicial sets in quasicategories. Read AlgebraicTopology/Quasicategory/Basic.lean:32-45: it defines the horn condition and does not give this result. Retained inherited searches without claiming to have rerun them.

Searched the whole DAG for universe inclusion, colimit uniqueness, reflection of equivalences and initial objects; ran blueprint_refs ancestor and searches for “universe colimit descent”, “initial objects”, “fully faithful”, and “universe”. Used lem-coef-spaces-small-colimits-universe and lem-cbc-enhanced-functor-cone-calculus already present; no duplicate node was created. The former supplies preservation, while this item adds reflection for the specified cocone. The full-essential-image equivalence is stronger machinery than the elementary inverse argument needs and was not cited.

## Review by Q158

I checked the unchanged statement clause by clause: I is U-small (including empty), both Q and M are small spaces, the assumed larger colimit is the image of the given cocone, and the conclusion concerns that cocone and every induced comparison. The ambient universe is kept distinct from the index universe. No existence theorem for merely small diagrams is applied to a larger index.

Step 1 uses exactly the existence, actual-cocone preservation, and universe-inclusion clauses in lem-coef-spaces-small-colimits-universe. I opened its entire statement and checked all three hypotheses: small shape, coherent small-valued diagram, and small apex. This does not assume descent, and does not cite its proof.

Step 2 uses the definition of initial colimit cocones in def-cbc-enhanced-diagrams-cones. Its contractible mapping space is nonempty, so a comparison is a cocone morphism, including the compatibility homotopy, not an arbitrary apex map. This is an elementary use of the definition and works for any choice of comparison.

Step 3 uses full faithfulness from spaces-small-colimits-universe and the mapping-space/full-faithfulness/equivalence definitions in enhanced-diagrams-cones. A weak equivalence of Kan mapping spaces gives a bijection on components. Surjectivity lifts an inverse component; injectivity on the two endomorphism spaces gives both inverse equations. Scholze p.14 explains why these equations are precisely the equivalence criterion. This three-line inverse argument is elementary from the cited definitions and not a hidden lemma. Preservation just applies the functor to the inverse and its witnesses. This clause holds even without the larger-colimit hypothesis.

Step 4 uses the cocone/initial-object calculus in lem-cbc-enhanced-functor-cone-calculus. Its statement explicitly includes dual cocones, initial objects and their contractible full subcategory, and applies to arbitrary shapes. Both cocones are initial by step 1 and the hypothesis. I wrote out the backward cocone arrow and both endomorphism homotopies, then evaluated at the apex. Thus the image of the actual comparison, not some unrelated map Q to M, is invertible. Step 3 reflects it.

Step 5 uses the same node's dual mapping-space criterion. Its displayed composite is identified with the universal-arrow map for lambda by the compatibility from step 2. The inverse to alpha gives an explicit inverse on mapping spaces, so no unsupported “transport of colimits” theorem is assumed. The mu factor is an equivalence because mu is a colimit. Therefore the criterion applies for every small test Y and proves exactly the original lambda colimiting.

I tested I empty (Q the empty space; no vertex or nonempty-shape assumption appears), I a point (the comparison is the cocone's apex map), and a discrete two-point shape (the construction compares the coproduct cocones). The inverse-lifting argument also works for empty mapping spaces whenever an image inverse exists: surjectivity then forces a source component. I checked that the non-elementary steps are all below 2000 characters and hide no auxiliary comparison theorem. Every non-elementary input is an existing cited statement, quotes are verbatim, and the only off-unit statement is explicitly declared as a generic tool. There are no new statements to test, no node-sized clause moved into a new name, no circular dependence introduced by the argument, and no unresolved mathematical defect.

## Unfinished work

None in the stage-1 split. Mechanical validation and delivery are run with the required server-side delivery tool; no local DAG checker, compiler, Lean or Lake command is used.
