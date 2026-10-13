## What changed

Proved `Algebra.isGlobalCompleteIntersection_localizationAway` with the original signature.
Mathlib's presentation API supplies the one-variable, one-relation localization presentation,
its composition with the polynomial quotient presentation, and its quotient equivalence.
The dimension proof uses the principal localization open embedding, the spectrum
homeomorphism of the original algebra equivalence, and the existing equidimensionality
lemma. Added the proof-only import `Mathlib.RingTheory.Extension.Presentation.Basic`.
Updated the item's DAG proof to match this implementation.

## Proved and sorry left

Closed: `Algebra.isGlobalCompleteIntersection_localizationAway`
(node `lem-weil-pbc-global-complete-intersection-principal-localization`).
One of one original holes closed; zero holes added; no sorry left in this delivery.
This is a proof from existing declarations, not a decomposition into new statements.

The proof handles a zero localization before assuming nontriviality, and a zero source
cannot occur in the remaining branch. Empty generator/relation families and c = n are
covered by the uniform presentation composition and natural subtraction identity.
Compilation with lcompile.py passes with no warnings.

## No longer needed

Removed import `Sheaf.Topology.DimensionSupremumLocalDimensions` and dependency node
`lem-weil-pbc-dimension-supremum-local-dimensions`; that module is not needed by this proof.
Also removed proof dependency `lem-weil-pbc-dimension-at-point-open-subspace`.
The range of the localization open embedding itself is an open neighborhood, so the
infimum defining local dimension gives the lower bound directly. No transport of local
point dimensions is needed. The module `WeilConjectures.Mathlib.Topology.KrullDimension`
stays needed for dimension at a point and the embedding/range dimension equality.
The coefficient kernel and polynomial localization quotient dependencies remain embodied
in Mathlib's proved presentation composition/localization constructors; no new lemmas
or modules are needed for those calculations.

## Where the brief, the DAG or earlier work was wrong

No statement or definition error found. The original plan's dimension argument was
longer than necessary, and Mathlib already provides the presentation composition and
reindexing machinery for the algebra step. The unit's realized statement and proof steps
are not bypassed: this item is below that level.

Searches: msearch leanfinder for principal localization of global complete intersections;
msearch loogle for Algebra.Presentation.comp; msearch grep for localizationAway; direct
rg on both library roots and pinned Mathlib. No existing theorem directly states this
result. The related PrincipalLocalizationCI proof confirmed the elementary open-range
dimension argument; its module is not imported, because its relative fibre theory is
not required here.

## Second reading by T1

1. PASS: Compared the complete delivered module with the repository by diff and checked
   the theorem signature byte for byte. The signature and all definitions are unchanged;
   no target statement or public import changed. Only the theorem proof, its explanatory
   proof paragraph, and private proof imports differ. There are no new declarations.
2. PASS: Compiled the delivered module through lcompile.py with no errors or warnings.
   Scanned for sorry and forbidden declarations/options: none occur in the delivered module.
   A scratch-copy `#print axioms Algebra.isGlobalCompleteIntersection_localizationAway`
   reports propext, Classical.choice, Quot.sound, and sorryAx. The remaining sorryAx is
   inherited from the existing equidimensionality dependency, not added by this delivery;
   this closes the item's hole conditionally on the existing lower statements, and does
   not certify the target import closure as axiom-free. The zero ring, zero localization,
   empty relation/variable families and c = n require no extra hypotheses. No arbitrary
   data is chosen from an unproved existence statement: the presentation is constructed
   by Mathlib, and the hypothesis supplies the original quotient equivalence.
3. PASS (vacuous for splits): Zero statements split off and zero new holes. Independently
   searched library sources for complete-intersection localization and Mathlib via msearch
   grep and loogle (including Presentation.reindex). No shorter existing theorem replaces
   the proof. Read Presentation.comp's kernel calculation: its auxiliary kernel uses
   MvPolynomial.ker_mapAlgHom; localizationAway uses the localization quotient kernel.
4. PASS: Reviewed from the target downward. The presentation composition/reindexing and
   the two dimension inequalities directly prove the original conclusion. The open range
   is a neighborhood of the selected spectrum point, so iInf₂_le suffices for the lower
   bound without transporting local dimension. The two retired dimension dependencies
   are both listed under No longer needed. Remaining imports support the statement or
   the used presentation/equidimensionality/dimension API. Checked sk-thm-p1.json realized:
   this item is below its realized unit statements and steps; its route is preserved.
5. PASS: Compared the node with the repository: only proof, proof_deps and proof_origin
   change. proof_deps is exactly the union of proof-step uses. The retained coefficient
   kernel and localization quotient Mathlib leaves occur in the presentation API's proof.
   Node statement, Lean statement record, source, chapter and unit are unchanged; no
   new node or change record is needed.

Second reading changed only this report: added the five review verdicts and clarified
that the closed proof still inherits sorryAx from existing lower dimension results.
The Lean proof and DAG update were correct and were retained.
