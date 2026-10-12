## What changed
Replaced the sole sorry in Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit with a complete Lean proof from two strict intermediate results: stage representatives of limit classes, and eventual vanishing of stage classes whose images vanish. Both new modules preserve all geometric, boundedness, canonical-map, and diagram compatibility hypotheses. Neither states the original colimit conclusion.

The redundant direct proof import Mathlib.CategoryTheory.Limits.Types.Filtered was
removed in second reading; Grp.FilteredColimits already supplies it transitively.

The combining proof uses subtraction to derive eventual equality, applies Mathlib's Types.FilteredColimit.isColimitOf' to the underlying types, and reflects the colimit back to abelian groups. The proof explicitly shrinks filtered-colimit preservation from universe u+1 to the indexing universe u. No existing signature or definition changed. The original node now records this proof route.

## Proved and sorry left
Proved (relative to the named intermediate statements): AlgebraicGeometry.Etale.nonempty_isColimit_etale_complex_cohomology, node lem-weil-pbc-etale-cohomology-limit-complex-systems. Its complete original signature is preserved, and its body contains no sorry.

Two sorries are split off, each exactly the whole proof of a public theorem:
- AlgebraicGeometry.Etale.exists_etale_complex_class_rep in Sheaf.AlgebraicGeometry.EtaleComplexClassDescent, node lem-weil-pbc-etale-complex-class-descent.
- AlgebraicGeometry.Etale.exists_etale_complex_class_eq_zero in Sheaf.AlgebraicGeometry.EtaleComplexClassVanishing, node lem-weil-pbc-etale-complex-class-vanishing.

These lemmas retain the termwise continuity / finite spectral-sequence route of 0EZM. Their docstrings and nodes give the directed reindexing, termwise comparison, uniform stabilization, finite filtration, and canonical map identification needed by subsequent workers. Zero systems and degrees p<a yield zero classes; a constant singleton system reduces to representation by the same class and vanishing at the identity arrow. The constant degree-a case reduces to the corresponding surjectivity and injectivity halves of sheaf continuity.

Local compilation of all three modules succeeds. The delivery dry run also checks the independent server compilation and the stage-3 preflight. This is a reduction, not an assertion of closure under standard axioms: the original theorem still depends transitively on the two named sorries.

## No longer needed
Removed from the item's direct imports:
- Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes (lem-weil-pbc-etale-cohomology-limit-of-schemes).
- Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence (thm-sp-spectral-object-yields).
- Sheaf.CategoryTheory.HypercohomologyFirstPage (thm-sp-if-e1).
- Sheaf.CategoryTheory.KInjectiveBridge (def-sp-kinjective-bridge).
- Sheaf.CategoryTheory.SpectralSequenceComparison (lem-weil-pbc-complex-spectral-sequence-comparison).
- Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial (lem-weil-pbc-hypercohomology-e1-pullback-functorial).

These remain proof dependencies of the new intermediate items, with their modules imported there. Therefore none is claimed globally pruned from the targets' closure. Also removed from the item's direct proof_deps: def-sp-etale-dictionary and
def-weil-pbc-etale-cohomology. These definitions remain statement dependencies or
proof dependencies of the intermediate nodes; the item's direct proof uses only the two new nodes and Mathlib. The unit sk-prop-h2's statement and route are unchanged.

## Where the brief, the DAG or earlier work was wrong
The earlier ABANDON incorrectly treated missing instantiated spectral-sequence data as an obstruction to delivery. They can be left as strict intermediate statements with complete proof sketches. Also, both sheaf continuity and spectral-sequence comparison are stated for directed preorders, whereas this item's signature allows an arbitrary small cofiltered category. The new intermediate proofs explicitly start with lem-weil-pbc-filtered-category-directed-cofinal (Tag 0032).

The source text is absent from this read-only clone. Checked the official Stacks page https://stacks.math.columbia.edu/tag/0EZM against the recorded node proof; its finite-term argument is the route followed here. The new nodes expand its omitted details rather than invoking the parent theorem circularly. Searches of the imported blueprint for hypercohomology, 0EZM, class representatives, and eventual vanishing found no existing statement of either new half. LeanSearch returned HTTP 500 and is recorded as unavailable; LeanFinder and source grep yielded no exact matching theorem.

## New nodes
lem-weil-pbc-etale-complex-class-descent: the surjectivity half of the finite abutment comparison, stated as an actual stage representative under precisely the canonical cocone equations. Module lean/Sheaf/AlgebraicGeometry/EtaleComplexClassDescent.lean.

lem-weil-pbc-etale-complex-class-vanishing: the injectivity half, stated as eventual zero of a stage element. The main proof converts it into eventual equality by applying it to x-y. Module lean/Sheaf/AlgebraicGeometry/EtaleComplexClassVanishing.lean.

No change record is required: existing public signatures, public imports, and definitions are unchanged; new modules are imported only for proofs.


## Second reading by R1

1. Compared the delivered main module with the repository using diff and compared
   its entire theorem signature as bytes. Verdict: unchanged, including all
   geometric, boundedness, transition, canonical-map and cocone equations; the
   four public imports and all existing definitions and docstrings are unchanged.
   The only existing node fields changed are proof, proof_deps and proof_origin.
2. Compiled all three modules locally in import order and compiled a scratch copy
   with #print axioms for all three declarations. Verdict: no errors or warnings;
   the axiom sets are exactly propext, Classical.choice, Quot.sound and sorryAx.
   The only direct sorries are the two reported public intermediate theorems,
   each with a node and source/proof docstring. No prohibited declarations or
   hollow definitions occur. The main result is a reduction, not yet a theorem
   closed under the three standard axioms alone.
3. Read both new statements, their complete hypotheses, docstrings and nodes,
   the imported continuity and spectral-sequence comparison statements, and
   the official Stacks proof https://stacks.math.columbia.edu/tag/0EZM.
   Verdict: the representative and eventual-zero statements are strict parts
   of the argument; neither states the original colimit universal property.
   Empty indexing is excluded by IsCofiltered. Zero complexes and p<a have zero
   abutments, with any stage representing zero and the identity arrow witnessing
   vanishing. A singleton system has identity transitions and reduces to the
   same class and identity zero witness. Complexes concentrated in degree a
   reduce to the two halves of ordinary sheaf continuity. No extra assumption
   on transition injectivity or surjectivity is used.
   Searched with independent wording via msearch LeanFinder (derived global
   sections, surjective/injective canonical comparison), Loogle
   (Types.FilteredColimit), Mathlib grep and repository rg. The hits supply the
   generic filtered-colimit criterion and structure-sheaf section vanishing,
   not these varying-site complex results. The existing spectral comparison
   requires spectral-sequence/filtration data that these hypotheses must still
   construct; neither split theorem can be closed in a short proof from it.
4. Checked the subtraction argument, the same-stage eventual-equality condition,
   the universe shrink for preservation and colimit reflection. Verdict: the
   Mathlib route is direct and sound. Removed the redundant direct proof import
   Mathlib.CategoryTheory.Limits.Types.Filtered; the file still compiles because
   Grp.FilteredColimits imports it transitively. Completed No longer needed with
   the two old proof-dependency IDs that had only been mentioned descriptively.
   All eight old direct proof dependencies remain on the intermediate route;
   no module is claimed globally pruned. Read dag/units/sk-prop-h2.json: its
   Kummer route and all realized fields are unchanged, with no unit bypass.
5. Checked the nodes against Lean: the main proof uses precisely the two new
   nodes, and each new proof_deps is the union of its proof steps' uses. New
   nodes have the required source, searches, origin, created record, ancestor,
   chapter/unit and Lean record. Verdict: consistent. Corrected stale step
   references after the added reindexing step. Expanded the new docstrings and
   nodes to explain transport from an arbitrary original stage into the directed
   cofinal system and composition of a later zero witness back to the original
   category. No theorem statement or proof body was changed in second reading.

Second-reading changes: one redundant proof import removed; pruning report
completed; cofinal-witness proof explanations and node step numbering repaired.
