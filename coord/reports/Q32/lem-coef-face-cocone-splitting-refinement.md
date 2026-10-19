# Q32 — lem-coef-face-cocone-splitting-refinement

## Files written

- `dag/nodes/sec-six-functors/lem-coef-face-cocone-splitting-refinement.json`: statement, now split into five explicit elementary steps. Statement unchanged; no exact project attachment and no Mathlib match.
- `citations.json`: verbatim statement excerpts for the two citations in each of Steps 1 and 3.
- `searches.jsonl`: four actual item searches, with the returned records preserved in the item. The four inherited Q119 searches and their results were retained and read.
- `check_cases.py`, `small-cases.txt`: finite mathematical sanity check; these are sandbox support files, not new DAG nodes.
- `write_split.py`: sandbox-only writer; `report.md`: this report.

No new nodes or Mathlib leaves. No unit record changed: this auxiliary item is not the unit's key statement.

## Attachments

None. Searched the whole read-only `WeilConjectures/` tree of `/home/ubuntu/weil-src-slopmaster2` for the exact id, face-cocone/admissible-splitting terms and simplicial-thickening/rigidification terms. There is no declaration stating this item. The matches for rigidification concern Picard normalization or Artin–Schreier sheaves, not subset flags. No master sorry declaration was treated as a proof.

## Wanted literature

WANTED: Jacob Lurie, Higher Topos Theory, https://people.math.harvard.edu/~lurie/papers/HTT.pdf, archival copy in `literature/`, Definitions 1.1.5.1 and 1.1.5.3 (printed pp.20–22) and proof of Theorem 2.2.5.1 (printed p.90), for lem-coef-face-cocone-splitting-refinement. Read these places online from the official PDF on 2026-10-17. No document was downloaded or added to the shared repository. The refinement proof is an agent-written expansion, not a theorem claimed to appear verbatim in HTT.

## Findings and changes

The imported item is true as stated. Its proof was empty. Its source pointed only at the boundary-cube application; I added the precise simplex-model definitions to the source place, while retaining that application and the archival request. There is no STATEMENT-DISPUTED and no changed hypothesis or conclusion.

The last sentence about the canonical splitting is conditional on having an admissible splitting. If the family contains only singletons and i<j, there is no admissible splitting; the proof does not manufacture one. Inserting a vertex not in S_0 would fail to give the claimed strict union factorization, but the statement explicitly requires all inserted vertices to be in S_0.

No new node is needed for one insertion, finite induction, or the canonical common refinement: they are short arguments from the union model, functor axiom and the given compatibility and closure conditions. They are written as steps rather than renamed clauses. No statement or proof of the already reviewed parent is edited.

The blueprint search `tools/blueprint_refs.py search 'face cocone'` returned zero blueprint nodes. The broader 'splitting' and 'subset' searches, DAG keyword matches and statements of the nearby coherent-realization bead-normal-form, ordered-simplex-cone-evaluation, cofibrant-subset-colimit-decomposition and poset-relative-vertex-insertion nodes do not state this result. The simplex-model and simplicial-category nodes already exist and suffice. The current main-20261015 integral-exceptional-adjoint statement and proof were read at `sec-six-functors/sk-thm-sf-package/`; they retain the coefficient-adjunction paragraph recorded in the inherited ancestry. This item realizes the single-insertion calculation extracted from former Step 4 of the boundary-cube parent, within that existing route. No SGA source or purity-route replacement is used.

Mathlib: ran leanfinder for the whole refinement statement, leansearch for the single-cut flag factorization (a second semantic phrasing), loogle for `"SimplicialThickening", "comp"`, and grep for `SimplicialThickening|face.*cocone|splitting.*refin` under AlgebraicTopology. Every service succeeded and every returned signature was read. Read `Mathlib/AlgebraicTopology/SimplicialNerve.lean:54–208` and `Mathlib/CategoryTheory/Enriched/Basic.lean:299–310`. These give union composition, image functors and the enriched functor axiom; they do not state the compatible-family refinement theorem. The remaining semantic hits concern simplex-category generators or pointed Kan-simplex multiplication. None is a one-line specialization proving all clauses of the item.

## Review by Q32

I read the source for the item in the official HTT PDF: Definition 1.1.5.1 really uses the nerve of endpoint-containing subsets and union composition, and Definition 1.1.5.3 makes a face inclusion act by the same subsets. The first paragraph of the proof of Theorem 2.2.5.1 is the boundary-cube application, whose face-cocone details this item expands. There are no new nodes needing separate sources. The proof_origin correctly says agent because I supplied this refinement calculation. I also read the chapter and unit records, SETUP's three route levels, GOAL, dag-sync, the worker/stage-1 rules and delivery-errors B–E.

For Step 1 I opened the full statements of lem-coef-pinched-cube-latching and lem-coef-simplicial-interval-lifting. The former states the mapping-poset model; the latter explicitly supplies associative unital simplicial composition. The endpoint containment follows from R⊆S_0⊆S_t, and singleton face compatibility, a hypothesis of this item, identifies all endpoint objects. Thus the flag images have the types that the composite requires. Neither model structure, latching monicity nor a colimit theorem is taken from those nodes.

For Step 2 no external statement is used: a new interval cannot cross an old cut because the new splitting contains the old one. Its support is a nonempty subset of an old support, so exactly the stated downward-closure hypothesis applies. Endpoints are still in S_q. This works for nonconsecutive ambient vertices and intervals with no interior vertices.

For Step 3 I rechecked the same two cited statements. The restricted flags share the cut c in every entry because c∈S_0, and the explicit union equality reconstructs every entry of the old flag. The cited union composition therefore reconstructs that entire nerve simplex. The only passage to D is the defining composition-preserving axiom of the enriched functor f_T, plus strict cocone compatibility for T^-⊆T and T^+⊆T, which are hypotheses of the item. I wrote out that equation; no uncited homotopy-coherence, comparison or normal-form theorem is being used. The target's associativity, stated by the interval node, replaces the one old factor with the two new factors in the ordered composite. These two citations are backed by verbatim excerpts in citations.json, as are the two in Step 1.

Step 4 explicitly sets up induction on the finite difference, with the zero case and one-vertex reduction. Step 5 applies the proved refinement statement to S_0 and compares both admissible splittings with that same canonical value. Both steps use only the previous steps and elementary finite-set reasoning. Every step is marked elementary because each is the displayed set calculation or an immediate definition/axiom application, or a finite induction on that calculation. No step has more than 2000 characters (the largest has 1102), and none hides a separate standard lemma.

I checked delivery-errors B1–B10: there are no new statement-only nodes or new notions, no unrun search, no unsupported leaf or attachment, and no missing blueprint place. For C1–C8 I checked each use against the cited statement rather than its proof; the dependencies are precisely the two definition-bearing nodes already in stmt_deps, in the same unit, with no new back edge or off-unit tool use. For D1–D5 the steps carry the argument, including the single insertion and the induction, instead of moving clauses to children or treating a source reference as a proof. For E1–E7 I checked all hypotheses, object endpoints and degrees, strict equality rather than homotopy, nonempty supports, and the full finite-family quantifiers; no source correction or statement dispute arose.

My finite enumeration checked every downward-closed face family containing singletons for |V|=1,2,3,4, every endpoint pair, every weak flag in degrees q=0,1,2, and every admissible splitting: 126 families, 2720 admissible splittings, 3050 refinements, and 327 single insertions. It found no failure of support admissibility or the entrywise union identity. This includes the degenerate/repeated flags, q=0, full and sparse face families, and the singleton-ambient case (no endpoint pair). The arbitrary-D equality is justified by the functor axiom in the proof, not asserted on the strength of the enumeration.

## Unfinished work

None in this one-level split. The two existing definition-bearing dependencies keep their own work states. No Lean file was written and no compiler, Lake or build tool was run.
