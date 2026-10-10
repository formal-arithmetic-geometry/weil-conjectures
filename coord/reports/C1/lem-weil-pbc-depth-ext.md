# Worker report: lem-weil-pbc-depth-ext

1. Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-depth-ext.json`: split into five source-based proof steps; status `split`; blueprint ancestry and split report recorded.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-ext-annihilated-by-first-argument.json`: new Mathlib leaf for Stacks 00LV, matched by `CategoryTheory.Abelian.Ext.postcomp_smul_id_eq_zero_of_mem_annihilator` (`Mathlib/Algebra/Category/ModuleCat/Ext/Basic.lean:35`); blueprint ancestry recorded.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-ext-zero-hom.json`: new Mathlib leaf for zeroth Ext as Hom (Stacks 00LO), matched by `CategoryTheory.Abelian.Ext.addEquiv₀` (`Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean:317`); blueprint ancestry recorded.

2. Attachments:

- `CategoryTheory.Abelian.Ext.postcomp_smul_id_eq_zero_of_mem_annihilator` belongs to `lem-weil-pbc-ext-annihilated-by-first-argument`.
- `CategoryTheory.Abelian.Ext.addEquiv₀` belongs to `lem-weil-pbc-ext-zero-hom`.

3. WANTED:

- None. Stacks source was read from `/tmp/c1-lead-current/literature/stacks-project/algebra.tex`; the nodes cite the repository path `literature/stacks-project/algebra.tex`.

4. What was wrong in the prior split / blueprint:

- The item was unsplit despite having a complete argument in Stacks Tag 00LW. It now records: finite depth, the degree-zero Hom/associated-prime equivalence, reduction by the first element of a maximal-length regular sequence, with quotient depth computed directly from the definition, the long exact Ext sequence (00LU), vanishing of the scalar maps (00LV), and the induction proving the first nonzero Ext degree.
- The prior proof used `lem-weil-pbc-depth-drops-by-one`, whose source proves it via depth-in-ses and hence this very item. Removed that edge: taking the first element of a maximal regular sequence gives quotient depth exactly d-1 by tail and prepending arguments, both written explicitly in step 3. This follows the chosen-element assertion of 00LW and requires no independent depth-drop theorem.
- The degree-zero argument now cites the separate `Ext⁰ ≅ Hom` Mathlib leaf. Step 4 attributes `Ext⁰_R(κ,M)=0` to Step 2, as required for positive depth.

5. What I could not finish:

- No Lean was written or built (stage 1). The pinned Mathlib has no depth definition or exact depth–Ext theorem; `ModuleCat.exists_isRegular_tfae` in `RingTheory/Depth/Rees.lean` is only a multi-step candidate, so the item remains a statement node rather than a Mathlib leaf.

## Searches and checks

- `tools/check_dag.py`: DAG-wide reach warnings pre-existing in unrelated constructible nodes; no cycles.
- `tools/review_split.py lem-weil-pbc-depth-ext`: PASS.
- LeanSearch, LeanFinder, Loogle, and Mathlib grep were run for depth–Ext, nonzerodivisor/associated-prime, Ext annihilation, and zeroth Ext. The two exact pinned-Mathlib matches are recorded in their leaves; depth–Ext itself has no pinned-Mathlib match.
- Searched the DAG by the Stacks tags 00LW, 00LV and 00LO, the names of the Ext declarations, and the depth/Ext concepts. No same-statement node was found for either leaf. The blueprint fields trace both leaves through this item and `lem-weil-pbc-depth-in-ses` to Step 7 of `thm-weil-pbc-finite-etale-lifting` (Stacks 0GS2, essential-surjectivity paragraphs); the full intervening DAG chain is recorded in each node's `blueprint.from.via`.

## Mathematical checks

## Review by C1

I read Algebra 00LW (`lemma-depth-ext`), 00LL, 00LU, 00LV, 00LK, 00KQ, and Definitions 00LF/00LI in `literature/stacks-project/algebra.tex`. The item states precisely the first-nonzero-Ext characterization for a nonzero finite module over a Noetherian local ring. Step 1 uses the support-dimension and finite-local-dimension nodes to bound depth; Step 2 uses the zeroth-Ext/Hom leaf and associated-prime nonzerodivisor node for the base case; Step 3 chooses the first member of a maximal regular sequence and checks both directions of the quotient-depth equality by tail and prepend arguments. This removes the old circular use of the depth-drop item. Step 4 cites the long exact Ext and annihilation leaves to obtain the short exact sequences. Step 5 performs induction; at d=1, Step 2 gives Ext^0(k,M)=0 and the induction hypothesis gives Ext^0(k,Q) nonzero, so Ext^1(k,M) is nonzero.

I read pinned Mathlib `Algebra/Homology/DerivedCategory/Ext/Basic.lean:315-319` and `Algebra/Category/ModuleCat/Ext/Basic.lean:29-43`; the new leaves are exact one-declaration matches for Ext^0=Hom and annihilation of Ext by an element killing its first argument. Each leaf is self-contained, cites `def-pc-ext`, has source labels, search records, and a checked blueprint chain. Searches of the current DAG and imported blueprint found no duplicate. I tested the field/nonzero-vector-space depth-zero case and the DVR depth-one case; zero M is excluded and Nakayama handles quotient nonzeroness. The worker revised the draft to remove the cycle, added the missing Ext^0 leaf, fixed the Step 4 attribution, and recorded the blueprint ancestry. `review_split.py` passes; `check_dag.py` has no cycles and seven unrelated existing reach warnings. Sections A-E of `coord/delivery-errors.md` are satisfied.

## Worker mathematical checks

Read Stacks 00LW, 00LL, 00LV and the degree-zero Ext identification in 00LO from `/tmp/c1-lead-current/literature/stacks-project/algebra.tex`; read both cited finite-dimension/support-depth node statements and both Mathlib leaf declarations. For a field and nonzero finite vector space, d=0 and Hom is nonzero. For a DVR with M=R, the quotient k has depth 0 and the degree-0 exact segment identifies Hom(k,k) with Ext^1(k,R). At d=1, the range j<d-1 is empty: Step 2 gives Ext^0(k,M)=0, while induction on the depth-zero quotient gives Ext^0(k,Q)≠0, so the Step 4 short exact sequence gives Ext^1(k,M)≠0. The zero module is excluded by the theorem hypotheses; Nakayama ensures the quotient modules in the induction are nonzero. Both new nodes are Mathlib leaves; no new unsplit node was needed.
