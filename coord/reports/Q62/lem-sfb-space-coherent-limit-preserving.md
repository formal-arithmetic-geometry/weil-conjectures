## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-coherent-limit-preserving.json`: split the statement into seven proof steps; retained the statement, its statement dependencies, source, creation metadata, and inherited blueprint chain. Mathlib verdict: no match.
- `citations.json`: twenty entries, one for every step/node pair, quoting the complete statement actually read so that all the relevant hypotheses and conclusions remain visible.
- `searches.jsonl`: the five actual Mathlib queries made in this sandbox, including the second semantic phrasing. Existing searches inherited from the item's creator remain in the item.
- `report.md`: this report and signed review.

## New nodes

None. Zero Mathlib leaves. The relevant general theorems already have DAG nodes, and the argument assembling their clauses belongs in the item.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for coherent families, proper-support descent and limit preservation. There is no exact project declaration of this algebraic-space family statement. Hits about coherent integer tensor families and scheme complexes do not state it. No Lean was written and no compiler or build was run.

## Literature and blueprint

Read `literature/stacks-project/quot.tex`, Situation 08KB (`situation-coherent`, lines 880–900) and Lemma 08KD (`lemma-coherent-limits`, lines 1090–1134). Its three inputs are the limit test for maps to B, module-category continuity, and eventual flatness/proper support. Read the relevant statements in `spaces-limits.tex`: 05N0 (`remark-limit-preserving`, lines 567–581), 07V7 (`lemma-descend-modules-finite-presentation`, lines 2013–2018), 08K0 (`lemma-descend-flat`, lines 1752–1764), 08K2 (`lemma-eventually-proper-support`, lines 3007–3018), and the quasi-compact quasi-separated setup 084W (`situation-descent-property`, lines 1449–1456). Read `spaces-perfect.tex`, 0CZI (`lemma-module-support-proper-over-base`, lines 1031–1045) and 0CZJ (`lemma-base-change-module-support-proper-over-base`, lines 1067–1079).

Read the item's chapter/unit records and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). The item is a supporting coherent-stack input below the existing alteration/stable-moduli chain, not the unit's key statement. Its null blueprint ancestor is inherited: `tools/blueprint_refs.py ancestor lem-sfb-space-coherent-limit-preserving` returns `None`. The existing exact `from.place` and `via` are retained and the split report describes how the supporting input is used.

## Searches and reuse

Searched the whole DAG by Stacks tags 05N0, 07V7, 08K0, 08K2, 08KD and by module/descent/flatness/support concepts, then opened each selected node's statement. Whole-blueprint searches were `coherent limit`, `07V7`, `05N0`, `flat proper support`, and `coherent families`. None is another blueprint statement of this item. The broad semantic blueprint matches concern unrelated coefficient or six-functor constructions.

Reuse is substantive: `lem-sfb-space-fp-module-limit-category` supplies object descent, map descent, eventual equality and preservation of finite presentation; `lem-sfb-space-module-eventually-flat` supplies a tail of flat modules; `lem-sfb-space-module-eventually-proper-support` supplies a stage with proper scheme-theoretic support; and `lem-sfb-space-module-proper-carrier-support` bridges the latter to the carrier convention in this item. Thus no new node for any of these facts was made.

Mathlib searches in the sandbox log used LeanFinder, Loogle, grep, LeanSearch, and a second LeanFinder phrasing. Read the returned signatures. The first semantic search gives scheme-module categorical limits, scheme flatness and a sheaf-pullback finite-limit theorem; Loogle gives presheafed-space colimits; grep gives no hits. The second semantic search and LeanSearch return finite-presentation predicates, local free presentations, scheme descent and structure-sheaf sections. These do not prove continuity of the groupoid on algebraic spaces, even by a one-line specialization. The original item's earlier searches have been retained separately.

## Source error

At `quot.tex` line 1119 the proof writes `X_T = colim X_i`. These objects form an inverse system; the correct identification is `X_T = lim X_i`. For example, the affine inverse system `Spec F_2 -> Spec Z` has inverse limit `Spec F_2`, whereas its categorical colimit is its terminal object `Spec Z`; their point sets differ. The proof's use of 07V7 requires the inverse limit. Step 3 supplies exactly that identification by the existing base-change-of-limits statement. This is a notation correction in the source proof, not a change to the item statement or the unit route.

## What changed and what remains

The imported item had no proof. Wrote all three descent clauses rather than citing them loosely as a categorical colimit. Kept the statement unchanged: no extra separation, noetherianity, finite-presentation condition on the base schemes, or flatness of transitions was introduced. There are no unfinished parts of this one-level split. The existing dependency nodes keep their own independent stage-1/proof status.

## Review by Q62

I checked the item against 08KB/08KD with the source open. The morphism f is finitely presented, B is only locally of finite presentation over S, and T_i are affine in a small nonempty directed system. The item explicitly means a finitely presented quasi-coherent module, base flatness, and proper support. The carrier formulation agrees with the scheme-theoretic formulation by the full statement of `lem-sfb-space-module-proper-carrier-support`, matching 0CZI (2) iff (3). No new statements were created, so there are no new-node sources or unchecked new-node hypotheses.

Step 1 uses the whole conclusion of `lem-sfb-space-module-base-change-flat-proper-support`: its flatness is the same chart-stalk condition as the item's, and its proper support is exactly a proper closed carrier with finite type module. It needs only locally finite type for the source map, which follows here from finite presentation; `lem-sfb-space-flat-proper-fp-locality` expressly preserves finite presentation under arbitrary base change. The formula in `def-sfb-space-module-tensor-composition` is the canonical comparison used for arrows. Associativity and units are checked by that tensor formula, not asserted for an arbitrary choice of comparison.

Step 2 uses `lem-weil-pbc-affine-scheme-qcqs` for the precise source hypotheses of `lem-sfb-lfp-space-scheme-limit-test`. The latter explicitly allows non-quasi-compact and non-quasi-separated B and gives both map descent and eventual equality. It is not a theorem requiring a finitely presented target. Cofinality of a tail is the elementary upper-bound argument written in the step.

Step 3 uses `lem-sfb-space-flat-proper-fp-locality` for finite presentation of each X_i over T_i, then its quasi-compact and quasi-separated meaning. `lem-sfb-space-qcqs-source-products` explicitly gives quasi-separated source over quasi-separated target. Quasi-compactness of X_i is the identity test over the affine T_i; it does not assume X itself is quasi-compact over S or B is quasi-separated. `lem-sfb-space-affine-locality` expressly preserves affine maps under arbitrary base change, and `lem-sfb-space-affine-limits-schematic-stages` gives the displayed base-change formula for the limit, not merely existence of a limit. I applied that formula to the T_i system and W = X_{i_0}. `lem-sfb-space-change-base-to-integers` preserves the products and small etale ringed sites needed to use the two eventual-property nodes, which are stated over Spec Z. Morphism and module properties are unchanged because their chart tests and carriers are the same. The fibre-product reassociations are universal-property identifications.

Step 4 takes object descent and preservation of finite presentation from the actual statement of `lem-sfb-space-fp-module-limit-category`; no part of its proof or a remembered stronger version is used. Its hypotheses are the small directed system, affine transitions and quasi-compact quasi-separated stages established in step 3. The quasi-coherence conclusion is an elementary substitution of the finite free local presentation in `def-trf-space-quasi-coherent-module`, which allows arbitrary small free presentations. This avoids silently assuming that a theorem about all finitely presented modules had asserted a separate quasi-coherent descent clause.

Step 5 checks the hypotheses separately. `lem-sfb-space-module-eventually-flat` requires f_i and M_i finitely presented, affine bases, and a flat limit pullback; those are all present and it gives flatness at every later index. The carrier equivalence requires locally finite type f and finite type M, both consequences of finite presentation here. After applying it to M, `lem-sfb-space-module-eventually-proper-support` applies to M_i without any transition-flatness hypothesis. Applying the carrier equivalence at its later stage gives exactly the finite type carrier module the item requires. Thus the index chosen for proper support is still in the tail of flatness. I specifically avoided the generally false assertion that annihilators commute with arbitrary base change.

Step 6 uses the eventual equality of base maps in `lem-sfb-lfp-space-scheme-limit-test` to put both modules on the same space. It then uses the map and eventual-equality clauses of `lem-sfb-space-fp-module-limit-category` for alpha, its inverse, and the two inverse equations. The latter equations are finite in number, so a common upper bound exists. This proves a stage map really is an isomorphism; merely descending its forward map would not suffice. Step 1 ensures both stage objects keep their flatness and proper support when moving later.

Step 7 uses the same two cited statements solely for base-map equality and module-map equality, respectively. Its final inference is the definition of eventual arrows and the elementary equivalence criterion of full faithfulness plus essential surjectivity. Every proof citation has an entry in citations.json containing a verbatim statement. All statements were read; no definition was substituted for a permanence or descent theorem. Recursive dependency inspection found no selected node depending on this item. The only cited statement from another unit is the existing Mathlib leaf for affine schemes being quasi-compact and quasi-separated, so no undeclared off-route theorem is used.

For small cases, I checked the zero module and an empty X_T (support is empty and is proper), a constant system and a one-element directed system (all constructions specialize to the ordinary identity comparison), and non-Noetherian affine bases (none of the cited continuity/property nodes assumes Noetherianity). Even if a nonempty source system has empty limit, the cited eventual descent/equality clauses handle it without choosing a point of T. Support is only assumed proper, so the argument never requires X_T itself to be proper or separated. No step exceeds 2000 characters; no hidden comparison lemma is moved into a long step. Checks B–E resulted in the explicit carrier bridge, inverse-equation descent, and the inverse-limit correction described above. No statement dispute, SGA source, or route replacement is involved.
