# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-qcqs-constructible-integral-lattice-tree.json: item, statement, split; no Mathlib match.
- citations.json: eleven step/node entries, each quoting the cited statement verbatim.
- report.md: this report. searches.jsonl is the unmodified output log of the required search command.

New nodes: 0. New Mathlib leaves: 0. No unit file changed: this item is not its unit's key statement.

## Attachments

None. Searched the current lean/WeilConjectures/ for the exact blueprint tag and item id, integral-lattice and refinement-tree terminology, and lisse/constructible declarations in the pro-étale adic source. The lattice hits concern adic coefficient limits, algebraic lattices and coherent ideals, not both clauses of this assertion for ordinary internal modules and the finite-subextension condensed algebraic-closure coefficient. No complete project declaration stating the item was found.

## WANTED

None. All sources needed for this assembly are present. The proof is marked agent-written because the blueprint is agent-written and Stacks 09Y4 states the topological refinement, while the stronger scheme-theoretic refinement and coefficient assembly are reused as DAG statements.

## Findings and corrections

The item was unsplit and its proof empty; no earlier sandbox item, report or search log existed. No repair note was present. The item statement is unchanged: its moreover clause assumes integral models on finite partitions; it does not construct those models or assert a global lattice. In particular, I did not apply the Noetherian stratified-lattice theorem to a general qcqs scheme, and did not replace the finite-subextension coefficient ring by all norm-continuous algebraic-closure-valued functions.

The source's discussion of the lattice construction is only context here. The actual refinement theorem already exists as lem-fix-constructible-open-closed-refinement. I reused its statement, including actual morphisms through original strata, rather than replacing it by set containment or creating another refinement lemma. The root's inherited chapter/unit metadata are preserved, although the compactification-coherence unit comes from the older smooth-purity organization while this descendant lives in six-functors-basics. The split stays on the inherited closed-complement generation route and declares its geometric and coefficient tools explicitly.

The preliminary scalar algebra is written out rather than hidden in the word lisse: evaluate the coefficient ring at a point, then use Gaussian elimination on each finite scalar presentation to get a finite free sheaf cokernel. This works for E and Omega alike, because both scalar rings are fields. It asserts no descent of an arbitrary transition map to a finite coefficient field.

## Unfinished work

None for stage 1. No Lean was written, no compiler or Lake was run, and no repository or launcher file was changed. The subsequent statement/proof formalizations remain outside this delivery's scope.

## Search results and reuse

Read the item's five inherited search records and retained them verbatim. For the current conditional statement I additionally ran two distinct LeanFinder phrasings, LeanSearch, Loogle and grep using msearch.py. All five commands succeeded. I read every returned signature: the hits were finite open subcovers, constructible image/preimage theorems, finite-presentation morphisms, general sheaf pullback or finite-type generators. None states this tree refinement with actual factoring morphisms and ordinary coefficient-lattice isomorphisms. The exact command queries and returned summaries/digests are recorded in the item's mathlib_searches and in searches.jsonl. These are not claims that ordinary pullback itself is absent from Mathlib.

Searched the whole DAG for binary/refinement trees, lattice pullback, constructible strata and scalar pullback; searched the whole blueprint with blueprint_refs.py for open closed refinement, lattice, lattice pullback and refinement, and used its ancestor command. The exact geometric input is already in the DAG. The narrower lem-sfb-lattice-pullback has continuous section-ring coefficients, an inclusion and an E-valued rationalization; it was not used as if it covered the finite-subextension algebraic closure coefficient. Instead the proof cites the general internal inverse-image/extension statement.

## Not duplicates

No new nodes were created. The existing geometric refinement, arbitrary condensed-ring local-free pullback, and internal scalar-extension comparison cover the required tools. This item's first clause combines the geometric tree with lisse restrictions, and its second clause assembles the given lattice data after further leaf refinement; it is not an exact attachment to the geometric theorem alone.

## Review by Q21

I read the current item, chapter sec-six-functors-basics, the full unit sk-prop-sf-comp-coherence, the stratified-lattice proof in main-20261015, the constructibility definition and scalar-model proof, the cartesian-coefficients proof, and Stacks topology.tex Tag 09Y4 (lemma-constructible-partition-refined-by-stratification). I also read sites-modules.tex Tag 03DO (lemma-local-pullback) and Tag 03EL (lemma-tensor-product-pullback). The source's trace argument produces lattices only after stratification; this item conditionally refines such data, so no trace, finite étale stratification or lattice-existence lemma is silently assumed.

For step 1, I opened sk-def-sfb-constructible and sk-def-sfb-qlbar-condensed. The former gives finite constructible locally closed strata and presentations by finite matrices of actual scalar entries; the latter gives the point scalar ring Omega, because every algebraic element has finite degree. For underline E the scalar ring is E by its explicit continuous-function definition in the item. I checked the finite Gaussian-elimination induction and the cokernel of the resulting identity/zero block. The basis changes act through the same scalar action as the original matrix and remain inverse, so the resulting sheaf cokernel is a finite free regular module. This is elementary finite-matrix algebra inside the step, not a new theorem or an invocation of a nonconstant sheaf-matrix reduction.

For step 2, I opened lem-fix-constructible-open-closed-refinement in full. Its statement assumes exactly qcqs root plus finite constructible locally closed strata; it explicitly provides qcqs vertices, quasi-compact edges, complementary binary splits, covering/disjoint leaves and a morphism through one original stratum. I do not borrow the proof's construction without its statement. I opened sk-def-sfb-module-pushforward-pullback for the composition isomorphism and lem-weil-pbc-continuous-locally-free-pullback for arbitrary condensed-ring coefficients. Its statement explicitly allows any scheme morphism and varying finite ranks, with no Noetherian, etaleness or field-degree assumption. Thus it applies to the actual factoring morphism and both rational coefficients of this item.

For step 3, the same refinement statement applies on each old leaf because every such leaf is qcqs by the given tree and each supplied partition is finite constructible locally closed. It retains the original stratum scheme structures. I checked that no reduced structure, scheme-theoretic containment inferred from set containment, or unstated finiteness of the stratum immersion is being substituted.

Step 4 is finite-tree grafting with no cited mathematical theorem: retain original internal vertices and replace old tips with the corresponding finite trees. Finiteness is the finite sum of their vertex counts, and every new split was already one of the valid splits. Coverage and disjointness follow separately within each old leaf and between distinct old leaves. Local closedness is preserved by composing the open/closed immersions along the path. There is no induction assuming the conclusion, and no new category-theoretic colimit or smallness hypothesis.

For step 5, I opened all five cited statements. The local-free pullback theorem gives lisse B_W for the integral condensed ring A_F without restricting the scheme. lem-sfb-internal-extension-inverse-image states precisely the ordinary, uncompleted internal module isomorphism for arbitrary commutative ring objects R and S and any scheme map; it does not require flatness or a completed tensor. sk-prop-sfb-cartesian-coefficients supplies the untwisted ring isomorphisms for O_F and the selected rational coefficient, with no invertibility of ell imposed. sk-def-sfb-coefficient-morphisms states that alpha is a component of the natural pullback-from-point isomorphism, so naturality in the coefficient map is actually available. sk-def-sfb-module-pushforward-pullback supplies the successive/composite module comparison, identifying the last object with M restricted along the actual composite W to S to T to V. These statements justify every displayed isomorphism. No derived comparison, scalar flatness, global lattice inclusion or extra assumption on V is used.

I checked the empty root and empty old/new leaves, the zero module, rank zero, zero-row/zero-column presentation matrices, a single-stratum tree with no internal nodes, arbitrary finite extension fields varying from leaf to leaf, non-Noetherian qcqs roots, and nonreduced stratum structures. Empty leaves admit the zero A_E-module; E belongs to the allowed field family in either case. No additional characteristic or dimension hypothesis is needed. Each step is shorter than 2000 characters. The two elementary steps contain their arguments explicitly; the other steps cite every non-elementary input. Proof dependencies equal the union of uses, and each citation quote is copied from a node statement and checked as a literal substring. I checked all cited nodes' transitive statement/proof dependencies for a return to this item and found none.

Against delivery-errors B, the item preserves TeX and metadata and creates no statement-only-node or duplicate-node issues. Against C, I verified the actual statements rather than definition/proof substitutes and declared off-unit generic tools. Against D, the proof assembles existing smaller tools with explicit matrix elimination, grafting and coefficient identifications; it does not move either clause into a new node. Against E, I checked each hypothesis in the preceding paragraphs and the edge cases just listed. No statement dispute or source correction was needed.

## Delivery checks

The first completed dry run rejected a short coefficient quotation (under forty characters). I replaced it with the full untwisted isomorphism assertion, and expanded the scalar-matrix and point-coefficient quotations to complete sentences/formulas. The cited nodes and mathematical proof were unchanged.
