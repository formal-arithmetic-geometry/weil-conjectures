# Worker report: lem-sfb-equivariant-coequalizer-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-coequalizer-comparison.json`: the item, split into eight elementary universal-property steps. Statement and statement dependencies retained. No whole-item Mathlib match.
- `citations.json`: verbatim statement excerpts for every dependency cited by a proof step.
- `report.md`: this report. `searches.jsonl` is the search command's own record.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: this item is not the unit's key statement.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item id, equivariant/coequalizer comparisons, and the internal-module coequalizer vocabulary. Read the relevant declarations in `CategoryTheory/Monoidal/Mod/Tensor.lean`; these construct particular relative tensor products and functor comparisons, not the generic claim for arbitrary H,B,P,Q and arbitrary monoid A. The blueprint tag has no project-source hit. Mathlib declarations are not treated as project attachments.

## WANTED

None. The necessary source is available locally.

## Source, route and changes

Read `GOAL.md`, the three-level rule in `SETUP.md`, the chapter record `sec-six-functors-basics`, and the unit record `sk-thm-sfb-qlbar-two-colimit`. Read the current `main-20261015` statement and proof of `lem-sfb-extend-to-qlbar-constructible`. Its last sentence tensors finite presentations on strata; the ancestor does not itself contain the generic equivariant comparison proof. The parent `lem-sfb-internal-extension-inverse-image` needs exactly such a comparison between underlying balancing quotients. The present item stays on that supporting route and does not substitute a new route for a unit step.

Read Stacks `categories.tex`, Tag 002A, `definition-coequalizers` (lines 1153–1170), including the following uniqueness paragraph. It states the ordinary universal property and uniqueness up to unique isomorphism, without a smallness assumption. The equivariant and natural refinement is our own direct argument, marked `proof_origin.by = agent`; it is not attributed to Stacks as if Stacks stated the module-valued result.

The imported statement is correct. No `STATEMENT-DISPUTED` correction is needed. What was missing was its proof. The new steps explicitly derive cancellation from the very universal properties the statement assumes, construct both factors, prove both inverse identities, check both action equations, and verify both naturality equations. There is no appeal to a theorem that coequalizers exist in the module category and no creation/preservation theorem is needed. The hypotheses already provide all underlying coequalizers used.

## Searches and reuse

No earlier item copy, split or report was present in the sandbox, and there was no earlier sandbox search log. Retained the existing item's prior Mathlib search records and appended six searches actually executed for this work; their exact query text and raw command records are in the item and `searches.jsonl`.

Whole-DAG searches used `coequalizer`, `002A`, uniqueness/coequalizer and coequalizer/epimorphism patterns. Whole-blueprint searches used `coequalizer`, `equivariant`, and `quotient comparison`; `blueprint_refs.py ancestor` confirmed `lem-sfb-extend-to-qlbar-constructible`. The blueprint coequalizer results concern relative tensor/scalar-change constructions and are not this general comparison. The closest existing created nodes, `lem-sfb-extension-iso-quotient-formula` and `lem-sfb-internal-extension-inverse-image`, have different hypotheses and conclusions: the former treats extension along a ring isomorphism with a unit-insertion inverse, and the latter inverse-image/scalar-extension commutation. The latter is this item's parent and must not be cited back. No blueprint statement equals this item, so `same_as` remains empty.

Mathlib searches: LeanFinder with two phrasings, Loogle with internal-module/coequalizer names, LeanSearch with the comparison's full meaning, and grep in `CategoryTheory/Monoidal/Mod.lean` and `CategoryTheory/Monoidal`. All six services/commands returned successfully. Read `PreservesCoequalizer.iso` at `Limits/Preserves/Shapes/Equalizers.lean:178` and its surrounding hypotheses, the tensor-desc formula at `Monoidal/Bimod.lean:37`, and `Mod.Hom`, `Hom.mk'`, category composition and `hom_ext` at `Monoidal/Mod.lean:264–321`. The former is an underlying comparison for a functor preserving a chosen parallel-pair colimit; the tensor formulas use chosen coequalizers and stronger global tensor hypotheses. Neither states module linearity and naturality of the general family in this item. The second LeanFinder phrasing found presentations of ordinary modules over a ring, rather than internal module objects in an arbitrary monoidal category. These hits supply useful implementation infrastructure but are not one-line specializations giving every clause of this item.

## Not duplicates

No new node is proposed. In particular, coequalizer cancellation is a short consequence of the universal property already assumed in the statement and remains a proof step rather than a new node. Linearity and naturality are also proved in the item's steps, not moved into nodes restating its clauses.

## Review by Q26

I checked the item and the actual sources with delivery-errors B–E in view. I read the complete statements of `def-sfb-monoidal-category`, `sk-def-sfb-ring-object`, and `sk-def-sfb-module-objects`, rather than taking their names as sufficient. The monoidal definition explicitly says its tensor is a bifunctor preserving componentwise composition. Clause 2 of the module definition explicitly gives the action-compatibility equation for morphisms, their underlying composition, and the forgetful functor. Those are exactly the two definition statements the proof cites; the ring-object definition is retained as a statement dependency but no ring-object theorem is smuggled into the proof. The module definition's sheaf specialization is not used. Its generic monoidal clause applies here. It is declared as a generic off-unit tool in `split_report.tool_uses`.

Step 1 cites no additional node: if fe=ge, the common composite equalizes the parallel pair, and uniqueness of its factor through e proves f=g. This writes out the argument for all four of the assumed coequalizer maps, including both tensor maps, so a separate epi-cancellation theorem is neither assumed nor hidden.

Step 2 uses only hypothesis (1). The factor of q_j through r_j has source Q_j and target P_j, while the factor of r_j through q_j has the reverse type. Their existence uses q_j a_j=q_j b_j and r_j a_j=r_j b_j, respectively; neither requires H_j to be a module. Step 3 checks both composites on the correctly typed quotient maps and then uses step 1; no abstract uniqueness-of-colimits theorem is cited without a node.

Step 4 uses the tensor bifunctor statement and the definition of a module morphism. Its displayed chain is an equality A tensor B_j -> P_j, and uses the action compatibility of r_j, c_j r_j=q_j, then the compatibility of q_j. Only the last equality uses tensor functoriality. Cancellation is legitimate specifically because (3) says 1_A tensor r_j is a coequalizer. Step 5 writes the reverse calculation A tensor B_j -> Q_j, using d_j q_j=r_j and cancellation of 1_A tensor q_j. The cited module statement supplies the exact equation by which each result becomes a module morphism; no exactness, flatness, braiding, symmetry, or commutativity is used.

Step 6 uses the naturality equations assumed for q and r and the constructed comparison equations. The two maps Q_j -> P_k agree after r_j:B_j -> Q_j, so (1), via step 1, proves naturality. Step 7 writes the inverse square as well and cancels q_j, not a map with the wrong source. Both cite the module definition solely to interpret equality and composition of these underlying morphisms in the module category.

Step 8 uses only the already checked module morphisms and their underlying composition. Natural transformations have componentwise composition and equality, so the checked inverse identities give the natural isomorphism. For any competing isomorphism the normalization equation forces each component by the same factorization uniqueness; inverse morphisms introduce no further choice. Thus the uniqueness clause is included, not merely existence of a convenient family. All eight steps are short direct definition/universal-property arguments (the longest is under 800 characters); there is no long step concealing a separate lemma.

For E1/E4 I checked all four uses of a coequalizer against (1) and (3), every tensor source/target, and both naturality squares. Nothing assumes a colimit indexed by J, a small J, or an A-action on H. For E2 I tested the following boundary cases: an empty J gives the unique empty natural isomorphism; a one-object discrete J gives the ordinary equivariant coequalizer comparison; when a_j=b_j each coequalizer is an isomorphism by its universal property, and the result becomes q_j r_j^{-1}; the zero-module case in abelian groups gives the unique zero-object isomorphism. Noncommutative monoids and a nonsymmetric monoidal category cause no change because only the fixed left tensor functor occurs. If (3) were unavailable, the cancellation needed to deduce linearity would not be justified, which confirms where that hypothesis is used.

For B/C/D, there are no new statement-only nodes to audit and no imported fields were deleted. Every dependency cited in the proof has a literal excerpt of its statement in `citations.json`. There is no cyclic citation of the parent, no use of an existing node's proof as if it were its statement, and no SGA source. The Stacks universal property is written out in the item itself, so a Stacks theorem is not being used as an uncited black box. All elementary flags concern calculations or a single instance of that universal property, rather than an omitted mathematical input.

## Unfinished work

None in the requested one-level stage-1 split. No Lean was written or compiled. Server-side dry run and delivery are performed after this report is written.
