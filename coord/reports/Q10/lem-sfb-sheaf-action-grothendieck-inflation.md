# Q10 stage-1 delivery: lem-sfb-sheaf-action-grothendieck-inflation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-sheaf-action-grothendieck-inflation.json: existing statement, split in eight steps; statement unchanged; no single Mathlib declaration matches.
- citations.json: fourteen step/node citations with verbatim statement quotes.
- report.md: worker report and signed mathematical review.
- searches.jsonl: actual search-command output retained. prepare.py: item-local preparation script.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures/ for the exact blueprint tag and id, inflation, group-sheaf actions and equivariant module/sheaf terminology. The project has sheafification of groups, torsor coefficient constructions and fixed external-group equivariant evaluation; these do not state the present internal group-sheaf action theorem. The existing closed SheafOfModules.grothendieckAbelian_with_localized_generator belongs to the cited lem-pur-ringed-site-grothendieck-abelian, not to this item; its source at lean/WeilConjectures/CategoryTheory/RingedSiteGrothendieckAbelian.lean:81 was read.

## Wanted literature

WANTED: a precise published non-SGA reference for the general small action-site presentation of internal linear group-sheaf actions, for lem-sfb-sheaf-action-grothendieck-inflation and its existing dependency lem-sfb-internal-action-site-presentation. This is inherited from the item and the existing action-site node; I did not invent an external attribution. The proof_origin is agent. Ordinary module sheafification and abelianness were read in literature/stacks-project/sites-modules.tex, Tag 03CY (lemma-sheafification-presheaf-modules), Tag 03DA (lemma-abelian), and Tag 03DB (lemma-limits-colimits); Tag 03EI (lemma-sheafification-exact) was read as background, not used as an unrecorded lemma. No SGA source is used.

## What needed correction or clarification

The item was an unsplit statement with no proof, rather than an interrupted completed sandbox split. The initial sandbox contained only dispatcher marker files. I retained all its inherited fields and Mathlib searches and added the searches actually run for Q10. There is no statement dispute and no statement change.

The categorical argument must not assert that the action site has finite limits: the existing site presentation constructs a small Grothendieck site and the ringed-site Grothendieck theorem does not need its site to have finite limits. Step 1 explicitly uses the generated Grothendieck topology, avoiding the precoverage-composition pitfall documented in that presentation. The inherited blueprint ancestor chain returns None, ending before a blueprint id; I retained that null value and documented its known motivation, the direct-images proof paragraph (3), rather than fabricating an ancestor. The paragraph itself is the geometric compactification/direct-image assembly; it is not an external proof of the categorical input.

I searched the whole DAG and imported blueprint for action, group action, action site, inflation and Grothendieck structure before considering a new node. The general action-site theorem and equivariant reflector already exist; they are used directly. In particular no new node restates a clause of the item. Ordinary Mathlib Action is an action of one external monoid on an object of a category, whereas here the groups vary with sections. Its abelian and finite-colimit results do not specialize in one line to this theorem. Loogle, LeanSearch and LeanFinder results were read, and both natural-language phrasings plus both recorded source grep queries were checked. All actual Q10 search records are appended without invented queries or unavailability claims.

## Unfinished work

None for this one-level stage-1 split. Proofs of the existing unsplit dependencies remain separate queue items. This delivery writes no Lean and invokes no compiler, Lake, or build tool.

## Not duplicates

No new nodes were created. Reused lem-sfb-internal-action-site-presentation rather than creating a second action-site equivalence, and lem-sfb-equivariant-module-sheafification-reflector rather than a second equivariant quotient-sheafification theorem. Reused the general ringed-site Grothendieck theorem rather than its geometric specializations. Searched the closure of every proof dependency and found no path back to this item.

## Review by Q10

I read the item's current statement, the chapter record sec-six-functors-basics, the unit record sk-thm-sf-ctf-stability and the current main-20261015 direct-images proof paragraph (3). That source is an agent-written motivation for the coefficient/action calculation below direct-image stability. The item itself accurately states the general categorical input, including arbitrary internal group sheaves and the zero ring; it is not a discrete representation assertion. I read the complete statements of every cited node, including the action-site presentation and equivariant reflector, before using them. No new source statement or new node needs separate review.

Step 1 uses exactly the small-site, trivial-ring-action and coefficient-size hypotheses of lem-sfb-internal-action-site-presentation. Its statement explicitly supplies the additive equivalence, the same section modules and the formula a times restriction. Thus the equivalence preserves the particular sectionwise addition in this item. It supplies a small action site even though its arrow set is enlarged by group sections: the coefficient universe contains both the base category and all K(V), so the dependent sum of their hom sets is small. Its last clause is not needed until step 5.

Step 2 applies lem-pur-ringed-site-grothendieck-abelian only after step 1 has supplied a small site and an actual commutative ring sheaf on it. I read that node's statement and its closed source theorem. Its hypothesis is a small site, with no finite-limit condition, so this is a valid application to C_K. The cited lem-galois-equivalence-preserves-limits covers all limits and colimits in both directions because each inverse functor is an equivalence. The step writes out how kernel/cokernel universal properties and the monic/epic tests give every axiom in the cited def-sp-abelian, rather than silently appealing to a new abelian-transfer theorem.

Step 3 uses the same two statements for colimits and the generator. Essential surjectivity supplies the inverse image of the generator, and fullness identifies every map out of G with a map out of its inverse image. Faithfulness then detects equality. That argument does not assume the forgetful functor creates arbitrary colimits, which the item does not state.

Step 4 again uses the equivalence-preserves-limits statement and the ringed-site theorem's exact filtered-colimit clause. The cited exact-sequence definition explicitly defines exactness as image equal to kernel. Images are kernels of cokernels; these diagrams are preserved in both directions, so exactness is preserved and reflected. Applying that observation before and after the filtered colimit proves AB5 with the same small indexing universe. The cited def-sp-grothendieck-abelian requires just the abelian structure, small colimits, a generator and exact filtered colimits, all now exhibited. This is a direct verification from the cited axioms, not an extra lemma hidden in a long step.

Step 5 uses only the last paragraph of the action-site statement: it explicitly says forgetting creates sectionwise kernels and sheafified sectionwise cokernels and that zero is detected by restriction to C. The equivalence leaves section modules unchanged, so its restriction is the item's U_K. This avoids citing just a definition of sheafification for the equivariant claim.

Step 6 first checks all hypotheses of lem-per-exact-family-detection. The source and target categories are abelian by step 2 and def-weil-sheaf-of-modules-category. U_K is additive; the zero object and biproducts have the displayed componentwise actions; kernels and cokernels are preserved by step 5. Equalizers are kernels of differences and coequalizers are cokernels of differences, so finite limits and colimits are preserved. Zero detection was proved in step 5. The generic lemma's statement then supplies both exact and short exact detection for the singleton family. Consecutive triples handle arbitrary complexes. It does not claim that arbitrary section-evaluation functors are exact.

Step 7 is a formula check: the group homomorphism identity and multiplicativity give the action laws, naturality of theta gives compatibility with restriction, and linearity comes from the original action. Equivariant section maps remain equivariant after substitution; identities, composition and addition are unchanged. No external theorem is hidden in this elementary step.

Step 8 checks the actual canonical kernel and cokernel structures rather than only an abstract exactness claim. On the quotient presheaf the restricted action is [n] mapped to [theta(l)n]. The existing reflector statement explicitly gives a unique action on ordinary module sheafification with equivariant unit. Both candidate L-actions satisfy that same property, so their equality follows from this uniqueness. The maps are the same quotient and sheafification-unit maps. Exactness then follows from the literal identity U_L Inf_theta = U_K and the previously verified detection statement, applied with L as well as K. No additional flatness, finite-group, coefficient discreteness or nonzero-ring hypothesis is used.

I checked small cases explicitly. K=1 makes the action site the original site and makes the action category ordinary R-module sheaves. L=1 gives the ordinary forgetful functor, consistent with its established exactness. For the zero ring, unital modules have 1m=0m, so all sections are zero. A noncommutative group is allowed throughout: no calculation reverses multiplication or commutes two group elements. A site with empty covering families causes no exception, since the action-site and sheafification inputs are stated for arbitrary small Grothendieck sites. Non-surjective theta is permitted, because action restriction and its uniqueness argument require no lifting of a section along theta.

Against delivery-errors B--E, there are no new statement-only nodes to mistype, underspecify or duplicate; every node citation is backed by a verbatim statement quote in citations.json. All essential non-elementary facts are cited. Each proof step is under 1100 characters, hence none passes the 2000-character long-step threshold. No definition node is substituted for an equivariant extension theorem, no unnamed source construction is extracted from another node's proof, and there is no cycle. The two off-unit uses are generic tools: the ringed-site Grothendieck theorem and the abelian exactness-detection lemma. I declared both in split_report.tool_uses with their purpose. The other off-unit use, equivalence preservation of limits/colimits, is already a Mathlib leaf. The unit's geometric route has not been replaced or altered.
