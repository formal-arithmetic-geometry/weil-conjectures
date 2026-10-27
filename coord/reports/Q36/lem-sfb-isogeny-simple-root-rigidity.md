# Q36 stage-1 delivery: lem-sfb-isogeny-simple-root-rigidity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-isogeny-simple-root-rigidity.json: statement, now split into five proof steps; statement and statement dependencies unchanged; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-homomorphism-borel-rigidity.json: one new statement-only node, status unsplit; no Mathlib match.
- citations.json: ten entries, one per step/node citation, each checked as a literal substring of the cited statement.
- report.md. Research artifacts milne.txt, write_split.py and searches.jsonl stay in this item sandbox.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag, isogeny/simple-root notions, Borel and reductive terminology. The isogeny declarations found concern abelian varieties, and the reductive Lie-algebra declarations concern characteristic-zero Lie algebras, not these scheme homomorphisms. No complete project declaration states the item or the new lemma. No Lean file was written and no compiler, Lake or build tool was run.

## WANTED

None. Milne, Algebraic Groups (2017), is already in literature/milne-algebraic-groups_iAG2017.pdf.

## Corrections and scope

No statement dispute and no change to the item statement. The imported item was statement-only. Its cited Corollary 21.63 is correct, but the abbreviated source proof presupposes the rank-one Borel and generation statements. The delivered proof exposes these prerequisites and explicitly proves the subsidiary identifications from existing statements; it does not assume that the positive simple root groups generate the whole Borel in bad characteristic.

The item uses the existing simple-root generation theorem, including its empty-base clause. The source's Proposition 21.62 speaks of generation by G_alpha and its printed proof starts by using that each G_alpha contains T. With an empty base, interpret this application via the existing corrected node's explicit G=T clause, rather than asserting generation by an empty family of rank-one subgroups for a nontrivial torus.

The source of the item is Corollary 21.63, printed p.443; the sole new node is Proposition 17.21, printed p.358. No Stacks tag is assigned to these Milne statements. No SGA source is used. The new lemma is deliberately left unsplit: its eventual proof is Milne's descent of u(x)v(x)^{-1} to A/B, followed by constancy of maps from the complete connected flag variety to an affine group. That proof is recorded here as a handoff, not smuggled into the new node's statement or proof fields.

The chapter and unit records were read. This item is an auxiliary node, not the unit key node, so no realized record is changed. Its inherited blueprint.from.node is null, exactly as tools/blueprint_refs.py ancestor reports. Retained the inherited place and via chain; the new node prepends this item to via and specifies the Borel restriction step. Read the latest blueprint direct-image statement and proof, whose proof (3) supplies the ancestor route through alterations. Whole-blueprint searches for isogen, rank-one, Borel subgroup, root, homomorphism, centralizer, rigidity, solvable, 17.21 and 21.23 gave no equivalent blueprint node. The broad word searches found unrelated cohomological, Lie-algebra and sheaf-rigidity statements. No unit-level route was replaced.

## Mathlib research

All fresh Mathlib searches used the required msearch.py command with group Q36 and this item. Exact queries, results and verdicts are in the node JSON and authentic searches.jsonl. The new Borel restriction node records LeanFinder twice with different formulations, LeanSearch, Loogle and a source grep. LeanFinder returned AffineSpace.hom_ext/ext_of_isAffine and abstract group extensionality; these require agreement of coordinates or already identical underlying maps, and do not infer equality from a Borel restriction. I read Mathlib/AlgebraicGeometry/AffineScheme.lean:154 and AffineSpace.lean:128. Loogle's Borel hits are LieAlgebra.Basis.borelUpper/borelLower (read Algebra/Lie/Basis/Basic.lean:146-156) and measurable Borel-space machinery, not algebraic Borel subgroups. The AlgebraicGeometry source grep found no reductive/Borel/root-group interface. Fresh item searches returned RootPairing.Hom.ext (read LinearAlgebra/RootSystem/Hom.lean:64-78), Serre Lie-algebra constructors and unrelated group-extension/Galois-category results. None is a one-line specialization to these group schemes. Additional queries about rank-one centralizers were run while considering a separate geometry node; their Lie-algebra SL2/Cartan hits were read and rejected, and no such extra node was created.

## Not duplicates

lem-sfb-homomorphism-borel-rigidity vs lem-sfb-isogeny-simple-root-rigidity: the new lemma assumes equality on an entire Borel of an arbitrary smooth connected affine group and concludes equality there; the item starts with just a torus and positive simple root groups of a reductive group. Passing to each rank-one centralizer and producing its Borel is the item's argument, not a clause moved to the new node.

lem-sfb-homomorphism-borel-rigidity vs lem-sfb-isogeny-torus-conjugacy: that existing node compares isogenies with the same character map up to torus conjugation and depends on this item; the new node requires equality on a full Borel and says nothing about constructing a conjugating torus element. It is not cited here, so no circular proof is introduced.

lem-sfb-homomorphism-borel-rigidity vs lem-sfb-reductive-borel-pair-structure: the latter supplies Borel geometry and root data, not homomorphism uniqueness.

lem-sfb-homomorphism-borel-rigidity vs lem-sfb-simple-root-generation-mixed-commutation: the latter supplies generation by positive AND negative simple root groups, not rigidity from a Borel restriction.

lem-sfb-homomorphism-borel-rigidity vs lem-sc-rigidity: the latter concerns constancy of maps out of products with a proper factor; it neither has an affine algebraic group as domain with a Borel restriction nor supplies the descent to a quotient needed here.

No existing node states Milne 17.21. Searches of the whole DAG by its place and by Borel/agreement/uniqueness terms found the item and its parent as references, and unrelated uses of Borel subgroups; their actual statements were inspected. The rank-one geometry was initially considered as another node, but is instead expanded in steps 1-3 from the existing character antiduality, Smith bases, rank-one structure and Borel product statements, avoiding an elementary or duplicate node.

## Review by Q36

I read the source PDF through its extracted text at Proposition 17.21 (printed p.358), the definition before Theorem 21.11 and Theorem 21.11(a)-(c) and its proof (pp.428-430), 21.19 and 21.23-21.24 (pp.431-432), Proposition 21.29 and Theorem 21.32 (pp.433-435), Proposition 21.62 and Corollary 21.63 (p.443), and the root-product statement 21.68(a) (p.445). I also read the full statements of every node cited by an item step, and the definition statements used to state the new lemma.

Step 1 uses lem-sfb-pid-submodule-smith-bases for diagonal bases of the rank-one sublattice Z alpha in X, and lem-sfb-multiplicative-character-antiduality for changing torus coordinates by a character-lattice basis. These statements give precisely those operations. Over algebraically closed F every torus is split. A nonzero alpha gives one sublattice basis vector; changing its sign gives d>0. The equation d epsilon_1|L=0 in a free character group proves that every torus in ker alpha has first coordinate one. This is why the largest subtorus, rather than the entire possibly nonreduced kernel, is the right object. No smoothness of ker alpha is presumed.

Step 2 uses lem-sfb-reductive-rank-one-reflections for reductivity of C_G(T_alpha), the ambient torus-character weight decomposition and Q alpha intersect Phi={alpha,-alpha}. It uses lem-sfb-reductive-root-subgroup-parametrizations for the conjugation equation and uniqueness by tangent weight. The intervening Lie-centralizer equality is written out from the centralizer's defining commutation functor on dual numbers, not taken from an unstated stronger version of the reflection lemma. T remains maximal because an enlargement inside its centralizer would enlarge it inside G. The character restriction calculation of step 1 then computes the exact two roots, and the conjugation equation places the original U_{+/-alpha} in the centralizer on every algebra. Their tangent spaces identify them with that group's root subgroups by the cited uniqueness statement. The argument uses characters, not their differentials.

Step 3 uses lem-sfb-reductive-borel-pair-structure for <alpha,alpha^vee>=2 and B=U semidirect T; lem-sfb-regular-cocharacter-borel-description for the Borel P(lambda) and its positive-weight tangent formula; and lem-sfb-borel-root-product-coordinates for its single positive root subgroup being exactly its unipotent radical. Each applies to the reductive centralizer with maximal split torus T already checked in step 2. The coroot belongs to T. The integer pairings +/-2 are nonzero even in characteristic two as character pairings, so no bad-characteristic exclusion was introduced. The product is an isomorphism of schemes, which supplies a factorization of every test-algebra point and not merely F-points.

Step 4 uses the new general Borel restriction statement, whose full assertion I checked against Milne 17.21. Its source and target need be smooth connected affine of finite type. The centralizer has those properties by step 2; H has them by hypothesis; the Borel is supplied by step 3. The equality f(ut)=g(ut) is written explicitly and is valid over every F-algebra. Thus the use of the new lemma really yields equality on G_alpha and on its negative root group. The restrictions to G_alpha need not be surjective or isogenies: the new node intentionally imposes neither condition, exactly as 17.21.

Step 5 uses def-sc-group-scheme-subgroup for the criterion that a closed subscheme with subgroup-valued points is a closed subgroup, and lem-sfb-simple-root-generation-mixed-commutation for generation by T and both signs of the simple root groups. The coordinate ideal gives the actual closed equalizer, and its points are a subgroup because f,g preserve products and inverses. Thus the generation node's hypotheses are satisfied scheme-theoretically. E=G implies that the coordinate maps agree. For an empty root base, the existing generation node explicitly says G=T, so the torus restriction alone suffices. This avoids the incorrect claim that positive simple root groups generate a Borel in every characteristic.

I checked the new lemma on tori and unipotent/solvable groups, where the Borel is the whole group; on SL2 and PGL2, including characteristic two; and on products with central tori. Its affine-target hypothesis is essential and retained: one cannot replace it by an arbitrary proper target using the same completeness argument. The item's characteristic-p test includes relative Frobenius with nonreduced kernel: all torus restrictions, root parametrizations and centralizer calculations remain scheme-theoretic. Distinct powers of Frobenius are not counterexamples because their torus maps differ. Central torus factors are retained throughout. The unique new statement is self-contained, has no proof sketch, has no proof or proof dependencies, and does not restate a clause of the item. No proof step is over 2000 characters (lengths 821, 1011, 623, 597, 765); each comparison that might otherwise be hidden is explicitly calculated.

The B-to-E checklist was applied to the files: actual definition meanings and hypotheses checked; no fictitious Mathlib search or unavailable-as-no-match record; exact citations with literal quotes; existing generation reused; no whole-item restatement; no reverse parent dependency; no new statement error. All statements and source references retain the intended root-group and isogeny meanings.

## Unfinished work

No portion of this stage-1 item is left unfinished. The sole new supporting node remains unsplit by the one-level-split rule and is a future item. Required server dry-run checks and direct push are the remaining delivery actions.
