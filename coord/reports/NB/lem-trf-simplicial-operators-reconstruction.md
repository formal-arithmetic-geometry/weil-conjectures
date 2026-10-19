# Worker report: lem-trf-simplicial-operators-reconstruction

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-simplicial-operators-reconstruction.json`: statement, split into six steps; no Mathlib match for the complete reconstruction theorem.
- `citations.json`: verbatim statement quotes for every use in every proof step.
- `report.md`: this report. `searches.jsonl` retains the actual msearch results. `write_split.py` is a sandbox-only writing aid and is not a delivery file.

No new nodes and no new Mathlib leaves. The existing generator leaf is reused.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` for the exact blueprint tag and id, `SimplexCategoryGenRel`, `simplexPresentation`, `toSimplexCategory`, and simplicial operators, as well as the upstream name index. The concrete Amitsur, Čech and monomial Čech constructions do not state arbitrary-category reconstruction. The faithful-presentation node names a separate project's Sheaf declaration, not a declaration of the supplied slopmaster2 WeilConjectures source; I use its DAG statement, not an attachment claim.

## WANTED

None: the needed Stacks source is present.

## Findings and corrections

The original item was statement-only and unsplit. Its statement is correct as written, including the convention that relations are imposed only where both composites are typed. No statement or statement dependency was changed. Stacks 016B (lemma-characterize-simplicial-object), parts (2),(3), and remark-relations give exactly this assertion. Its short proof cites 0168 (lemma-face-degeneracy-category), whose proof is omitted. Instead of adding another presentation theorem, this split reuses the existing faithful-presentation node and the existing morphism-generator Mathlib leaf, and writes out the remaining construction.

The prior parent's search conclusion that faithfulness alone is not the whole reconstruction theorem remains true, but it does not require a new completeness node: generation plus faithfulness makes J bijective on each hom set, and the explicit word evaluation then produces the desired functor. The morphism clause is proved by checking that naturality is a multiplicative property of simplex maps. There is no transfer of the entire item to a new node.

The blueprint ancestor and via chain are retained. I read the current main-20261015 ancestor statement and proof, and the unit sk-i-curve-zero and chapter record. This item is a foundational input beneath the existing comonad/cotangent-resolution support chain; it does not change any unit route, statement, realized fields or chapter. The inherited chain's specific 016B invocation in 0G5N is made precise by the six steps.

## Searches and reuse

Read the actual existing sandbox `searches.jsonl` results before reusing them. The recorded leanfinder query about extending a sequence of operators, the second presentation phrasing, Loogle query, grep and LeanSearch query are preserved with their exact tool/query text. Both semantic services returned definitions or identities of already constructed simplicial objects. Loogle accepted the request but reported unknown identifier `SimplicialObject`, so that query itself supplies no evidence of absence. The grep and source inspection of Mathlib/AlgebraicTopology/SimplexCategory/GeneratorsRelations/Basic.lean (12–18, 51–90) and NormalForms.lean (25–35, end of file) show a quotient presentation and canonical functor, but no theorem making that functor an equivalence in this pinned source. Basic.lean's equivalence announcement is future work, not a declaration. Mathlib/AlgebraicTopology/SimplexCategory/MorphismProperty.lean:74–87 states the generator theorem already represented by lem-sc-simplex-morphism-property-generators.

Whole-DAG searches by 0168, 016B, face-degeneracy-category, generators, presentation and the expected declaration names found the existing faithful-presentation node and generator node. Blueprint_refs searches for reconstruction, simplex presentation and 0168 found no matching blueprint theorem. No new node is needed; hence no duplicated tag pair is introduced.

## Tool uses

`lem-sc-module-cup-godement-simplex-presentation-faithful` is declared in split_report.tool_uses. Its whole statement is a generic theorem on words in cofaces/codegeneracies, with no hypothesis concerning abelian varieties or cohomology. It provides exactly the completeness part of Stacks 0168 used by 016B, and the current unit has no theorem of that kind. This tool use does not replace any geometric route. The generator node and simplicial-object definition are existing Mathlib leaves.

## Review by NB

I read Stacks simplicial.tex from the definition of Delta through 0168, then 016A, 016B in full and the following remark on omitted superscripts. I checked the tags file: 0167 is lemma-relations-face-degeneracy, 0168 is lemma-face-degeneracy-category, and 016B is lemma-characterize-simplicial-object. The item keeps all objects U_n, all permitted operators, both mixed identity clauses, existence and strict uniqueness, and both directions of the morphism criterion. The category D need not have any limits, colimits or extra structure. No SGA source is used.

For Step 1 I opened the entire statement of lem-sc-module-cup-godement-simplex-presentation-faithful: it introduces P as the category of words modulo the six relations, J on degree labels and generators, and injectivity on each hom set. The step uses that stated P and J, not the order-duality construction in its proof. I wrote all relations explicitly; reversing a word turns them into exactly the five input relations, with the two cancellation equalities separate. A replacement within a word preserves its value by composition, and the equivalence closure preserves equality. This is the elementary quotient well-definedness argument for these data, not an invocation of an unstated functor-extension theorem.

For Step 2 I opened lem-sc-simplex-morphism-property-generators and Mathlib's matching statement. It applies to any property containing identities and closed under composition, with all cofaces and codegeneracies. Here W means existence of a preimage under J. Identity lifts, composite lifts and generator lifts are exhibited in the step. The faithful-presentation statement then gives uniqueness of each lift; it is not cited for fullness. Unique lifts of identities, composites and generators are checked by applying J. These are exactly its needed hypotheses and conclusions, and they introduce no unproved equivalence theorem.

For Step 3 I opened def-weil-pbc-simplicial-object: it defines the contravariant functor, its operators and degree objects. The reverse evaluation law and unique-lift equations from Steps 1–2 give the functor laws by the two displayed equations; the generator lifts give precisely d_i,s_i. This is a direct elementary assembly of the established data.

For Step 4 the same generator statement applies to the property that two functors agree on a simplex arrow. The objects already agree, so equality of arrow values is typed. Identity preservation and the explicit composite calculation verify multiplicativity; agreement on both types of generators is the stipulated input. Equality of both assignments gives strict functor uniqueness. No claim is made that arbitrary equivalences imply strict uniqueness.

For Step 5 the generator statement is applied to the displayed naturality equation, with correct endpoints m,n,r. The step writes the full composite calculation in contravariant order. The definition node states exactly that these equations for all operators constitute a natural transformation; this supplies the morphism conclusion. For Step 6 the same definition directly supplies the two restricted naturality equations and uniqueness by components. Every node use in these six steps has its complete verbatim statement in citations.json.

I tested degree zero: there are no faces out of U_0, but s_0:U_0→U_1 has both d_0s_0=1 and d_1s_0=1, agreeing with the two adjacent mixed relations. I tested a degree-two face pair and i=j in the degeneracy relation by reversing the corresponding presentation words. Empty words and degree-zero identity lifts work; maps [m]→[0] and [0]→[n] are included in the generator-property theorem and require no negative ordinal. Constant data with all operators identities give the constant functor and arbitrary natural component families subject to the same equations; a discrete target category causes no additional hypotheses. All proof steps are shorter than 2000 characters. There are no new statements to test or hidden long-step comparisons. No dependencies were taken from a cited node's proof, and no new node restates a clause of the item.

The main correction during this review was to avoid introducing a new presentation-completeness node: the existing faithful-presentation statement plus generator leaf already supplies the exact needed content. The evaluation quotient, functor laws, uniqueness and naturality remain explicit proof steps. Steps 2,4,5 are non-elementary because they apply the cited generator theorem; Steps 1,3,6 only assemble the presented-category data or unfold definitions with their calculations written out.

## Unfinished work

None in the mathematical split. Required server dry run and push follow this report; their output determines the final delivery status.
