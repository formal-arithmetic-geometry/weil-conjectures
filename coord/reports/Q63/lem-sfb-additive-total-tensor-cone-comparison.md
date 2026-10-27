## Worker report

Q63, 2026-10-22, stage 1, lem-sfb-additive-total-tensor-cone-comparison.

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-additive-total-tensor-cone-comparison.json (statement, split; no exact Mathlib match). The sandbox also contains citations.json and the search command's searches.jsonl. No new nodes and no new Mathlib leaves. The statement and its hypotheses are unchanged. No Lean files were written or compiled.

Attachments: none proposed. The dispatched brief specifically forbids repeating the rejected ATTACH result. The comparison and inclusion in WeilConjectures/FromJoel/Algebra/Homology/BifunctorMappingCone.lean:493-510 were read. Unlike the previous attempt's snapshot, the current read clone DOES contain WeilConjectures/Algebra/Homology/BifunctorMappingConeNaturality.lean; its simultaneous hom naturality theorem is at line 85. This is source evidence for the calculation, not a renewed attachment claim or a claim that a compiler/axiom audit ran.

WANTED: none.

The original node had no proof. The stale reference to naturality at lines 90-104 was corrected to the current file region. The missing simultaneous naturality clause from the rejected attachment is proved explicitly in step 4. No statement dispute was found. Nothing remains unfinished at stage 1; the independent maintainer review remains the delivery workflow's next step.

## Sources and route

Read literature/stacks-project/derived.tex, Tag 0G6E, label remark-double-complex-as-tensor-product-of. Its first assertion concerns a bilinear functor from additive categories with countable sums in the target. The proof below expands its cone calculation directly, rather than appealing to exactness on the homotopy category to assert a chain isomorphism. This is recorded as an agent proof. I also read the concrete project comparison and the current naturality source named above.

Read the chapter sec-six-functors-basics and the unit sk-prop-sf-rf-shriek-preservation. This item stays on its existing coefficient-equivalence branch, serving the fourth unit paragraph through lem-sfb-exact-monoidal-equivalence-total-kflat; it does not replace the geometric route or alter the unit. The ancestor command confirms sk-prop-sf-rf-shriek-preservation. Blueprint searches for tensor cone, mapping cone and 0G6E found no imported blueprint node with this general statement.

## Searches and reuse

Read the original node's six logged-result summaries and retained those records. Ran the prescribed msearch command for leanfinder, loogle, grep and leansearch, plus a second semantic phrasing. Every added mathlib_searches record is copied from the command's actual JSONL entry, with the same tool and query. The available services returned hits or zero hits; no unavailable service is reported as a negative result.

The returned mapHomologicalComplexIso in Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean:641 applies a functor on the underlying category degreewise. Reading its type rules it out for the total tensor with an arbitrary complex. HomologicalComplex.tensorObj constructs the total tensor but does not state its cone comparison; the second semantic search returned bifunctor summand inclusions and descent/associator helpers, not the required result. Loogle and the targeted grep returned zero hits.

Searched the whole DAG by cone/tensor/bifunctor and coproduct/biproduct terminology and by Tag 0G6E. The existing lem-sfb-left-resolution-additive-finite-coproducts is precisely the finite-coproduct preservation fact needed in step 1. Its Mathlib reference CategoryTheory.Functor.preservesFiniteCoproductsOfAdditive was read at AdditiveFunctor.lean:213. No new node is needed for reindexing a coproduct, defining signed summand maps, or checking the two parity identities.

## Not duplicates

lem-sfb-additive-total-tensor-cone-comparison vs lem-pc-tensor-mapping-cone-iso: the existing latter statement concerns sheaves of modules on a ringed site; this item concerns every abelian category with an additive monoidal structure and the stated coproduct assumptions. A sheaf-module result cannot be applied to an arbitrary such category.

lem-sfb-additive-total-tensor-cone-comparison vs lem-weil-pbc-total-tensor-homotopy-cone-signs: the latter is also restricted to module sheaves and includes homotopies and K-flatness. Its general sign formula is useful corroboration, but its hypotheses do not cover this item's arbitrary category, so it is not cited for a stronger claim.

lem-sfb-additive-total-tensor-cone-comparison vs lem-trf-tensor-double-hom-exact-comparisons: that statement is about derived R-modules and particular tensor and double-Hom functors, not arbitrary additive monoidal categories.

## Review by Q63

I read the item, Tag 0G6E and all five cited node statements, and checked delivery-errors B through E, including the duplicated historical B-E sections. There are no new statements to audit under B1-B10. The existing statement introduces its category, coproduct and tensor hypotheses, all complexes and arrows, and the cone convention; its four statement dependencies supply the notions actually used. The source has no SGA reference. No statement was weakened to fit a library declaration.

Step 1 uses def-sfb-preserves-kflat-quasi-iso for the actual direct-sum formula and lem-sfb-left-resolution-additive-finite-coproducts for finite-coproduct preservation by an additive functor. I checked the latter's statement: it assumes only preadditive source and target, an additive functor and existence of the given finite coproduct. These follow from the abelian hypothesis and additivity of P^p tensor -. The remainder explicitly defines both regrouping maps and proves their inverse equations on the canonical inclusions. It does not claim that an arbitrary tensor functor preserves infinite products, or that coproducts are exact. The countable sums really are indexed by integers, even for unbounded complexes. This step is non-elementary only for the cited preservation theorem.

Step 2 uses def-sp-abelian for the preadditive category and finite biproducts. Its signed graded maps are explicit; their inverses follow from (-1)^(2p)=1 on each summand. This is elementary morphism arithmetic. I added the explanation that x and y in later formulas denote morphisms from summands, so no illegitimate argument with elements in an abstract category is hidden here.

Step 3 uses the actual cone matrix in def-weil-abstract-derived-category and the actual total differential in def-sfb-preserves-kflat-quasi-iso. I checked every component: the X-to-Y coefficient is (-1)^p, the horizontal X-to-X coefficient changes to (-1)^(p+1), and the vertical one changes to -1; on the other side they are (-1)^p, -(-1)^p and -1. These are the same. The Y components agree without a sign change. This is a short matrix computation from the cited definitions, not an appeal to a hidden tensor-cone theorem. Invertibility is already established independently in step 2.

Step 4 uses def-sfb-monoidal-category only for its explicitly stated bifunctoriality, def-sfb-preserves-kflat-quasi-iso for maps on each (p,q) summand, and def-weil-abstract-derived-category for the cone differential. The map of cones is defined as diag(b,a[1]); the equation u'a=bu verifies its chain property. The induced total tensor square commutes by bifunctoriality. On its two summand families the naturality equation is respectively f^p tensor b^q and (-1)^p(f^p tensor a^(q+1)) on both sides. Degree zero of f is essential and is present. Thus this proves naturality for varying P AND a varying arrow square, exactly the omitted clauses in the earlier rejected attachment. No project naturality theorem is silently used as an uncited node.

Step 5 uses def-weil-abstract-derived-category for the literal inclusion of the Y component and the localization functor Q. Identity on the Y family proves the inclusion equation directly. Applying a functor to the two inverse equations proves the derived isomorphism. Importantly, this never asserts that tensoring by an arbitrary P defines a functor on the derived category; it only applies Q to the constructed chain isomorphism. No K-flatness, boundedness or exactness of countable coproducts is needed.

I checked C1-C4 against the actual statements and wrote a verbatim citation entry for every cited node in every step. The only non-elementary external fact is an existing Mathlib leaf. No source's proof or stronger special-case statement is being treated as a cited theorem. For C5-C8 and D1-D5 there is no new-node duplication, clause relabelling, circular lemma or off-route replacement: the steps construct and verify the isomorphism themselves. All five steps are below 2000 characters; none conceals an auxiliary comparison needing its own node.

For E1-E7 I checked zero complexes, u=0, u the identity, P concentrated in an even or odd integer degree, and characteristic two. The odd-degree case requires the minus sign on the shifted X component; omitting it fails the differential check. For negative p the same parity identities still hold. In characteristic two all signs become identities and the matrix check remains valid. For zero P or X the construction reduces to the expected zero or identity maps, and arbitrary unbounded support is allowed because maps out of coproducts are determined by their inclusions, not by any elementwise finite-support assumption. There was no false source inference or extra hypothesis to repair. The concrete repairs are the missing proof, the omitted simultaneous naturality, and the stale naturality source location.
