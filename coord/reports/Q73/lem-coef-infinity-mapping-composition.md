# Q73: lem-coef-infinity-mapping-composition

## Files written

- dag/nodes/sec-six-functors/lem-coef-infinity-mapping-composition.json — statement item, now split in eight steps; Mathlib searches find no full match. Retained the existing statement, argument, citations, historical search records, source and all maintainer-owned fields. Added six genuinely executed search records from this sandbox's searches.jsonl.
- citations.json — 24 entries, one for every step/node pair, quoting the current dependency statements verbatim.
- report.md — this report.

New nodes: 0. New Mathlib leaves: 0. No unit record changed: this supporting descendant is not its unit's key node.

## Attachments

None. I searched the whole permitted WeilConjectures/ checkout for the item id, mapping_composition, MappingCompositionStatement and the mapping/composition concepts, and checked dag/lean_names_upstream.json. There is no declaration there giving this item. The inherited Sheaf.CategoryTheory.InfinityMappingComposition Lean record is not an attachment in the specified WeilConjectures/ checkout. Its presence and old reviewed metadata do not turn the current unsplit stage-1 item into a finished proof; I have not modified those maintainer-owned records.

## WANTED

WANTED: archived Kerodon Subsection 4.6.8, Tag 01PF, especially Corollaries 4.6.8.5 and 4.6.8.8, Construction 4.6.8.9, Propositions 4.6.8.11–12, Remark 4.6.8.14 and Notation 4.6.8.15, for lem-coef-infinity-mapping-composition.

WANTED: archived Kerodon Proposition 4.6.5.10, Tag 01L5, and Subsection 1.4.6, Tag 004Q, for the mapping-model comparison and the inverse-triangle interpretation of lem-coef-infinity-mapping-composition.

WANTED: archived Kerodon Corollary 3.1.3.4, Tag 00TN, and Proposition 1.5.5.14, Tag 0077, for the background functor-space Kan property and relative boundary-cell argument used by lem-coef-infinity-mapping-composition.

These sources were read online, not downloaded or written to the shared literature. They are Kerodon tags, not Stacks tags. The proof remains marked agent-written because these references are not archived in literature/.

## Findings and changes

No statement correction was necessary. The source means composition in the homotopy category of Kan complexes; the item faithfully expresses that class and then its transport through the specified right-pinch map. I retained its explicit inverse-triangle argument rather than assuming that equality of component classes is already a triangle with the specified third edge.

The existing item had a complete-looking proof and historical review records but status unsplit. Its final step combined two conclusions and had 2154 characters. I read that whole argument before restructuring it: it uses the already established component rule, an inner 2-horn, the degree-one formula for the right-pinched complex, and one fully specified inner 3-horn. It hides no additional comparison theorem or independent lemma. The two conclusions (the category on components, and the inverse-triangle criterion) now have separate steps. I also separated the homotopy-class calculus from conjugation and separated component dependence from associativity/units, so each use is auditable. The longest resulting step has 1467 characters. No elementary subcalculation was promoted to a new node, and no clause of this item was moved into a child.

The current chapter and unit records were read. The nearest blueprint ancestor, confirmed by tools/blueprint_refs.py ancestor, is prop-coef-integral-exceptional-adjoint. I read its current main-20261015 statement and proof, especially the second paragraph beginning “For K”, which computes the derived coefficient adjunction. The current unit metadata remains sk-prop-sf-biduality-general and is untouched. This split supplies the mapping-space foundations below that calculation; it changes no chapter/unit route. The two already recorded generic tools, lem-cbc-simplicial-composition-spine and lem-cbc-kan-mapping-homotopy-invariance, remain declared in split_report.tool_uses. The first supplies arrow-space composition coherence; the second supplies only the Kan property of internal functor spaces. Neither replaces a step of the geometric biduality route.

## Unfinished work

No part of this one-level split remains unfinished. Dependencies retain their own existing states; this delivery makes no claim that the transitive DAG is completely proved. The source archives requested above are unavailable locally, so their absence is explicitly recorded rather than concealed.

## Review by Q73

I read delivery-errors B–E in full and checked this split against the mathematical content of the cited statements, not their titles. For the item I read Kerodon 01PF, 01L5, 004Q, 00TN and 0077 online. There are no new nodes requiring further source or definition audits. I read the complete statements of all six proof dependencies and the two statement dependencies. The statement's quasicategory, equivalence-edge, internal-functor and right-pinched conventions are exactly those of def-cbc-enhanced-diagrams-cones; its U and its specified j are exactly those in lem-coef-infinity-pinch-comparison.

1. Step 1 uses the degreewise Fun definition in def-cbc-enhanced-diagrams-cones, the fixed-vertex H fiber in lem-cbc-simplicial-composition-spine, and the U,j definitions in lem-coef-infinity-pinch-comparison. They really identify V with H_D(a,b,d). I checked that the edge order is 12,01, hence the product order is U(b,d) times U(a,b), as the item requires.
2. Step 2 uses the spine node's explicitly stated boundary lifting, the relative boundary-cell filtration of lem-coef-infinity-monomorphism-boundary-cells, and the Kan property of U in the pinch-comparison statement. Extending over each cell and taking the compatible union gives lifting against monomorphisms. The section lifts the empty inclusion; the cylinder lift has endpoints sp and id and base map p pr_V, whose restrictions are both p. Products are Kan by coordinatewise horn fillers. Thus both the Kan and homotopy-equivalence conclusions hold, including the empty case. No separate assertion about arbitrary weak equivalences is being assumed here.
3. Step 3 uses lem-cbc-kan-mapping-homotopy-invariance with u=id_A, which satisfies its realization hypotheses and has the required smallness in the chosen large universe. Its statement explicitly says Fun(A,Z) is Kan. The quasicategory/Kan definitions supply outer 2-horn reversal and inner 2-horn concatenation, so the relation of cylinder homotopy is already an equivalence relation. Products and composition of cylinders are written down by pairing and substitution; there is no uncited model-category calculus.
4. Step 4 uses the composition supplied by the spine node and the actual homotopy equivalences j in the pinch-comparison node. Writing J=[j] and K=J inverse, the formula c=K C(J times J) constructs the class, and multiplying by J proves its characterization and uniqueness. Its inputs and outputs are Kan, so the classes and their representatives are legitimate by step 3.
5. Step 5 uses the spine statement's associativity/unit coherence and the pinch node's explicit prism formula, whose degree-zero map is the identity on edges. I checked both displayed conjugation equations and cancellation of J. The input identities are therefore precisely the degenerate edges specified in the item. The Kan functor-space statement from step 3 converts equality of classes to actual cylinder homotopies.
6. Step 6 uses the right-pinched Kan property from the pinch node, the horn definitions, and exactly the component-bijection clause of lem-coef-kan-realization-serre. Reversal and concatenation of edge chains produce a single oriented edge. Evaluating the composition representative on (z,q(t)) or (q(t),z) gives the asserted cylinder. No fibration or higher-homotopy clause of the realization theorem is used.
7. Step 7 uses the mapping-space definition, the component-bijection clause just named, the fixed-vertex triangle in the spine statement, and j's identity on edges. A triangle sigma satisfies theta(sigma)=(v,u) and ell(sigma)=w. Applying pi_0 to ell=C theta gives [v][u]=[w]. The earlier associativity and units yield the ordinary category. Every component has a vertex, and degree zero in the right-pinched definition is precisely an edge of D.
8. Step 8 uses only the quasicategory/right-pinched definitions, their Kan property in the pinch statement, and the established component interpretation. I checked the orientation: a degree-one point of M(x,x) from id_x to w is the triangle with 01=id_x, 12=w and 02=id_x. On vertices (x,x,y,x), the chosen faces 123=(f,g,w), 013=(id_x,w,id_x), and 012=(id_x,f,f) agree on every shared edge. They form Lambda^3_1, an inner horn; its missing face 023 is (f,g,id_x). Applying this same construction to (u,v) and (v,u) uses the same inverse representative v and proves both triangle conditions. The converse follows directly from step 7. This is the item's own clause proved by a short horn construction, not a new lemma that restates it.

I tested the statement on the empty quasicategory (all vertex-indexed assertions vacuous), the point, ordinary-category nerves including N([1]), and groupoid nerves. In ordinary nerves the fixed-vertex fibers are discrete, theta is bijective, and the criterion reduces to an ordinary two-sided inverse; the noninvertible arrow of N([1]) is correctly excluded. Empty mapping spaces introduce no nonemptiness assumption. The triangle and cylinder arguments require only the stated Kan or quasicategory hypotheses, never outer fillers in D itself.

The whole-DAG keyword and 01PF/inverse-triangle searches found the existing spine and pinch nodes, which are reused. Blueprint searches for “mapping composition”, “mapping space” and “spine” returned no equivalent imported node; the broader “composition” search was also inspected for the relevant foundations. I checked that a new node is unnecessary, so there are no new/existing duplicate pairs to list. Mathlib searches used the required msearch command, including a second semantic phrasing and a second grep. I read the hits in StrictBicategory.lean, TwoTruncated.lean and SimplicialCategory/Basic.lean: they concern categories of quasicategories, edge quotients, or an assumed enrichment, and do not construct this full right-pinched composition. All six local log records are copied exactly; historical records are retained without pretending they were executed anew by Q73.

I checked B's self-contained notions, TeX and blueprint metadata; C1/C4's citation coverage and exact statement agreement; D's actual argument rather than relabelling; and E's hypotheses, objects and compatibility maps. The proof-dependency list is exactly the union of step uses, citations.json contains a verbatim statement substring for every pair, and no non-elementary step now exceeds 2000 characters. No SGA source is cited, no live file was written, and no Lean or compiler command was run.

## Not duplicates

No new nodes. The existing lem-cbc-simplicial-composition-spine supplies general arrow-space composition; the item additionally identifies the specified triangle fiber and transports the laws through the specified right-pinch map, with the component and inverse-triangle clauses. It is reused as a tool, not recreated.
