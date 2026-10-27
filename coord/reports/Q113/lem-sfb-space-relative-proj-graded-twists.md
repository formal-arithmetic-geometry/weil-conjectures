## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-proj-graded-twists.json`: statement, now split into nine proof steps using nineteen existing nodes; no Mathlib match.
- `citations.json`: 37 step/node entries, each quoting the exact cited statement. The full statements are retained so the unit, variance, normalization and hypothesis clauses can be checked together.
- `searches.jsonl`: the five Mathlib searches run for Q113, including two different semantic phrasings.
- `report.md`: this report.

No new nodes; no new Mathlib leaves. The sandbox was initially empty of node files, so the current repository item was copied before editing.

## Attachments

None. Searched the entire `lean/WeilConjectures` tree for the blueprint id and examined the projective-spectrum twisting modules and relative-Proj directory by concept. `AlgebraicGeometry.Proj.twist` and `unitIsoTwistZero` in `AlgebraicGeometry/ProjectiveSpectrum/Twist/Modules.lean` are absolute scheme constructions, not this algebraic-space statement with all its scheme-test clauses. They do not justify an attachment.

## Literature wanted

None. All sources used are present under `literature/stacks-project/`.

## Findings and corrections

The mathematical statement and all its statement dependencies are unchanged. The original item had no proof. Stacks 084D gives the intended construction but omits the arbitrary-scheme-test verification; 085C likewise omits the twisting comparison verification. The delivery supplies these arguments using the affine scalar-extension and module-descent nodes already present. In particular it does not create a second copy of the scheme twists, of scalar extension of twists, or of effective module descent.

The actual tag of `constructions-lemma-relative-proj-base-change` in the checked-out tags table is **01O3**. Some neighbouring source records refer to that label as 01NQ; 01NQ is `constructions-lemma-glue-relative-proj`. The proof uses the correct tag 01O3 and label, without modifying another node's source field. There is also a harmless printed subscript typo in the 084D proof, which writes Proj over U for the algebra on R; the delivery consistently uses Proj over R. Neither observation changes the item's statement.

The blueprint searches `twisting`, `graded algebra`, `twists`, `Proj twist`, and `quasi-coherent descent` were read alongside DAG source/tag searches. No imported blueprint node states this algebraic-space family with all the test comparisons. The existing scheme twists and affine scalar-extension nodes supply its genuine smaller inputs. The item's inherited ancestry command returns None; its original null ancestor and full via chain are retained. The latest blueprint was read at `sec-six-functors-basics/sk-thm-sf-ctf-stability/`: the inherited compactification/Chow prerequisite still serves the proper/open direct-image paragraph. No unit step is replaced and no unit realization is claimed for this subordinate lemma.

## Unfinished work

None at this split level. Existing dependency nodes that are unsplit retain their own work; in particular the affine scalar-extension twist comparison is cited for its statement and not treated as an already formalized proof.

## Not duplicates

No new nodes were created. All scheme twist, affine comparison, fibre-product, pullback and descent facts were reused under their existing ids.

## Review by Q113

I read the complete item against spaces-divisors.tex Tag 084D (`lemma-twists-of-structure-sheaf`), the preceding atlas discussion after 084C, and 085C (`lemma-relative-proj-base-change`). I also read constructions.tex 01NR (`lemma-glue-relative-proj-twists`), 01O3 (`lemma-relative-proj-base-change`), 01N2 (`lemma-base-change-map-proj`), and 01MZ (`lemma-morphism-proj-transitive`). These impose no finite generation, degree-one generation or flatness assumption. There is no new node whose source needs a separate review.

Step 1 uses the actual statements of `lem-sfb-space-module-pullback-quasicoherent`, the Zariski-etale equivalence, ringed-topos pullback-tensor compatibility, the specified etale module-functor adjunction, left-adjoint preservation of small colimits and the normalized space pullback compositor. I checked that the equivalence's forward functor is explicitly tensor pullback and that the compositor states its local tensor formula. Hence preservation of products and coproducts follows from cited statements, rather than an unsupported claim that restriction preserves everything. For these foundations I read sites-modules.tex 03D7, 03D8 and 03EL, descent.tex 03DX, and spaces-properties.tex 03GA. The associativity calculation uses coefficients mapped into the final structure ring, so all displayed products have the same type.

Step 2 uses `lem-sfb-relative-proj-twists-degree-opens` only for the scheme family and its affine restrictions; I verified that its statement does not itself assert arbitrary scheme-base-change compatibility. That missing inference is written out using `lem-weil-pbc-module-pullback-affine-sections`, `lem-nagata-affine-proj-scalar-extension` and `lem-sfb-proj-scalar-extension-twist-comparison`. The latter explicitly supplies every integer degree, the fraction formula, preservation of products/sections, and compatibility with further standard-open restrictions; the former Proj node explicitly supplies the covering by inverse images of the original standard opens. On an affine base refinement all maps are induced by the same composite ring map, so their fractions agree. I read schemes.tex 01I9 and 01IA for the coefficient identification. I avoided asserting intersections of affine opens are affine: refine each intersection by affine opens, and glue maps and inverses by the sheaf condition.

Step 3 takes the identity and composition clauses from the affine twist-comparison statement, together with the stated pullback compositor and scheme site equivalence. Equality can be checked on the affine chart covering because these are maps of sheaves. The same fraction formula proves compatibility with the canonical graded algebra identifications; no unexplained transport is used. This supplies the cocycle on triple overlaps before descent is invoked.

Step 4 uses `def-trf-algebraic-space` for a representable surjective etale atlas and representable diagonal, `lem-sfb-space-relative-proj-scheme-tests` for representability of P over X and compatible scheme comparisons, `lem-trf-space-fibre-products-etale-covers` for the pulled-back covering, and `lem-sfb-space-fppf-covering-calculus` for etale implying fppf. I checked that U2, U3 and every P_V here really are schemes by representability, rather than by separation or quasi-separatedness. The descent isomorphism has the same direction as the fppf-descent statement, and the step-3 composition identity is precisely its triple-overlap identity. I read spaces-topologies.tex 0DFC and the fppf covering discussion. No quasi-compact atlas is needed.

Step 5 applies `lem-sfb-space-fppf-qcoh-descent` to modules with the cocycle just constructed. Its statement explicitly has both essential surjectivity and full faithfulness, without a quasi-compactness assumption. I checked this against spaces-descent.tex 04W8. The equality E0=O_P is made by transporting along the unique compatible degree-zero isomorphism, not asserted as a literal property of an arbitrary descent choice. Tensor-product quasi-coherence is justified locally by the scheme equivalence, pullback-tensor compatibility and `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`; I read schemes.tex 01I8 and modules.tex 01CE. The local criterion is explicitly present in `def-trf-space-quasi-coherent-module`, so full faithfulness is applied to quasi-coherent sources as required.

Step 6 uses that same full faithfulness to descend compatible multiplication maps and degreewise section maps. Pullback-tensor identifies the product's source, the compositor identifies the section-map source, and space pullback preserves quasi-coherence of A_n. Associativity, ordinary commutativity, unit laws and multiplicativity descend as equalities of maps, tested on the atlas. `def-trf-etale-graded-module-algebra` explicitly defines the total object as a sheaf coproduct and explains assembly of homogeneous operations; it does not assert that sections commute with infinite coproducts. This distinction is preserved.

Step 7 checks the part omitted in 084D: for an arbitrary W, W'=W x_X U is a scheme etale-covering W, and P_W' covers P_W. Both candidate modules are quasi-coherent by the cited pullback theorem. Their isomorphism is explicitly constructed on that covering from the previously constructed scheme comparisons, and the triple-composition equality makes it compatible with its two projections. The stated full faithfulness descends it and its inverse, and tests preservation of the algebra and section maps. I verified that the cited scheme-test node supplies the underlying scheme and morphisms, not a twisting theorem that would be circular.

Step 8 uses the normalized compositor and module descent only. Both competing comparison maps become the scheme composition formula on the indicated covering, so faithfulness proves their equality. For uniqueness, the two families agree over the atlas with their actual descent isomorphisms; full faithfulness therefore supplies a unique isomorphism of modules, and faithfulness checks all operations and every test comparison. This is stronger than an unsupported assertion that agreeing objects are canonically identical.

Step 9 uses the scheme twist node, `def-weil-pbc-proj-twisting-sheaf` and the affine twist comparison exactly for their local fraction and homogeneous-section clauses. I checked negative shifts use C_i=0 for i<0, and did not assume any twist is invertible or any multiplication is an isomorphism in this generality.

I checked B--E against these files: there is no new statement-only-node or duplicate problem, no clause moved into a renamed node, no extra hypothesis, no missing operation comparison, and no dependency reaches back to this item. Each cited statement was opened; `citations.json` contains its exact text, including hypothesis clauses. All nine steps are below 2000 characters; the elementary assembly of already-cited affine comparisons contains no new non-elementary lemma. Generic tools from other units (Zariski-etale equivalence, fibre-product calculus, affine module sections/tensor and colimit preservation) are declared in `split_report.tool_uses`, not a top-level maintainer field.

Small cases checked: an algebra concentrated in degree zero has empty Proj, so every descended module is the unique module there; the empty base/atlas is handled by the same descent statement. For k[x] with deg(x)=1 the chart module in every integer degree is generated by x^n. For k[x] with deg(x)=2 the odd twists are zero on Proj; this confirms why no general invertibility or tensor-isomorphism claim can be inserted. The nonflat extension Z to F_p is covered by the scalar-extension formula without exactness of tensor. Arbitrary larger degree-zero rings are permitted because none of the affine inputs requires A0=R. None of these cases requires a statement repair.

The first server `review_split` check passed with zero new nodes. The full delivery dry run and push are the remaining mechanical delivery operations.
