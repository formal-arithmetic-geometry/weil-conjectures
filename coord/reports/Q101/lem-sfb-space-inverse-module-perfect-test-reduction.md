# Q101: lem-sfb-space-inverse-module-perfect-test-reduction

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-inverse-module-perfect-test-reduction.json: item, statement, split into six proof steps; statement unchanged; inherited Mathlib searches retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-nil-ring-perfect-derived-limit.json: new statement-only lemma, unsplit; no Mathlib match after LeanFinder (two phrasings), LeanSearch, Loogle and source grep (two directories).
- dag/nodes/sec-six-functors-basics/lem-sfb-space-perfect-tensor-global-limits.json: new statement-only lemma, unsplit; no Mathlib match after LeanFinder (two phrasings), LeanSearch, Loogle and source grep.
- citations.json: verbatim statement quotations for every step/node pair.
- searches.jsonl: actual msearch.py log. write_split.py is a sandbox-only JSON-writing helper, not a delivery file.

Two new nodes; zero Mathlib leaves. All proof steps have fewer than 2000 characters. No Lean file was written, no compiler or Lake was run, and no repository or launcher file was changed by this worker.

## Attachments

None. Searched the whole upstream WeilConjectures source for the blueprint tag and for inverse/perfect, perfect/product, perfect/proper-support and compute-against-perfect terminology. No declaration states the item, the general nil-kernel perfect reconstruction theorem, or the D_QCoh perfect tensor global-product assertion. Scheme colimit continuity, ordinary perfect dualizability and the local nilpotent-reduction predicate do not give an attachment for these statements. The source check for the item did not treat a sorry declaration as completed evidence.

## WANTED

None. The source files needed are already in literature/stacks-project/.

## Problems found and repairs

The item had no proof or proof dependencies. Its statement is faithful to Stacks Situation 0CX4 and Lemma 0CX6(1), including the canonical maps; no statement dispute was found. The existing perfect-tests node proves only perfectness, so it does not discharge reduction. The existing 09AW node lem-weil-pbc-rlim-perfect-complete assumes powers of one ideal and cannot be applied to the arbitrary surjective locally-nilpotent-kernel tower here. I introduced the general 0CQG statement instead of silently using that specialization outside its hypotheses.

I kept all existing metadata, citations/searches and the item's statement. The new nodes inherit the chapter and unit. tools/blueprint_refs.py ancestor returns null for this long created-node chain; I retained that inherited null and prepended the item to the existing via list. The current blueprint is literature/blueprint/latest/ (main-20261024); I read its chapter, unit and direct-images proof (3). This is the inherited coherent-family/Quot effectivity prerequisite, not a new chapter route. No unit realization fields are due from this support lemma.

## Sources and search evidence

I read spaces-flat.tex Situation situation-existence (0CX4), lemma-compute-what-it-should-be (0CX5), and the complete statement and proof of lemma-compute-against-perfect (0CX6). Its proof first computes RHom and then translates by perfect duality; the delivery takes its tensor form so the actual coefficient reduction maps remain visible. I also read sites-cohomology.tex lemma-dual-perfect-complex (08JJ), spaces-perfect.tex lemma-base-change-tensor (0A1K), lemma-base-change-tensor-perfect (0A1P), lemma-base-change-RHom-perfect (0A1R), and lemma-cohomology-base-change (08IN), and spaces-cohomology.tex lemma-affine-vanishing-higher-direct-images (073H).

For lem-sfb-nil-ring-perfect-derived-limit I read more-algebra.tex lemma-Rlim-perfect-gives-perfect (0CQG), its entire proof and the neighboring adic specialization. The node states its all-stages-perfect case, with the canonical adjunct maps made explicit; it makes no completeness-for-one-ideal or uniform-nilpotence assumption. Naturality and the transition equation are the adjuncts of p_n=t_n p_(n+1), not a claim of a functorial choice of cones in an arbitrary triangulated category. Its searches returned ordinary adic completion, perfectoid rings, local cohomology and ordinary limits, no derived perfect reconstruction theorem. The RingTheory grep hits are ring perfection, Teichmuller and perfectoid material, not perfect complexes.

For lem-sfb-space-perfect-tensor-global-limits I read the exact-product/global-RHom paragraph of 0CX6 and its final duality translation, alongside 08JJ. This node isolates the general functor on D_QCoh and its product-triangle calculation; it does not assume an infinitesimal module system and asserts no perfectness of its output. The intended later split uses perfect duality to make tensor by E a right adjoint within D_QCoh, and the derived pullback/global-sections adjunction over the affine base to preserve products. One must take products inside D_QCoh, not assume they are ambient sheaf-derived products. Exactness then sends the displayed 1-shift triangle to the corresponding product triangle in D(A). The source's global RHom argument supplies precisely this general input. Search hits about global sections varying affine schemes, ordinary sheaf evaluation, flat finite limits and induced exact derived functors do not state it.

Before creating either node I searched all DAG statements and source places, the tags 0CQG/0CX6, RHom/perfect limit/product terminology, and the Lean source; I ran blueprint_refs.py searches for Rlim-perfect-gives-perfect, base-change-RHom-perfect, dual-perfect-complex, 0CQG, 0A1P, perfect global sections inverse, nilpotent perfect limit, global cohomology products, perfect complexes nilpotent, perfect tensor products and nilpotent kernels. There was no blueprint-node match. The exact logged Mathlib queries and actual result records are in the new nodes and searches.jsonl; no unavailable service was called a negative result.

## Not duplicates

lem-sfb-nil-ring-perfect-derived-limit vs lem-weil-pbc-rlim-perfect-complete: the existing statement is only the adic A/I^n case, and assumes completeness and perfect K_1; the new statement allows any surjective locally-nilpotent-kernel tower and assumes every stage perfect, as in 0CQG. The existing theorem is not a generalization of the new one.

lem-sfb-space-perfect-tensor-global-limits vs lem-sfb-space-inverse-module-perfect-test-reduction: the new node only proves preservation of products and the inverse-limit triangle for the functor F_E on arbitrary D_QCoh objects; it asserts neither perfectness nor reduction isomorphisms. The item still constructs the compatible finite-level perfect tower, proves its reconstruction hypotheses, applies ring reconstruction, and identifies the specified maps.

lem-sfb-space-perfect-tensor-global-limits vs lem-sfb-space-inverse-module-perfect-tests: perfect-tests assumes the full infinitesimal flat proper-support module setting and concludes perfectness over A; the new functor lemma assumes none of those module/ring-tower hypotheses and does not conclude perfectness.

lem-sfb-space-perfect-tensor-global-limits vs lem-sfb-space-inverse-module-affine-base-change: the existing node computes reduction of sections of K on etale charts; the new node is about the perfect tensor global-sections functor preserving products inside D_QCoh. It is not a chartwise base-change assertion and does not depend on the affine-base-change item, so no circular route is introduced.

lem-sfb-space-perfect-tensor-global-limits vs lem-sfb-ringed-site-global-rhom-derived-limits: that statement concerns ambient ringed-site derived inverse limits of strict towers. The new one concerns products in D_QCoh, which need not be ambient products, and global tensor with a perfect object with its A-action. The ambient result cannot be applied without an additional coherator/duality argument; that is the general comparison isolated here.

## Review by Q101

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the files and the sources, and made the following substantive checks.

Step 1 uses the actual statements of flat-proper-fp-locality (arbitrary base change preserves finite presentation), perfect-limit-category (derived pullback preserves perfect objects), and proper-support-closed-operations (a proper carrier implies proper closed support, and this is unchanged by the closed structure). Since the carrier's ideal kills M_n, its annihilator support is a closed subset of that carrier. This verifies the support hypothesis of tensor-perfect; I did not infer it from the name of a proper-support definition.

Step 2 applies tensor-perfect to f_n, E_n and the single-term complex M_n[0]. Finite presentation of f_n, finite presentation and base-flatness of M_n, boundedness of this single-term complex and proper support were all verified in step 1 or are explicit hypotheses. The affine realization, etale/Zariski equivalence, etale perfectness detection and affine bounded-projective criterion together supply ring-perfectness, not just sheaf-perfectness. Flat-complex-base-change assumes qcqs f_n, QCoh E_n, and a bounded-above relatively flat coefficient complex; all hold. It does not assume X_n flat or M_n intrinsically O_Xn-flat. Its statement explicitly uses ordinary coefficient pullback, hence the supplied module isomorphism identifies it with M_(n-1). The affine pullback/tensor statement is Zariski, so I explicitly cited the etale/Zariski equivalence rather than applying it directly to the etale objects. Transition maps are the adjuncts of these canonical comparisons.

Step 3 uses only the new 0CQG statement. A=lim A_n and the exact kernel assumptions are explicit in the item. Every stage T_n is perfect by step 2, and its derived reductions are the gamma maps just proved invertible. This is the all-stages-perfect branch, which permits locally nilpotent kernels without a common exponent. I did not substitute the stronger nilpotent-kernel or adic hypotheses of a different lemma.

Step 4 uses quasi-compact separated QCoh pushforward on i_n, affine MODULE higher-image vanishing (not merely additive-sheaf vanishing), the qcqs derived projection formula and derived pushforward composition. I made the affineness argument explicit on a chart Spec B: its inverse image is Spec(B tensor_A A_n), induced by a quotient. The closed-immersion affine chart characterization is cited. The projection-formula node says exactly that its canonical counit-induced comparison is invertible; chart-calculus says composition respects units/counits. Their naturality, applied to M_n -> M_(n-1), identifies the tower maps, so the proof does not choose arbitrary isomorphisms for the targets.

Step 5 uses the derived-limit node for the product triangle of K, the new general functor lemma to apply F_E to that triangle, and the new ring reconstruction lemma for the projection adjuncts. Its isomorphism theta satisfies the displayed projection equation. Taking scalar-extension adjuncts of that equation gives the beta in the item's statement, not just some isomorphism between its source and target. This also proves the X-expression after the projection-formula identification.

Step 6 is the elementary equality check on those already constructed maps. I wrote the tensor square for a morphism E -> E' and the equality of the two scalar-extension adjuncts for successive n. The derived-limit statement explicitly gives q_(n-1)=t_n q_n, the projection formula is natural, and flat-complex-base-change specifies the transition coefficient comparison. Thus the adjuncts agree and the bijection implies equality of the maps. Merely saying 'compatibility transports' would not prove this clause; the equations here do. It is elementary relative to these cited statements, not an uncited base-change theorem.

I opened every node used in each step and copied its actual statement into citations.json. No definition is used in place of a theorem, and no node's internal proof is cited as if it were part of its statement. Off-unit tools are declared only in split_report.tool_uses: the affine bounded-projective criterion, affine tensor/pullback comparison and QCoh direct image theorem. Their generic comparison roles preserve the inherited unit route.

Small cases checked: M_n=0 or E=0 makes every cohomology object and reduction map the zero-object isomorphism; X empty gives the same result. A constant ring/module tower reduces to the finite-level tensor-perfect assertion with identity reductions. X=Spec A and M_n=A_n gives the familiar perfect-complex reduction E tensor_A A_n. Nil kernels need not have a uniform exponent, and the 0CQG branch used expressly permits this. Shifts and a zero perfect complex do not require a nonempty cohomological interval. The new product-preservation node applies to arbitrary unbounded QCoh objects, and specifically makes no false assertion that their products are the ordinary sectionwise products of QCoh modules.

Both new nodes are self-contained statements, without proof sketches, proof dependencies or proof-origin fields disguised as proofs. Their definitions are either written inline or cited, TeX has single decoded backslashes, source places are Stacks tags with labels, and their Mathlib records are actual executed queries. Neither new node restates a clause of the item: the item combines general ring reconstruction with finite-level geometry and a general functorial limit comparison. None of its six steps exceeds 2000 characters or hides a further geometric comparison beyond the named inputs. No target or definition used by a target was changed.

## Unfinished work

None for this stage-1 split. The two new nodes remain intentionally statement-only for later splitting; no Lean proof is claimed. The maintainer independently reviews the delivery.
