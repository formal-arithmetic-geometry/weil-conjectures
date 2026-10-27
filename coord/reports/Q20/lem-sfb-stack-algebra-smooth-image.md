1. Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-stack-algebra-smooth-image.json: item, statement unchanged, four proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-stack-qcoh-abelian.json: statement-only prerequisite, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-stack-smooth-qcoh-exact.json: statement-only prerequisite, unsplit; no Mathlib match.
- citations.json: verbatim cited statements for all eleven step/node pairs.

2. Attachments

None. Searched WeilConjectures for the blueprint tag and for stack/quasi-coherent image notions; found scheme-level images and ambient module categories, not this stack theorem. No declaration of the item was found. New prerequisites have no corresponding project declaration.

3. WANTED

None: all mathematical sources used here are present in literature/stacks-project/.

4. Corrections and limitations

The original item is mathematically sound and its statement and statement dependencies were retained. The essential correction to a naive proof is that a categorical monomorphism of quasi-coherent modules need not be a monomorphism in all big-fppf module sheaves. The cokernel is computed there, but kernels need not be. The proof therefore descends multiplication using monicity only in QCoh and uses exact smooth restriction before asserting sectionwise injectivity. No arbitrary-test injection is asserted. Smooth-stack global sections are handled by an atlas and section descent, not by incorrectly treating the big-site inclusion as left exact.

The creation chain has blueprint.from.node null. blueprint_refs.py ancestor returns None. I retained the inherited exact place and via list; the current latest blueprint direct-images proof (3) was read and supplies the upper-unit direct-image context, whereas these stack tools support its inherited adequate-moduli subargument. Nothing at chapter or unit level is changed.

5. Unfinished work

The two new prerequisite statements remain unsplit as required by a one-level split. No Lean was written or compiled. No SGA source was used.

## Review by Q20

I read Stacks stacks-sheaves.tex Tag 06WV, lemma-quasi-coherent-algebraic-stack, all seven assertions and its proof, and stacks-cohomology.tex Tags 076X, lemma-flat-pullback-quasi-coherent, and 0GQF, lemma-quasi-coherent-check-exact, including the smooth-chart proof. I also read sites-modules.tex Tag 03EP, lemma-tensor-commute-colimits, and its tensor/internal-Hom adjunction proof. These are the sources for the item. The abelianity child is exactly 06WV(2), with the big-site QCoh convention stated explicitly. The smooth-exactness child is the smooth specialization of 076X; smoothness on scheme charts gives flat chart maps because smooth scheme morphisms are flat, and the proof of 076X identifies the smooth scheme restrictions as faithful exact functors. The scheme clause concerns ordinary Zariski quasi-coherent modules through the existing scheme-test equivalence. I read stacks-morphisms.tex 075U for the nonrepresentable smoothness convention. None of these results needs finite generation, Noetherian hypotheses, or quasi-compact atlases.

Step 1 cites the abelianity child to take the kernel and its cokernel, obtaining the coimage/image factorization. I opened the existing flat-atlas-exactness node and used exactly its statement that ambient cokernels stay quasi-coherent and coincide with QCoh cokernels, and that ambient epis mean fppf local surjectivity. Its statement does not give kernels or all of abelianity; I did not use its proof as a theorem. In particular j is mono only in QCoh here.

Step 2 cites that same existing node for the structure module and tensor closure. The independent-sheaf-tensor-colimits statement applies on the small-site/universe convention inherited by our stack and preserves cokernels. With K the actual kernel, q is its cokernel in QCoh, and ambient cokernels agree. The displayed equations kill both K tensor A and A tensor K using monicity of j between quasi-coherent objects. Two cokernel descents give multiplication. Tensor powers of q are epis, so checking the ring laws and the two algebra maps by precomposition is justified. This step contains the algebra argument itself, not a restatement delegated to a child. Its 1198 characters hide no subsidiary identification or standard lemma.

Step 3 cites exact smooth restriction for both kernel and cokernel preservation, then the existing scheme-restriction node for its fully faithful, structure/tensor-compatible identification and F(a)=Gamma(T,F_a). I opened the existing ringed-space-algebra-image node: it states precisely that the ordinary local image is an algebra sheaf whose underlying module is the categorical image, whose quotient is locally surjective and whose inclusion is sectionwise injective. It therefore supplies the ordinary scheme algebra image, not a big-site stack injection. Agreement of multiplication follows after the epi q_a tensor q_a, and of units after q_a. Taking sections on T gives the required injection even for nonaffine T; no surjectivity of A(T) to C(T) is claimed.

Step 4 uses the smooth-exactness child twice, first on a and then on the scheme atlas p of Z, so no unstated composition theorem is needed. The algebraic-stack definition supplies a smooth surjective scheme atlas, representable by algebraic spaces after scheme base change. The existing smooth-cover-section-descent statement explicitly says equality of global sections can be checked on that atlas, which is all this step takes from it. Pullback preserves the quasi-coherent algebra by the item conventions. Thus the descent hypothesis is applied to an algebra already constructed in Step 2, and to an actual smooth jointly surjective atlas.

I checked B--E against the node files: both children introduce their base, stack, site, module convention and hypotheses; have statements only; name their Stacks tags and labels; and were searched by LeanFinder twice, Loogle, grep and LeanSearch, using the actual log records. Read the candidate sources: Mathlib AlgebraicGeometry/Modules/Sheaf.lean:50 gives ambient scheme modules abelian, and :183--203 gives general scheme pullback/adjunction, not exact QCoh stack pullback. Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean defines local presentation data, while its Abelian.lean:40 is ambient module-sheaf abelianity. RingTheory/Flat/CategoryTheory.lean proves flat tensor exactness over one ring. These do not specialize in one line to either child. No unavailable service was recorded as a negative result. Existing item search records were retained, and all new searches are logged verbatim.

Small cases: on an affine scheme the proof is the usual image algebra of a ring map. For the identity map C=A; for an algebra map to the zero algebra C=0, with the same construction and unit law. Empty smooth tests have zero section rings and the injection is automatic. Nonaffine tests may have no lift of a global image section, which is why the quotient is sheaf-surjective rather than globally surjective. Nonflat pullback is deliberately excluded from the injection claim: over k[t], multiplication by t can be injective as a module map and cease to be so after tensor with k[t]/(t). The children assert only intrinsic abelianity and exact smooth pullback, so they pass these tests. No new step exceeds 2000 characters. Generic tool uses outside this unit are declared in split_report.tool_uses.

## Not duplicates

lem-sfb-stack-qcoh-abelian vs lem-sfb-smooth-cover-section-descent: Existing node states descent of algebra sections along a smooth cover, not intrinsic QCoh abelianity or exactness of smooth pullback on modules.

lem-sfb-stack-qcoh-abelian vs lem-sfb-finite-schemes-etale-stack-descent: Existing node states descent of finite schemes on a DM presentation, not a module-category theorem.

lem-sfb-stack-qcoh-abelian vs lem-sfb-stack-qcqs-algebra-direct-image: Existing node states quasi-coherence and comparison of qcqs direct image; no kernel or intrinsic abelian-category assertion.

lem-sfb-stack-qcoh-abelian vs lem-sfb-stack-flat-scalar-sections: Existing node states flat scalar base change of global sections for qcqs stacks, not local exactness on arbitrary stacks.

lem-sfb-stack-qcoh-abelian vs lem-sfb-affine-groupoid-quasicoherent-algebra-descent: Existing node states the affine finite-locally-free groupoid algebra dictionary and invariant sections, not general Artin-stack module exactness.

lem-sfb-stack-qcoh-abelian vs lem-sfb-qcoh-presentation-tensor-equivalence: Existing node states tensor-compatible module descent for a DM etale atlas, not abelianity or smooth exactness on arbitrary algebraic stacks.

lem-sfb-stack-qcoh-abelian vs lem-sfb-smooth-atlas-algebra-descent: Existing node states descent of algebra objects and smooth-etale injectivity testing, not intrinsic abelianity or preservation of kernels by smooth module pullback.

lem-sfb-stack-qcoh-abelian vs lem-sfb-stack-qcoh-flat-atlas-exactness: Existing node states tensor/cokernel closure, faithfulness and epi tests only; explicitly makes no kernel claim and does not state QCoh abelianity or exact smooth pullback.

lem-sfb-stack-qcoh-abelian vs lem-sfb-stack-algebra-smooth-image: Existing node is the algebra-image item; the new child concerns arbitrary modules and does not construct algebra multiplication or any factorization.

lem-sfb-stack-qcoh-abelian vs lem-sfb-groupoid-module-limits-colimits: Existing node requires a groupoid in schemes with flat source and target, whereas an arbitrary Artin-stack atlas has an algebraic-space relation and no stack equivalence is in this statement.

lem-sfb-stack-smooth-qcoh-exact vs lem-sfb-smooth-cover-section-descent: Existing node states descent of algebra sections along a smooth cover, not intrinsic QCoh abelianity or exactness of smooth pullback on modules.

lem-sfb-stack-smooth-qcoh-exact vs lem-sfb-finite-schemes-etale-stack-descent: Existing node states descent of finite schemes on a DM presentation, not a module-category theorem.

lem-sfb-stack-smooth-qcoh-exact vs lem-sfb-stack-qcqs-algebra-direct-image: Existing node states quasi-coherence and comparison of qcqs direct image; no kernel or intrinsic abelian-category assertion.

lem-sfb-stack-smooth-qcoh-exact vs lem-sfb-stack-flat-scalar-sections: Existing node states flat scalar base change of global sections for qcqs stacks, not local exactness on arbitrary stacks.

lem-sfb-stack-smooth-qcoh-exact vs lem-sfb-affine-groupoid-quasicoherent-algebra-descent: Existing node states the affine finite-locally-free groupoid algebra dictionary and invariant sections, not general Artin-stack module exactness.

lem-sfb-stack-smooth-qcoh-exact vs lem-sfb-qcoh-presentation-tensor-equivalence: Existing node states tensor-compatible module descent for a DM etale atlas, not abelianity or smooth exactness on arbitrary algebraic stacks.

lem-sfb-stack-smooth-qcoh-exact vs lem-sfb-smooth-atlas-algebra-descent: Existing node states descent of algebra objects and smooth-etale injectivity testing, not intrinsic abelianity or preservation of kernels by smooth module pullback.

lem-sfb-stack-smooth-qcoh-exact vs lem-sfb-stack-qcoh-flat-atlas-exactness: Existing node states tensor/cokernel closure, faithfulness and epi tests only; explicitly makes no kernel claim and does not state QCoh abelianity or exact smooth pullback.

lem-sfb-stack-smooth-qcoh-exact vs lem-sfb-stack-algebra-smooth-image: Existing node is the algebra-image item; the new child concerns arbitrary modules and does not construct algebra multiplication or any factorization.

lem-sfb-stack-smooth-qcoh-exact vs lem-sfb-groupoid-module-limits-colimits: Existing node requires a groupoid in schemes with flat source and target, whereas an arbitrary Artin-stack atlas has an algebraic-space relation and no stack equivalence is in this statement.

DAG and blueprint searches for 06WV, 076X, 0GQF, quasi-coherent abelian, quasi-coherent algebra image and smooth pullback found no equivalent blueprint statement. All existing nodes sharing these source tags were opened; the generic flat-atlas node and scheme comparisons are reused rather than duplicated. The groupoid theorem is deliberately not applied to an algebraic-space relation as though it were a scheme.

lem-sfb-stack-smooth-qcoh-exact vs def-sfb-algebraic-moduli-stack: Existing node defines algebraic stacks and smooth atlases, but asserts no exactness on quasi-coherent modules.

lem-sfb-stack-smooth-qcoh-exact vs lem-sfb-arithmetic-nodal-curve-stack-smooth: Existing node proves smoothness and open loci for a specific moduli stack of curves, not exactness of module pullback.

lem-sfb-stack-smooth-qcoh-exact vs lem-sfb-finite-type-stack-affine-smooth-atlas: Existing node constructs an affine finite-type atlas, not preservation of module kernels or exact sequences.

lem-sfb-stack-smooth-qcoh-exact vs lem-sfb-stack-smooth-atlas-base-change: Existing node compares geometric atlas smoothness with scheme tests and base change, not module-category exactness.

lem-sfb-stack-smooth-qcoh-exact vs lem-sfb-stack-smooth-permanence: Existing node proves composition and base-change permanence of smooth morphisms, not exactness on quasi-coherent modules.
