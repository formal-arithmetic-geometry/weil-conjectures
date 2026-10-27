# Stage-1 repair: lem-sf-weil-native-closed-forgetful

## Files written

- dag/nodes/sec-six-functors/lem-sf-weil-native-closed-forgetful.json: existing statement, unchanged, with a 1445-character three-step assembly proof.
- dag/nodes/sec-six-functors/lem-sf-weil-frobenius-action-resolutions.json: statement, unsplit, no Mathlib match; returned steps 1--3.
- dag/nodes/sec-six-functors/lem-sf-ringed-forget-two-injective-hom.json: statement, unsplit, no Mathlib match; returned steps 4 and 6.
- dag/nodes/sec-six-functors/lem-sf-ringed-forget-tensor-transposition.json: statement, unsplit, no Mathlib match; returned steps 5, 7 and 8.
- citations.json: a verbatim statement quote for every citation in each assembly step.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag and native_closed_forgetful, and read WeilSheaf/Category.lean 134--180 and DerivedHom.lean 107--113. Upstream derivedHom defines only the product-Hom functor, not the item's comparisons and compatibility. The project theorem in lean/Sheaf/Paper/NativeWeilClosedForgetful.lean ends with sorry at line 514; its declarations are retained in the existing node, not presented as finished proofs.

## WANTED

None. Sources and prior reviewed arguments are available locally.

## Return repaired

The released stage-1 repair note explicitly reopens this reviewed split and asks for at least two comparable statement-only obligations, a parent proof of at most 3000 characters, preservation of the statement and route, and retention of every argument. Three nodes now divide the 6995-character original argument into site/resolution foundations (steps 1--3), derived internal-Hom models (4,6), and tensor/adjunction/transposition compatibility (5,7,8). Each has a complete independently usable statement, empty proof, empty proof_deps, null proof_origin, unsplit status, its own provenance and four actually run Mathlib searches. The last two nodes are generic conditional ringed-site lemmas so they can be worked on independently of the geometric realization. They are strictly smaller than the original: none asserts the complete native geometric package. The original proofs are reproduced verbatim below as future-worker material rather than inserted as proof sketches in statement-only nodes. No old argument is lost or replaced by a vague slogan.

Final self-containedness read: expanded the second helper's native specialization to introduce its finite field, geometric scheme, Frobenius, coefficient ring and abelian fixed-pair category locally, with all definition dependencies; the first draft had left g_T implicit there. No statement dispute was found. The coefficient condition remains local finite-subextension continuous functions, the geometric Frobenius is semilinear and invertible, and the source remains the derived category of the abelian fixed-pair category. The evaluation-normalized adjunction in the earlier review is explicitly fixed in both generic nodes and the assembly; an arbitrary adjunction with the same right-adjoint objects is insufficient.

## Searches and nonduplication

Read coord/delivery-errors.md B--E in full and the three blueprint levels in SETUP. Read the chapter and the item's actual biduality unit, which has no numbered proof steps. The obsolete package unit was also read but not used to change the assigned unit. Searched the entire DAG for the relevant tags and words, and used blueprint_refs.py search for Frobenius, action site, uncurry/uncurrying, forgetful, K-injective, transposition, native Weil, ringed action, two-K-injective and forgetting Frobenius. The ancestor command prints None: the existing native obligation has a maintainer-created parent with no imported blueprint ancestor. New nodes retain that null ancestor and the full via chain, with precise textual provenance in cor-coef-verdier-weil-equivariance's internal-Hom/evaluation/transposition paragraph. No invented blueprint id is substituted.

All twelve new-node searches were run through msearch.py and are in searches.jsonl; each node records its own exact queries. Each has LeanFinder and LeanSearch with different phrasings, Loogle, and Mathlib grep. Read hits and inspected Mathlib Algebra/Category/AlgCat/Basic.lean 243 (algebra isomorphisms, unrelated to IsoAlgebra fixed pairs), Algebra/Homology/DerivedCategory/ExactFunctor.lean 36--95 (generic exact descent, no action-site or Hom-model theorem), Algebra/Category/ModuleCat/Sheaf/Abelian.lean (abelianity), Condensed/Light/AB.lean (Grothendieck abelianity), CategoryTheory/Monoidal/Closed/Functor.lean 40--107 (Cartesian closed exponential comparison, whose Cartesian tensor is not module tensor), and Algebra/Category/ModuleCat/Monoidal/Closed.lean 71 (ordinary module evaluation). None is an exact match or one-line specialization. The second phrasing and broader names therefore do not yield a Mathlib leaf. All services returned available results; no unavailable response is called no match. The parent's older search records are retained.

## Not duplicates

lem-sf-weil-frobenius-action-resolutions vs lem-sf-twisted-action-ringed-site: the existing statement is wholly underived on a supplied ringed action site; the new lemma establishes the actual geometric Frobenius coefficient/site instance and derived cohomology and resolving-class preservation.
lem-sf-weil-frobenius-action-resolutions vs lem-sf-fixed-pair-derived-forget-comparison: the existing generic Grothendieck fixed-pair lemma has conservative forgetting and K-injectives but no geometric coefficient small-site realization or preservation of K-flat flat-term resolutions. Its generic subclaims are reusable inputs, not a replacement for the geometric resolving package.
lem-sf-weil-frobenius-action-resolutions vs lem-sf-native-weil-basic-comparisons: that node states derived direct-image and open-extension composition, not this geometric ringed-action and tensor-resolution instance.
lem-sf-ringed-forget-two-injective-hom vs lem-sf-weil-derived-hom-single-resolution: the existing result has a sheaf in degree zero as its first argument and a bounded-below second argument, identifies a right-derived single-sheaf Hom, and does not assert this unbounded two-variable forgetful comparison.
lem-sf-ringed-forget-two-injective-hom vs lem-pur-rhom-well-defined: the latter supplies quasi-isomorphism invariance on one ringed site; the new statement compares the native two-injective model to the one-injective model and across a product/Hom-preserving functor.
lem-sf-ringed-forget-two-injective-hom vs lem-weil-pbc-ringed-equivalence-module-hom: the latter assumes an equivalence of ringed topoi. Forgetting an infinite cyclic action is generally not an equivalence.
lem-sf-ringed-forget-tensor-transposition vs lem-sfb-ringed-derived-monoidal-comparisons: that node gives monoidal pullback and composition/direct-image adjunction coherence, not normalization of tensor--internal-Hom transposition with a preserved two-injective model.
lem-sf-ringed-forget-tensor-transposition vs lem-coef-ringed-pullback-hom-evaluation-comparison: that node constructs the evaluation-transposed map but does not show it agrees with the product-of-sheaf-Hom representative isomorphism fixed here.
lem-sf-ringed-forget-tensor-transposition vs lem-sf-evaluation-bidual-comparison-transport: that statement assumes an equivalence of selected full subcategories for duality transport. Here forgetting is conservative, not assumed an equivalence; the new statement verifies comparison normalization on unbounded K-flat/K-injective models and imposes no duality or reflexivity.
lem-sf-ringed-forget-tensor-transposition vs lem-pod-derived-automorphism-hom-evaluation: that statement is about an invertible scheme map and coefficient-stage operations; forgetting a Weil action is not an invertible scheme pullback.
lem-sf-ringed-forget-tensor-transposition vs lem-sf-derived-weil-tensor-hom-adjunction: despite that node's title its statement only asserts bounded constructible tensor stability and depends on this item, so it cannot be cited without a cycle.

New nodes cite the blueprint paragraph as their source, with agent native refinement stated explicitly. They do not misattribute their full new comparisons to a Stacks tag: the tags below supply the generic resolution and Hom machinery, not Frobenius equivariance. No new node's source carries a Stacks tag, so the delivery tool's source-tag duplicate-pair set is empty. The actual close overlaps are compared above.

## Review by Q48

I read the blueprint main-20261015 cor-coef-verdier-weil-equivariance.proof.md, especially the displayed contragredient dual Weil action and the evaluation/transposition paragraph. This is the source for the item and all three new refinements, marked agent refinements rather than claiming the blueprint already states the native theorem. I read Stacks sites-cohomology.tex at lemma-K-flat-resolution (06YS, line 3207), lemma-pullback-K-flat (0G7E, 3508), lemma-RHom-well-defined (0A95, 8754), lemma-internal-hom (08J9, 8896) and lemma-internal-hom-evaluate (0A97, 8965); these justify the generic mechanisms in the preserved arguments, with the last tag used for evaluation construction, not falsely identified with an equivariant comparison. Read the actual native category and derivedHom sources as above. No forbidden SGA source is used.

For assembly step 1, I opened the new Frobenius action/resolutions statement and checked that it supplies every fact the step takes: the small model closed under integer Frobenius iterates, coefficient transport, equivalence at the abelian level, exact conservative descent/cohomology, and both preserved resolution classes. For its retained argument I opened all original cited nodes: def-weil-frobenius-detailed gives the actual semilinear automorphism, def-weil-size-convention supplies the universe bound, the condensed and colimit nodes describe the same coefficient sheaf and its inverse-image compatibility, and lem-sf-twisted-action-ringed-site gives ringed pullback, exact induction, limits/colimits, tensor and conjugation Hom. The exact-functor node states triangulated descent; the unbounded-derived-iso-cohomology node detects isomorphisms of MORPHISMS, as needed for conservativity. K-flat-resolution supplies flat terms, not just K-flatness; ringed-pullback-preserves-kflat explicitly requires these flat terms. The right-adjoint-preserves-kinjective criterion has the correct direction: Ind is the exact LEFT adjoint of U. The K-injective-existence node requires a small ringed site, supplied before it is applied. The new first lemma includes all of this work, rather than a clause asserting only one desired isomorphism.

For assembly step 2, I opened both cited statements. The first gives exactness, product preservation, preservation of K-injectives, and module-category realization, exactly the hypotheses of the second. The second explicitly states the two-injective model, its precomposition quasi-isomorphism, the chain comparison and naturality in the LOCALIZATION, and identifies the actual native derivedHom model. In the retained old steps 4 and 6, lem-pur-rhom-well-defined is used with t:K->J and s=id_I, giving Hom(J,I)->Hom(K,I), not the reverse chain map. def-pur-hom-complex supplies products and the signed differential. def-pur-derived-internal-hom supplies resolution independence in the derived category, not merely degreewise cohomology. I retained the earlier reviewer correction: the normalized adjunction is specified by lem-sf-ringed-derived-tensor-hom-adjunction and def-coef-ringed-tensor-hom-model, not inferred from the unspecified closed-structure theorem alone. Those existing nodes' statements were read.

For assembly step 3, all three cited statements were read again with their hypotheses. Step 1 gives tensor/unit/Hom, products/coproducts and evaluation as underived maps, plus the two preserved resolving classes; step 2 gives precisely the comparison chi fixed in the third node's hypotheses. The third states the tensor differential, summandwise comparison, signed symmetry, full derived uncurrying identity, evaluation square, and the natural transposed map with its iterated-chi image identity. In the retained step 5, site-derived-tensor-descent supplies unique extension of natural transformations from simultaneous K-flat representatives. In old step 7 the normalized model's pure-tensor formula is x tensor y -> phi(x)(y), followed by the inverse localized augmentation; U respects that exact formula. Old step 8 uses the same adjunction and symmetry, so ordinary adjunction injectivity identifies the transpose. I checked every original cited definition/result statement, not just its proof or title. citations.json quotes each new node verbatim in full, so no unsupported shortened quote masks a missing clause.

Small cases checked by hand: the empty scheme/site gives zero module categories; a point with identity action gives modules with an invertible operator (Laurent-polynomial modules), whose forgetful functor is not an equivalence of derived categories but has exact orbit induction. No faithfulness of derived forgetting is assumed. Zero complexes satisfy both comparison and transpose formulas, and unbounded inputs are allowed only with the stated K-resolution conditions. In a ringed site with trivial action the Hom conjugation still uses both the source inverse and target action. For two odd homogeneous degrees the symmetry sign is negative on both sides, and in degree zero evaluation is ordinary f(x). An infinite-dimensional vector space and a general W need not be reflexive: the transpose exists and is compatible, but invertibility is never concluded. Countably many Frobenius iterates of a small model remain within the chosen larger universe. These checks reveal no missing finite-dimensionality, boundedness, exact-left-adjoint, or coefficient hypotheses.

I checked B1--B10: new statements introduce their own objects, have notion dependencies and TeX, retain no proof sketch in statement fields, have genuine logged searches and complete provenance. C1--C8: every assembly fact is in a cited statement, all quotations are verbatim, no statement or proof edge points back to the parent, and all three helpers inherit its unit. D1--D5: this repair extracts genuine comparable model arguments with independent hypotheses, not one whole-package alias or mere shortened prose. E1--E7: tested the edge cases and checked all resolution hypotheses, map directions, signs, underlying coefficient objects, and actual adjunction normalization. The old prose is retained below, with all citations visible for subsequent workers. No new parent step exceeds 2000 characters; total parent proof is below 3000. No repository, launcher, Lean source or compiler was modified or invoked.

## Original arguments allocated to the new workers

The following is the returned proof verbatim, with allocations. These are report material only: new node files are statement-only, as required.

### Returned step 1 -> lem-sf-weil-frobenius-action-resolutions

By [def-weil-frobenius-detailed], geometric Frobenius is an automorphism of the geometric scheme (semilinear over $k$ is allowed). Postcomposition of pro-etale objects by this automorphism and its inverse preserves coverings and pullbacks. Choose a small site model closed under these integer iterates, enlarging the selected small model by its countable orbit if necessary, within [def-weil-size-convention]. The coefficient sheaf is invariant: transport a continuous function along the induced homeomorphism of the object; the same finite intermediate coefficient field still contains its values, and this also respects the local condition [sk-def-sfb-qlbar-condensed, sk-prop-sfb-qlbar-colimit-x]. Apply [lem-sf-twisted-action-ringed-site] to this ringed site and its Frobenius action. It identifies the ABELIAN category $\mathcal B_T$ with modules on a small ringed action site and identifies forgetting with its ringed-topos pullback. Its tensor, sheaf Hom, symmetry and evaluation are the diagonal and contragredient ones in the question. We take complexes and localize only after this equivalence; no equivalence with fixed pairs in $D(\mathcal A_T)$ is asserted.

Cited nodes: def-weil-frobenius-detailed, def-weil-size-convention, sk-def-sfb-qlbar-condensed, sk-prop-sfb-qlbar-colimit-x, lem-sf-twisted-action-ringed-site.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.proof.md; Agent native-derived refinement of the internal-Hom/evaluation argument.

### Returned step 2 -> lem-sf-weil-frobenius-action-resolutions

The abelian forgetting functor is exact and conservative by [lem-sf-twisted-action-ringed-site]. Thus [lem-sf-exact-functor-derived-triangulated] gives its triangulated functor on unbounded derived categories. Exactness gives $H^n(UK)=U H^n(K)$: apply $U$ to kernels and images of the two adjacent differentials, then to their quotient. If $Uf$ is an isomorphism, each $UH^n(f)$ is an isomorphism; abelian conservativity implies each $H^n(f)$ is one, so [lem-weil-pbc-unbounded-derived-iso-cohomology] makes $f$ an isomorphism. This proves derived conservativity. Boundedness and the stated constructibility of $UK$ follow immediately from this cohomology identity and the definition of $\mathcal W(T_0)$.

Cited nodes: lem-sf-twisted-action-ringed-site, lem-sf-exact-functor-derived-triangulated, lem-weil-pbc-unbounded-derived-iso-cohomology.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.proof.md; Agent exactness/cohomology argument at the native localization.

### Returned step 3 -> lem-sf-weil-frobenius-action-resolutions

Apply [lem-pc-kflat-resolution] and [prop-pur-kinjective-resolutions-exist] on the small ringed action site of step 1. Every native complex has a K-flat representative with flat terms and a functorial K-injective representative. Forgetting a K-flat complex with flat terms preserves these properties by [lem-weil-pbc-ringed-pullback-preserves-kflat], because step 1 supplies a ringed-topos pullback. Forgetting a K-injective complex preserves K-injectivity by [lem-weil-pbc-right-adjoint-preserves-kinjective]: the exact additive LEFT adjoint required there is precisely the orbit-sum induction of [lem-sf-twisted-action-ringed-site]. Both applications are to actual module-sheaf categories, and no boundedness assumption on the complexes is needed.

Cited nodes: lem-pc-kflat-resolution, prop-pur-kinjective-resolutions-exist, lem-weil-pbc-ringed-pullback-preserves-kflat, lem-weil-pbc-right-adjoint-preserves-kinjective, lem-sf-twisted-action-ringed-site.

Source: literature/stacks-project/sites-cohomology.tex; Tags 06YS, 0G7E; K-injectives via exact-left-adjoint criterion of the cited node.

### Returned step 4 -> lem-sf-ringed-forget-two-injective-hom

Apply [lem-sf-ringed-derived-closed-symmetric-monoidal] to the action site. It supplies the symmetric closed structure on the native derived category, with total K-flat tensor and product-total derived internal Hom. Its closed adjunction is taken to be the evaluation-normalized one of [lem-sf-ringed-derived-tensor-hom-adjunction] for this tensor and the recorded derived internal Hom; the statement of the symmetric monoidal theorem alone does not pin which adjunction bijection is used, and its evaluation is the counit of this one. This is also the two-K-injective Hom model in the item: if $K\to J$, $L\to I$ are K-injective resolutions, [lem-pur-rhom-well-defined] applied to $t:K\to J$ and $s=1_I$ identifies $\mathcal Hom^\bullet(J,I)$ with $\mathcal Hom^\bullet(K,I)$ by a quasi-isomorphism. This is the ordinary model [def-pur-derived-internal-hom]; the products and differential are exactly [def-pur-hom-complex]. Step 1 identifies its Weil structure as conjugation term by term, so it agrees with the recorded `ProEtaleWeilSheaf.derivedHom`, rather than derived global Hom.

Cited nodes: lem-sf-ringed-derived-closed-symmetric-monoidal, lem-pur-rhom-well-defined, def-pur-derived-internal-hom, def-pur-hom-complex, lem-sf-twisted-action-ringed-site, lem-sf-ringed-derived-tensor-hom-adjunction.

Source: literature/stacks-project/sites-cohomology.tex; Tags 0A95 and 08J9; native two-resolution identification checked against DerivedHom.lean lines 107-113.

### Returned step 5 -> lem-sf-ringed-forget-tensor-transposition

Choose K-flat flat-term representatives $P,Q$ of $K,L$ as in step 3. Since forgetting preserves the sheaf tensor and coproducts, the termwise identifications give a chain isomorphism $U\operatorname{Tot}(P\otimes Q)\simeq\operatorname{Tot}(UP\otimes UQ)$: the differential is $d_P\otimes1+(-1)^p1\otimes d_Q$ on bidegree $(p,q)$ on both sides. The underlying representatives are K-flat by step 3. Localizing this isomorphism gives the asserted derived tensor comparison. The naturality and uniqueness clause of [lem-weil-pbc-site-derived-tensor-descent] on the action site extends it uniquely from these representatives to all derived objects and morphisms. Symmetry is preserved since both representatives exchange $x\otimes y$ with $(-1)^{pq}y\otimes x$ [lem-sf-ringed-derived-closed-symmetric-monoidal].

Cited nodes: lem-sf-twisted-action-ringed-site, lem-weil-pbc-site-derived-tensor-descent, lem-sf-ringed-derived-closed-symmetric-monoidal.

Source: literature/stacks-project/sites-cohomology.tex; Tag 06YS and total-tensor descent of the cited node; agent naturality comparison.

### Returned step 6 -> lem-sf-ringed-forget-two-injective-hom

Choose K-injective representatives $J,I$ of $K,L$. Forgetting preserves products and the underived internal Hom by [lem-sf-twisted-action-ringed-site]. Hence the product-Hom formula [def-pur-hom-complex] gives a chain isomorphism $U\mathcal Hom^\bullet(J,I)\simeq\mathcal Hom^\bullet(UJ,UI)$: the same formula $d(f)=d_I f-(-1)^n f d_J$ defines both differentials. Here $UI$ is K-injective by step 3 and $UJ$ represents $UK$ by step 2. Thus [def-pur-derived-internal-hom, lem-pur-rhom-well-defined] identifies the right side with $R\mathcal Hom_{R_T}(UK,UL)$ and makes these identifications independent of resolutions and natural in the localization. This proves the required isomorphism of derived OBJECTS, with its naturality, not merely isomorphisms of individual cohomology sheaves.

Cited nodes: lem-sf-twisted-action-ringed-site, def-pur-hom-complex, def-pur-derived-internal-hom, lem-pur-rhom-well-defined.

Source: literature/stacks-project/sites-cohomology.tex; Tag 0A95, Hom-complex formula and derived internal-Hom construction.

### Returned step 7 -> lem-sf-ringed-forget-tensor-transposition

The adjunction supplied on each ringed site is normalized on simultaneous K-flat models by [lem-sf-ringed-derived-tensor-hom-adjunction, def-coef-ringed-tensor-hom-model]. In that normalization a map $\phi:P\to\mathcal Hom^\bullet(Q,I)$ uncurries to $x\otimes y\mapsto\phi(x)(y)$ into the K-injective target, followed by the inverse localized augmentation. Forgetting preserves this chain formula by the underived evaluation assertion of [lem-sf-twisted-action-ringed-site]; steps 3, 5 and 6 identify all its source, target and resolution maps with the underlying models. Consequently the tensor/Hom comparisons commute with uncurrying on these representatives, hence with the derived adjunction by resolution independence. In particular, take the transpose of the identity of $R\mathcal Hom(K,L)$: its counit evaluation is sent to ordinary evaluation. The symmetry assertion from step 5 uses the same normalization, so this also proves compatibility with evaluation after symmetry.

Cited nodes: lem-sf-ringed-derived-tensor-hom-adjunction, def-coef-ringed-tensor-hom-model, lem-sf-twisted-action-ringed-site.

Source: literature/stacks-project/sites-cohomology.tex; Tags 08J9 and 0A97; normalized representative uncurrying in the cited native adjunction node.

### Returned step 8 -> lem-sf-ringed-forget-tensor-transposition

Set $H=R\mathcal Hom(K,W)$ and define $\delta^W_K$ to be the adjoint of $K\otimes^{\mathbf L}H\xrightarrow{\sigma}H\otimes^{\mathbf L}K\xrightarrow{e}W$ for the symmetry of [lem-sf-ringed-derived-closed-symmetric-monoidal] and the evaluation-normalized adjunction of [lem-sf-ringed-derived-tensor-hom-adjunction] fixed in step 4, the same adjunction whose uncurrying step 7 compares. Naturality of adjunction, symmetry and evaluation gives naturality in $K$. By steps 5--7 the uncurrying of $U\delta^W_K$, under the comparisons, is ordinary $e\circ\sigma$. The ordinary adjunction is a bijection, so $U\delta^W_K$ equals its ordinary transpose. This argument uses no assertion that either transpose is invertible.

Cited nodes: lem-sf-ringed-derived-closed-symmetric-monoidal, lem-sf-ringed-derived-tensor-hom-adjunction.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.proof.md; Blueprint transposition of evaluation, applied through the native comparisons of steps 5--7.

## Remaining work

The three new nodes intentionally remain unsplit for independent future workers. Nothing required by this repair is knowingly unfinished; server preflight and delivery results are recorded by deliver.py.
