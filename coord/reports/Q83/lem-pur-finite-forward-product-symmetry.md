# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-finite-forward-product-symmetry.json`: existing statement unchanged, status split, four assembly steps (1,830 characters).
- `dag/nodes/sec-smooth-purity/lem-pur-finite-open-product-swap.json`: new statement, unsplit, 2,350 characters; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-finite-proper-product-transpose.json`: new statement, unsplit, 2,755 characters; no Mathlib match.
- `citations.json`: verbatim statement quotations for every parent proof citation.

## Attachments

None. The repository's `AlgebraicGeometry.ProEtale.finiteForwardProduct_symmetry` in `lean/Sheaf/Paper/FiniteForwardProductSymmetry.lean`, theorem beginning at line 346, ends in `sorry` at line 373. The project's WeilConjectures searches by the exact blueprint tag and by external-product/counit/symmetry terminology yielded no complete declaration of this item or either new comparison. The open projection, base-change, exactness and full-faithfulness declarations supply constituent operations, not the new two-factor normalized swap statement. No Lean was written or compiled.

## WANTED

None. The current blueprint and the relevant Stacks source files are present.

## What was wrong and what changed

This is the human's deliberate re-split return dated 2026-10-21, not a stale claim of an already reviewed split. The sandbox initially contained only dispatcher marker files: no node, report, citations, or search log. I copied the current live item as the retained delivered version. Its proof was exactly 6,232 characters; its source, statement, Lean records, prior review, ancestry and maintainer-owned fields remain intact. The repair changes its split-owned proof fields and adds two real tasks of comparable statement size. Both children are `unsplit`, with empty proof and proof_deps and null proof_origin. They can be worked on independently: neither cites the other or the parent. No previous argument is discarded or replaced by an unsupported assertion: the complete original seven steps are copied verbatim below and assigned to the new proof obligations.

The geometric open comparison task includes the actual two factorizations, the unit pins, and signed factor-swap identification, rather than merely naturality of an abstract symmetry. The proper task computes actual projection and exchange transposes, proves the required normalization of the ordinary direct-image compositor, and compares the swapped products. It is a statement about ordinary proper direct images, without the original item's compact-support functors or bounded-below tensor domain. Thus neither child restates the whole item. The parent applies the existing compactification identity twice and composes the new two comparison equalities. Its entire proof is below 3,000 characters and no assembly step exceeds 2,000 characters.

## Unfinished work

No requested stage-1 repair remains after successful delivery checks. Proofs of the two new statement-only tasks deliberately remain for later workers, as the return requires. The existing Lean declaration remains sorried and is not treated as an attachment.

## Sources and route

I read GOAL.md, SETUP.md's three blueprint levels, stages/1-dag.md, roles/worker.md, the standing stage-1 brief, tools/README.md, and delivery-errors B--E in full. I read the item's chapter `sec-smooth-purity` and unit `sk-prop-an`, especially Step 6 on permutation coherence, and the current Kunneth-coherence proof's paragraph (i). The nearest blueprint ancestor is `prop-pur-affine-space-composition-law`, via `lem-pur-affine-space-trace-factorization`. Both new nodes record precisely that ancestor and the original item's place plus their subargument; the via list adds this item in front of the existing via list. Whole-blueprint searches for external tensor, open external, proper product, two counits, tensor of counits and product symmetry found no equivalent node under the same hypotheses. `lem-sf-kunneth-coherence` assumes a six-functor datum and bounded finite-Tor inputs; that cannot replace this finite forward-map argument.

For the open child I read Stacks Tag 0GL1 (`sites-cohomology.tex`, `lemma-j-shriek-and-tensor`, lines 4577ff), and the module identity Tag 0E8I (`sites-modules.tex`, `lemma-j-shriek-and-tensor`, lines 4050ff), together with the complete statement of `lem-sf-open-tensor-normalization`. The tags give tensor/open-extension compatibility; the two-factor comparison and its signed swap are an agent-formulated refinement, explicitly identified as such in the new source. The child retains arbitrary ambient complexes and never imports the finite-Tor or six-functor hypotheses of the older external-tensor normalization node.

For the proper child I read Tag 0E48 (`sites-cohomology.tex`, `remark-compatible-with-diagram`, lines 13714ff), the preceding `equation-projection-formula-map` definition, and `remark-base-change`, whose transpose is the pulled-back counit. I also read Tags 0D6D and 0D6E (`lemma-derived-pullback-composition`, lines 3657ff; `lemma-derived-pushforward-composition`, lines 4010ff) and the full statement of `lem-sfb-derived-composition-adjunction-normalization`. Tag 0E48 itself does not literally state this two-map product formula: its omitted mate calculation is the actual task, not a citation pretending it is proved. I retain the earlier review's repair that ordinary direct-image composition alone is insufficient to identify the composite adjunction. All of its Grothendieck/exact-pullback/K-injective normalization argument is copied in old Step 5 below.

## Mathlib and project searches

Every new-node search was run through msearch.py with Q83 and this item, and the exact queries and actual results are in searches.jsonl and the nodes' mathlib_searches. Each child has LeanFinder twice (two different phrasings), LeanSearch, Loogle, and Mathlib grep. All services answered. The two first queries separately target normalized open extension and the counit transpose; the second phrasings ask about the actual two-open product and successive ringed-topos adjunctions. I read the returned signatures. In Mathlib I read externalProductSwap/Flip in CategoryTheory/Monoidal/ExternalProduct/Basic.lean, the sheafification braided instance in CategoryTheory/Sites/Monoidal.lean, Adjunction.comp_homEquiv at CategoryTheory/Adjunction/Basic.lean:584, and the underived structure-module pullback/direct-image adjunction and conjugate comparison in AlgebraicGeometry/Modules/Sheaf.lean:189,265. Diagram external products, symmetric sheafification, and a composite hom-bijection identity do not identify the specified geometric derived maps. A further theorem about these maps and their normalization is required, so neither child is a Mathlib leaf.

Whole-DAG keyword searches and same-tag source searches were made before node creation; the relevant close candidates were opened. In particular `lem-sfb-ringed-kunneth-factorizations` has one common map q and two maps into its single source, while this child has distinct proper maps a and b out of Y and Z. Turning the latter into the former using a disjoint-union construction would require additional functor and counit identifications, not a specialization. It does not state this distinct-map comparison. `lem-sfb-ringed-comparison-tensor-adjunction` supplies path/compositor normalization but not the two exchange/projection product formula. The older `lem-sf-open-external-tensor-normalization` has D^b_ctf and abstract-datum hypotheses absent here. Single-open tensor/support/normalization nodes are used to build the two-open comparison; none already states its two-order signed-swap equality.

## Review by Q83

I reviewed the return against the node files, the four-step parent and the sources. The parent statement is byte-for-byte the live statement. The new statements each introduce their field/coefficient convention, every scheme, morphism, category, object, source and target; a derived morphism's degree is zero. No finite Tor amplitude, invertibility of ordinary projection or exchange, or exceptional functor is introduced. The proper child has only proper maps and ordinary direct images; the open child has no properness hypothesis and no compact-support construction. Their statements contain definitions of the concrete maps and conclusions only, no proof steps or proof sketch. The full original reasoning is retained below as the handoff to future workers.

Parent Step 1 takes exactly T=Rc_*(e)Omega, including original-choice/refinement comparison and the bounded-below etale-origin tensor domain, from `lem-pur-finite-product-compactification`. I opened its statement and checked that its T is precisely the six-arrow Xi of the item, its ordered e is the child's e, and its Omega is exactly the proper child's kappa^{-1} Rb_*(v) w. The parent assumes the comparison's tensor hypotheses in both orders. It supplies no ambient boundedness hypothesis to either child.

Step 2 uses the proper child's displayed swap equality, including its definition of S_{a,b} by the factor swap and tensor symmetry. The child explicitly states all three transposes, so future proof workers must perform old Steps 3--5 and the normalization rather than merely assert symmetry. I checked the types: x has target Rt_*Lr^*H; v has target Rt_*E; w has target Rb_*(Lb^*F tensor J); Omega has target Rc_*E. Under Lt^* the transpose of v is Lr^*epsilon_a tensor identity, and the transpose of w under Lb^* is identity tensor epsilon_b. The normalized kappa makes their composite the tensor of the pulled-back counits. All these equalities and the swapped consequence are in the child statement, not just its report proof. Its proof obligation retains the old Step 5 Grothendieck/exactness and conjugate-compositor check in full.

Step 3 uses exactly the open child's equation e_{j,k}=u_!(sigma) tilde-e_{k,j} sigma and its normalization/independence assertion. I checked both open factorizations have composite u, and that the indicated open base-change/tensor maps are the actual normalized beta/gamma of the existing normalization theorem, not arbitrary isomorphisms. For the swap square, C and P have distinct swaps bar-s and s and bar-s u=u' s; the transported reverse map therefore lands in u_!(q^*N tensor p^*M). Its restriction is the signed tensor symmetry required by the original Step 2, including odd-degree signs. Applying Rc_* and composing with the proper equality uses ordinary functoriality; it cannot alter the swap restricted to P. Hence the output identification is exactly the parent's S.

Step 4 just substitutes these three cited equalities and composes arrows, so it is elementary and needs no extra lemma. Every non-elementary fact is a cited statement. citations.json copies the relevant verbatim parts of those statements; no quote is bent to fit a step. The parent has only same-unit proof citations and needs no new off-unit tool declaration. The report's preserved child proof arguments identify all pre-existing off-unit normalization/tensor tools for their future splits, without putting proof_deps on unsplit children. This follows the lecture-notes/diagonal-purity route; no SGA source is used.

For edge cases, if j and k are identities, both open comparisons are the identity and the displayed square reduces to tensor symmetry followed by its inverse. If either source is empty or either input is zero, all external products and maps are zero; the claims remain valid. If a or b is the identity, the proper transpose reduces to the remaining counit tensored with identity, using the identity compositor normalization. For complexes shifted in odd degrees, both input and output use the same signed symmetry and the naturality calculation carries the Koszul sign twice, cancelling as in old Step 6; no even-degree assumption is made. For A=Z/4 and module Z/2, tensor may be unbounded: both children still apply in the ambient category, while the parent comparison still demands its original bounded-below etale-origin tensor domain. This checks that a hidden boundedness assumption has not slipped into the new nodes.

I checked delivery-errors B1--B9: self-contained TeX statements, definitions actually supplying the named notions, precise source tags and labels without claiming they literally prove the refinement, real logged searches, no unsupported leaf, correct blueprint ancestry. I checked C1--C8 by matching each of the three parent citations to its open statement; the union of uses is exactly proof_deps, and no child reaches the parent. D1--D5 are addressed by two independently workable arguments (geometric open normalization versus ordinary proper counit/compositor calculation), with all old details retained below, not one renamed copy of the item. E1--E7 are addressed by the explicit domains, arrow checks, small cases and unchanged statement. There is no statement dispute or route change. The one returned point, including its at-least-two-new-nodes and at-most-3,000-character conditions, is repaired concretely.

## Retained original argument and assignment to the new tasks

The following is the original 6,232-character proof text, copied verbatim, not a shortened substitute. Old Steps 1 and 7 supply the parent's compactification and assembly; Step 2 is the open task; Steps 3--6 are the proper task. This section is the argument handoff for future workers; neither new node contains a proof.

### Original Step 1

Use the compactifications already chosen in the definition of the two forward maps, writing $f=aj$, $g=bk$. Put $H=j_!M$, $J=k_!N$, $F=Ra_*H$, $G=Rb_*J$, and $C=\bar X\times_B\bar Z$, with $r,t,c,u,D$ as in [lem-pur-finite-product-compactification]. That lemma identifies the actual map $\Xi_{f,g}$ with $Rc_*(e)\Omega_{a,b}(H,J)$, and identifies the exchanged actual map with the analogous expression for $(b,a,J,H)$. Its hypothesis about tensor objects holds in each order by the hypotheses of this item. The lemma includes transport from the independently chosen compactifications of the intermediate maps, so this is an equality of the specified maps, rather than a replacement by an arbitrarily chosen product morphism. It remains to compare the two proper composites and their open tensor identifications.

Cited nodes: `lem-pur-finite-product-compactification`.

### Original Step 2

The open comparison $e$ used in Step 1 intertwines signed symmetry. Indeed factor $u$ as $P\xrightarrow{w}X\times_B\bar Z\xrightarrow{v}C$. Open base change expresses $Lr^*j_!M$ as $v_!$ of the pullback of $M$; the tensor comparison for $v$ puts the other factor inside $v_!$. On $X\times_B\bar Z$, open base change of $k$ and the tensor comparison for $w$ then give $u_!D$. The opposite factorization gives the analogous isomorphism. By [lem-sf-open-tensor-normalization] each open comparison restricts to the identity under the open units. Both maps are therefore maps between objects in the essential image of the fully faithful $u_!$, with the same restriction, so are equal. The same test applied to the square obtained by swapping the factors and inserting tensor symmetry gives a commutative square: both restricted composites are exactly $\sigma_{Lq^*N,Lp^*M}$. Compatibility of pullback with signed symmetry is [lem-pur-derived-pullback-tensor-iso]. This proves the required symmetry of $e$, including all Koszul signs.

Cited nodes: `lem-sf-open-tensor-normalization`, `lem-pur-derived-pullback-tensor-iso`.

### Original Step 3

Compute the proper composite on $C$. Put $E=Lr^*H\otimes^LLt^*J$ and let $x:Lb^*F\to Rt_*Lr^*H$ be ordinary exchange. Its transpose is $Lr^*(\varepsilon_{a,H}):Lt^*Lb^*F\cong Lr^*La^*F\to Lr^*H$ by the definition in [def-exchange-projection]. Let $v=\pi_{t,Lr^*H,J}\circ(x\otimes1_J)$. Under $Lt^*\dashv Rt_*$ its transpose, using the tensor comparisons, is
$$\widehat v=(\varepsilon_{t,Lr^*H}\otimes1)\circ(Lt^*x\otimes1)=Lr^*\varepsilon_{a,H}\otimes1_{Lt^*J}.$$
The first equality is exactly the counit definition of $\pi_t$ and naturality of the tensor comparison; the second is the defining transpose equation for $x$. No exchange or projection is inverted.

Cited nodes: `def-exchange-projection`, `lem-pur-derived-pullback-tensor-iso`.

### Original Step 4

Write $w=Rb_*(\sigma_{J,Lb^*F})\circ\pi_{b,J,F}\circ\sigma_{F,G}:F\otimes^LG\to Rb_*(Lb^*F\otimes^LJ)$. Its $Lb^*\dashv Rb_*$ transpose is
$$\widehat w=\sigma_{J,Lb^*F}\circ(\varepsilon_{b,J}\otimes1)\circ\sigma_{Lb^*F,Lb^*G}=1_{Lb^*F}\otimes\varepsilon_{b,J}.$$
Here $G=Rb_*J$. The first equality is the definition of the ordinary projection transformation. The second is naturality and involutivity of signed symmetry; pullback carries the input symmetry to the displayed one by [lem-pur-derived-pullback-tensor-iso]. All maps, including counits, have degree zero, so this calculation introduces no extra sign.

Cited nodes: `def-exchange-projection`, `lem-pur-derived-pullback-tensor-iso`.

### Original Step 5

The ordinary proper product is $\Omega_{a,b}=\kappa_{b,t}^{-1}\circ Rb_*(v)\circ w$. Transpose successively under $Lb^*\dashv Rb_*$ and $Lt^*\dashv Rt_*$, with the canonical composite adjunction $Lc^*\dashv Rc_*$. The composite hom bijection is the one of [def-weil-pbc-composite-adjunction], and [lem-weil-pbc-mate-pasting] supplies its pasting normalization. The compositor $\kappa_{b,t}$ of [lem-weil-derived-direct-image-composition] is the conjugate of the pullback compositor $Lc^*\cong Lt^*Lb^*$ of [lem-weil-pbc-proetale-derived-pullback-composition]: for constant $A$ the inverse images are exact, the module sheaf categories are Grothendieck abelian by [lem-cbc-sieve-module-sheaves-grothendieck], and [lem-sfb-derived-composition-adjunction-normalization] identifies the conjugate of the derived pullback compositor with the class of the termwise sheaf compositor on K-injectives, which is the normalization of $\kappa_{b,t}$. Hence transposing $\kappa_{b,t}^{-1}$-composites under $Lc^*\dashv Rc_*$ is transposing successively under $Lb^*\dashv Rb_*$ and $Lt^*\dashv Rt_*$. Naturality of each hom bijection gives
$$\widehat\Omega_{a,b}=\widehat v\circ Lt^*(\widehat w)
=(Lr^*\varepsilon_{a,H}\otimes1)\circ(1\otimes Lt^*\varepsilon_{b,J})
=Lr^*\varepsilon_{a,H}\otimes Lt^*\varepsilon_{b,J}.$$
Its source is $Lc^*(F\otimes^LG)\cong Lr^*La^*F\otimes^LLt^*Lb^*G$ and target is $E$. The direct-image compositor is [lem-weil-derived-direct-image-composition]; the pullback tensor and composition identifications are those of [lem-pur-derived-pullback-tensor-iso]. The last equality is functoriality of tensor [lem-weil-derived-tensor-functorial].

Cited nodes: `def-weil-pbc-composite-adjunction`, `lem-weil-pbc-mate-pasting`, `lem-weil-derived-direct-image-composition`, `lem-pur-derived-pullback-tensor-iso`, `lem-weil-derived-tensor-functorial`, `lem-weil-pbc-proetale-derived-pullback-composition`, `lem-cbc-sieve-module-sheaves-grothendieck`, `lem-sfb-derived-composition-adjunction-normalization`.

### Original Step 6

Repeat Steps 3--5 for $(b,a,J,H)$. Identify $\bar Z\times_B\bar X$ with $C$ by the swap. After precomposing with $\sigma_{F,G}$ and postcomposing with the external tensor symmetry, its transpose becomes
$$\sigma_{Lt^*J,Lr^*H}\circ(Lt^*\varepsilon_{b,J}\otimes Lr^*\varepsilon_{a,H})\circ\sigma_{Lr^*La^*F,Lt^*Lb^*G}
=Lr^*\varepsilon_{a,H}\otimes Lt^*\varepsilon_{b,J}.$$
This is naturality and involutivity of the same signed symmetry; compatibility of its pullback and the factor-swap identifications is [lem-pur-derived-pullback-tensor-iso]. Direct images respect transport along the swap by [lem-weil-derived-direct-image-composition]. The adjunction hom bijection is injective, so the two proper forward morphisms themselves agree under these input and output symmetries.

Cited nodes: `lem-pur-derived-pullback-tensor-iso`, `lem-weil-derived-direct-image-composition`.

### Original Step 7

Apply $Rc_*$ to the commutative open-comparison square of Step 2 and combine it with the equality of proper maps in Step 6. Substitute the two factorizations from Step 1. The swap of the product compactifications restricts to $s:P\to Z\times_BX$; its external tensor symmetry followed by the open comparison is therefore exactly the map used to define $S$ in the statement. Thus the substituted equality is $\Xi_{f,g}(M,N)=S\circ\Xi_{g,f}(N,M)\circ\sigma_{Rf_!M,Rg_!N}$. The comparison lemma applies on precisely the bounded-below etale-origin tensor domain assumed here. None of Steps 2--6 required boundedness of the auxiliary ambient tensor objects or invertibility of any projection map.

Cited nodes: `lem-pur-finite-product-compactification`.

## Not duplicates

lem-pur-finite-proper-product-transpose vs lem-pur-finite-forward-product-symmetry: the parent involves chosen compact-support maps on a bounded-below etale-origin tensor domain; the child computes three ordinary proper-direct-image transposes and their swap for arbitrary ambient complexes, and has no compactification comparison. It is the proper subargument, not the complete compact-support assertion.

lem-pur-finite-open-product-swap vs lem-amb-open-projection-composition: composition of tensor projection maps for nested opens on ordinary etale sites is different from two product opens and factor swap on pro-etale sites.

lem-pur-finite-open-product-swap vs lem-asd-open-projection-exchange: the existing statement compares a single open tensor map with base change on ordinary etale sites; the new statement identifies both product-open orders and their signed swap on pro-etale sites.

lem-pur-finite-open-product-swap vs lem-cbc-ringed-open-strict-reduction: the existing result is an augmented adic quotient-tower reduction comparison, including transitions; the new result concerns a pair of opens at one constant finite coefficient level.

lem-pur-finite-open-product-swap vs lem-fix-open-scalar-tensor-normalization: the existing statement concerns change of coefficient ring and a single open tensor map; the new statement concerns two geometric opens and their product-factor swap.

lem-pur-finite-open-product-swap vs lem-pur-co-smooth-pf-exchange-coherence: projection/exchange base-change coherence for one chosen compactification does not identify the two-open product swap.

lem-pur-finite-open-product-swap vs lem-pur-etale-open-derived-tensor: the existing theorem is a single-open tensor isomorphism on ordinary etale sites; the new theorem specifies two-open product constructions and signed symmetry on pro-etale sites.

lem-pur-finite-open-product-swap vs lem-pur-open-projection-site-transport: the existing theorem transports a single open projection through the site-comparison functor; the new statement compares two geometric product-factor orders on one site.

lem-pur-finite-open-product-swap vs lem-pur-projection-formula-coefficient-coherence: the existing conclusion is unit/associativity of inverse projection maps on constructible finite-Tor inputs where they are invertible; the new conclusion is two-open symmetry on arbitrary ambient inputs.

lem-pur-finite-open-product-swap vs lem-pur-varying-ring-tensor-support: the existing conclusion is support for tensor on varying-coefficient systems; the new conclusion identifies normalized two-open product morphisms at constant finite coefficients.

lem-pur-finite-open-product-swap vs lem-sf-comparison-open-tensor-coherence: the existing statement compares etale and pro-etale realizations for one open immersion; the new statement compares two product-open factorizations and their signed swap entirely on pro-etale sites.

lem-pur-finite-open-product-swap vs lem-sf-finite-comparisons-existence: existence of FiniteComparisons and realization pins for one site square does not assert the product-open swap equation.

lem-pur-finite-open-product-swap vs lem-sf-finite-compatibility-transport: the existing equality transports finiteBeta/finiteGamma across a site comparison given an Assertion; the new equality exchanges the two independent open factors.

lem-pur-finite-open-product-swap vs lem-sf-finite-operation-comparisons: constructing prescribed finite realization and operation pins for one open square does not identify the two-open external-product swap.

lem-pur-finite-open-product-swap vs lem-sf-integral-open-reduction-comparison: the existing comparison uses completed integral coefficients and reduction/total-limit reconstruction for one open; the new statement is finite-level ordinary external tensor and swaps two opens.

lem-pur-finite-open-product-swap vs lem-sf-open-tensor-normalization: the existing beta/gamma are single-open base-change/tensor maps; the new statement constructs the two-open external comparison, equates its two factorizations, and identifies the factor-swap square.

lem-pur-finite-open-product-swap vs lem-sf-open-tensor-support: essential-image support of tensor with a single extension is only an object assertion; the new statement identifies two actual product morphisms and their signed swap.

lem-pur-finite-open-product-swap vs lem-sf-open-tensor-support-aux: invertibility of the transpose of one open tensor comparison does not identify the two separate product factorizations or their signed swap.

lem-pur-finite-open-product-swap vs lem-sp-compact-projection-base-change: the existing conclusion commutes projection and base change for a compactified functor; the new conclusion is an open-product swap comparison without a compactified functor.

lem-pur-finite-open-product-swap vs lem-sp-open-scalar-site-coherence: the existing scalar/site square uses A-to-B coefficient change and etale/pro-etale realizations; the new square is a geometric product-factor swap with unchanged coefficients.

lem-pur-finite-proper-product-transpose vs def-weil-pbc-ringed-tensor-square-presentation: the existing node defines representative data for a ringed tensor square; the new node is a theorem identifying a derived external-product composite.

lem-pur-finite-proper-product-transpose vs lem-amb-compactification-projection-composition: the existing result is a proper/open compactification-tower projection identity on etale sites; the new result has two proper maps and computes their binary external-product transpose.

lem-pur-finite-proper-product-transpose vs lem-amb-shriek-projection-open-restriction: the existing statement is compact-support projection compatibility with open restriction on etale sites; the new statement is an ordinary proper-product transpose and symmetry on pro-etale sites.

lem-pur-finite-proper-product-transpose vs lem-amb-shriek-tensor-composition: compatibility of compact-support tensor projection with composition on etale sites is different from the ordinary proper two-map pro-etale external product and factor swap.

lem-pur-finite-proper-product-transpose vs lem-pur-co-smooth-pf-exchange-coherence: the existing statement is projection/exchange base-change compatibility for one chosen compactification (and possibly systems); the new one computes the binary ordinary proper-product transpose and factor swap.

lem-pur-finite-proper-product-transpose vs lem-pur-projection-comparison-etale-origin: the existing statement transports a compact-support projection through an etale-origin comparison for constructible finite-Tor inputs; the new one computes ordinary proper products on arbitrary ambient inputs.

lem-pur-finite-proper-product-transpose vs lem-sbc-strict-quotient-exchange-unit-equation: the existing equation concerns a quotient-coefficient coaugmentation for an exchange map; the new statement computes a binary external-product transpose with two proper direct images.

lem-pur-finite-proper-product-transpose vs lem-sf-constant-semilinear-generator-comparison: the existing statement identifies scalar-restricted reduction generators; the new statement computes the two proper counits in an ordinary binary external product.

lem-pur-finite-proper-product-transpose vs lem-sf-generator-reduction-coherence: coefficient-change squares for semilinear reduction generators do not assert the binary proper product transpose or its factor swap.

lem-pur-finite-proper-product-transpose vs lem-sp-categorical-projection-mate-square: the existing statement is an abstract change-of-square projection/mate equation given tensor compatibility; the new statement computes two counits for the actual ordinary derived proper-product composite.

lem-pur-finite-proper-product-transpose vs lem-sp-compact-projection-base-change: the existing statement is projection/exchange base-change compatibility for one chosen compactification (and possibly systems); the new one computes the binary ordinary proper-product transpose and factor swap.

lem-pur-finite-proper-product-transpose vs lem-sp-completion-mate-comparison: the existing equation realizes completed exchange by strict quotient towers and total inverse limit; the new statement has fixed finite coefficients and an ordinary product transpose.

lem-pur-finite-proper-product-transpose vs lem-weil-pbc-completed-reduction-pullback-square: the existing square involves completed reduction and a strict integral tower before taking mates; the new statement is finite-level ordinary exchange/projection transposition.

lem-pur-finite-proper-product-transpose vs lem-weil-pbc-finite-level-rectangle: the existing assertion is a finite reduction/exchange rectangle; the new assertion is a binary proper-product transpose and symmetry, without coefficient reduction.

lem-pur-finite-proper-product-transpose vs lem-weil-pbc-finite-reduction-pullback-coherence: the existing statement concerns finite reduction commuting with an inverse-image square; the new statement has two ordinary proper direct images and no reduction tower.

lem-pur-finite-proper-product-transpose vs lem-weil-pbc-finite-reduction-pullback-square: the existing square identifies integral and finite inverse-image paths; the new statement computes the ordinary finite external-product transpose with two counits.

lem-pur-finite-proper-product-transpose vs lem-weil-pbc-intrinsic-finite-exchange-rectangle: the existing result commutes finite reduction/projection/exchange for a single square; the new result computes the two-proper-map external-product transpose.

lem-pur-finite-proper-product-transpose vs lem-weil-pbc-ordered-exchange-coefficient-comparison: the existing long result compares completed-ring and constant-ring realizations of ordered exchange; it does not identify a two-input ordinary external product with the tensor of counits.

lem-pur-finite-proper-product-transpose vs lem-weil-pbc-ringed-exchange-tensor-coherence: the existing square says that one projection commutes with exchange; it does not state the composite two-proper-map external product transpose or swap.

lem-pur-finite-proper-product-transpose vs lem-weil-pbc-ringed-square-tensor-compatibility: the existing result asserts tensor compatibility of a ringed square on K-flat representatives; the new result identifies a composite of two projections and exchange after derived adjunction and compositor normalization.

lem-pur-finite-proper-product-transpose vs lemma-weil-pbc-completed-exchange-coherence: naturality, identities and pasting for completed exchange are different from the finite binary product transpose and swap.

lem-pur-finite-open-product-swap vs lem-sf-open-external-tensor-normalization: the existing theorem assumes a six-functor datum and bounded finite-Tor complexes; the new theorem supplies the actual finite-level product-open comparison and signed swap on arbitrary unbounded inputs without a datum.

lem-pur-finite-proper-product-transpose vs lem-sfb-ringed-kunneth-factorizations: the existing theorem uses one q:X→Y twice and a,b:W→X; the new one handles distinct proper maps Y→B and Z→B and their geometric product and canonical compositor. No specialization directly identifies those schemes and functors.

lem-pur-finite-proper-product-transpose vs lem-sfb-ringed-comparison-tensor-adjunction: the existing result normalizes two paths of pullbacks/right adjoints and their tensor comparisons; the new result additionally computes the concrete two-projection/exchange product and its symmetry.

## Validation

The required deliver.py --no-push and final push are run after this report is written. No local DAG/preflight checker or compiler is run.

Preflight repair: added the explicit new-proper-node versus parent comparison in Not duplicates, and replaced the parent proof phrase “the item's hypotheses” by the explicit bounded-below etale-origin tensor conditions in both orders. These are presentation repairs; the statement and argument do not change.
