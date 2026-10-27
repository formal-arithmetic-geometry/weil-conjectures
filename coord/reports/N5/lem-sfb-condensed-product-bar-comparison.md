# Repair of lem-sfb-condensed-product-bar-comparison

## Worker report

The sandbox initially contained only dispatcher brief markers, not the promised retained node/report/search log. I therefore copied the current read-only repository item, whose eleven proof steps are exactly the returned long proof. `original-node.json` preserves that complete starting record, including its statement, citations, previous searches and Lean metadata. No repository or launcher file was written, no git command was run there, no Lean was written or compiled, and no agents were started.

Files written under dag/nodes/sec-six-functors-basics/:

- lem-sfb-condensed-product-bar-comparison.json: statement unchanged; four-step assembly, 1878 characters of proof text.
- lem-sfb-condensed-action-injective-restriction.json: statement, unsplit; no Mathlib match. Carries old steps 1–2.
- lem-sfb-condensed-product-bar-resolution-model.json: statement, unsplit; no Mathlib match. Carries old steps 3–4.
- lem-sfb-condensed-successive-bar-quasi-augmentations.json: statement, unsplit; no Mathlib match. Carries old steps 5–7.
- lem-sfb-condensed-product-bar-normalization-naturality.json: statement, unsplit; no Mathlib match. Carries old steps 8–11.

All four new nodes have empty proof and proof_deps and null proof_origin. Their statements introduce A, the small profinite site, groups, action categories, module operations, resolutions, and all auxiliary complexes and maps they use. They are separate implementation tasks: flat induction/injectivity; common model/diagonal; two augmentation quasi-isomorphisms; conditional arrow normalization and homotopy naturality. The last assumes the earlier augmentation and K-injectivity conclusions, rather than reasserting existence of the entire comparison package.

Attachments: none. Searches of lean/WeilConjectures for the item tag and condensed/product-bar concepts found no exact project declaration. The existing Sheaf.CategoryTheory.CondensedProductBarComparison theorem at lines 626–648 has `sorry` at line 648, so it is not an attachment. Its docstring carries the same eleven arguments. The metadata about this existing Lean statement was left unchanged.

WANTED: an exact reference for the product/successive internal bar comparison in ordinary internal modules over an arbitrary commutative condensed ring, for this item and the four new nodes. The main-20261015 direct-images proof paragraph (3) supplies the surrounding open-direct-image route, not this auxiliary theorem. This is the inherited agent-written input; no literature attribution was invented.
WANTED: Weibel, An Introduction to Homological Algebra, section 8.5, dual bicosimplicial Eilenberg–Zilber and totalization with a compatible nonnegative complex, for the already existing lem-sfb-bicosimplicial-shuffle-totalization used in the allocated old step 8. No new shuffle node is created here.

The returned fault was excessive proof work in one node, not a disputed mathematical statement. The statement is retained byte-for-byte. There is no STATEMENT-DISPUTED correction. Every old argument, including the equivalence of module encodings, the exact induction adjunction formulas, sectionwise image-and-quotient arguments, transpose signs, arrow normalization, lift homotopies and degenerate cases, is assigned below verbatim. The only unfinished work is the intended parallel proof work on the four statement-only tasks.

## Mathlib and duplicate searches

Each new node has its own executed natural-language searches, a Loogle query and a source grep, recorded exactly in mathlib_searches and searches.jsonl. Full first-round outputs are retained in the four .search-results.txt files. Extra LeanFinder phrasings and narrower greps are also in the log. Two LeanSearch requests were rate-limited and are recorded as unavailable, not negative results. Their tasks each received a second successful LeanFinder phrasing in addition to Loogle and grep.

I read the returned signatures: Condensed.profiniteFree only defines the free functor for an ordinary coefficient ring; LightCondensed internallyProjective/tensor-condition equivalences do not establish exact induction for actions over an internal ring. Rep.barResolution and Rep.standardComplex augmentation declarations concern abstract groups and ordinary rings, not the internal derived Hom model here. General injective-resolution lift/quasi-isomorphism declarations and Dold–Kan projectors do not state the group-augmentation or normalization assertions. I opened Mathlib/Condensed/Solid.lean (free functor), RepresentationTheory/Homological/Resolution.lean (standard/bar complexes and augmentation), and read the search signatures to reject these as exact or one-line specializations. No Mathlib leaf is claimed.

Before creating files I searched the whole DAG by names, titles, and statement keywords and ran tools/blueprint_refs.py search with bicosimplicial, injective restriction, successive bar, product bar, internal bar, injective induction and shuffle augmentation. None of the blueprint hits states a proposed task: the injective restriction hit is henselian geometric restriction acyclicity. The ancestor command returns None, as in the inherited item; the children retain this null ancestor and prepend the item to the inherited via chain, with exact old-step allocations in from.place. The unit and chapter route are unchanged.

## Not duplicates

- lem-sfb-condensed-action-injective-restriction vs lem-sfb-condensed-product-action-inflation: the existing statement establishes Grothendieck categories, exact inflation and right adjoint invariants, not flat represented free modules, exact induction left adjoints or injective restriction/forgetting. The present task needs those additional constructions.
- lem-sfb-condensed-action-injective-restriction vs lem-sp-right-adjoint-preserves-injectives: the generic theorem requires an exact left adjoint; the new task constructs and proves exactness of the internal-group induction adjoints needed to instantiate it.
- lem-sfb-condensed-product-bar-resolution-model vs lem-sfb-condensed-derived-invariant-bar: the existing theorem computes one group's bar; the new task supplies the common two-action compatible resolution model and identifies its diagonal and augmentation. It will use that theorem after identifying the model.
- lem-sfb-condensed-successive-bar-quasi-augmentations vs lem-sfb-condensed-internal-bar-resolution: the existing statement is exactness of a homogeneous free chain resolution, including tensoring; the new task passes to internal Hom against restricted injectives, retains G on the H augmentation and proves two signed total augmentation quasi-isomorphisms.
- lem-sfb-condensed-successive-bar-quasi-augmentations vs lem-sc-first-quadrant-total-column-comparison: that theorem assumes column quasi-isomorphisms, whereas the new task proves the requisite sectionwise augmented exactness and constructs the two comparison maps.
- lem-sfb-condensed-product-bar-normalization-naturality vs lem-sfb-bicosimplicial-shuffle-totalization: the existing theorem provides a generic shuffle and its augmentation identity, not equality with the specified conjugate of derived inflation adjunctions or resolution naturality of the condensed bar identifications.
- lem-sfb-condensed-product-bar-normalization-naturality vs lem-sfb-derived-composition-adjunction-normalization: the existing generic theorem identifies the derived conjugate on K-injectives, not its equality with the particular augmented shuffle or the signed bar homotopies.
- lem-sfb-condensed-product-bar-resolution-model vs lem-sfb-norm-algcl-bar-augmentation: the latter is a special norm-topological algebraic-closure coefficient theorem asserting that a particular UNDERIVED bar augmentation is an isomorphism; the new task retains derived Hom for arbitrary condensed coefficients and two groups. No such underived substitution is asserted.

The four tasks are strictly smaller than the whole item and divide its implementation work (old argument sizes 2632, 1696, 3323, 3231 characters respectively). No new node is just a new name for the whole item. The exact former steps and original uses appear below so the next workers do not lose any argument or reference.

## Review by N5

I read the current item's eleven steps, the chapter and unit records, the main-20261015 direct-images paragraph (3), and the existing Lean module's theorem/docstring. The direct-images paragraph is only context: I retained the agent proof origin and its missing-reference notice. For the first task I read the full statements of product-action-inflation, sheaf-tensor, internal-abelian-sheaf-module-equivalence, j-shriek-flat, tensor-closed, Grothendieck-enough-injectives, right-adjoint-preserves-injectives and bounded-below-injectives-kinjective. I also read Stacks sites-modules.tex Tag 03EV, label lemma-j-shriek-flat, whose sheaf clause applies to every site object, and Tag 03EO, label lemma-internal-hom-adjoint-tensor. Thus the required flatness concerns a represented profinite set, not a projective condensed module. The small-site monoidal sheafification assumption comes from the cited sheaf-tensor statement and is retained in the setup.

Assembly step 1 uses the first new statement's existence of I, its ordinary injective restrictions, and K-injectivity of I^H; the latter represents RΓ_H^G(N[0]), not an asserted resolution of N^H. Assembly step 2 uses exactly the second statement's common bicosimplicial model and quasi-isomorphism j_D, and gets the normalized direct derived object from the same J. The unchanged original step 3's commuting first-face calculation and original step 4's diagonal faces are assigned to this task. The single-group derived-bar statement says the augmentation is the invariant inclusion, as required.

Assembly step 3 uses exactly the third statement's maps j_K and k and their quasi-isomorphisms, with L and T differentials explicitly fixed. I read internal-bar-resolution: its arbitrary trivial-action tensor-factor clause, not just bare bar exactness, is the input for A[S] tensor A[G^a]. The old proof tests against an H-injective restriction rather than assuming Hom(A[G^a],-) exact. For the outer G augmentation, I^H is termwise G-injective by task 1. I read the full first-quadrant-total-column-comparison statement and Stacks homology.tex Tag 0133, label lemma-double-complex-gives-resolution: every diagonal is finite and both relevant column maps are in the first quadrant. The old (-1)^(bq) and (-1)^(aq) convention changes are preserved verbatim below. The derived-object identification, not only its cohomology, is included in the new statement.

Assembly step 4 uses the fourth statement under the three quasi-isomorphisms established by steps 2–3 and K-injectivity from step 1. I opened both the shuffle statement and derived-composition-adjunction-normalization: the former explicitly asserts S j_D=j_T, and the latter identifies the conjugate on I with C(κ)_I. Product-action-inflation explicitly identifies κ with M^(G×H)=(M^H)^G. Thus the node's normalization compares actual derived arrows. I read Stacks derived.tex Tag 09T5, label lemma-derived-adjoint-functors, and sites-cohomology.tex Tag 0D6E, label lemma-derived-pushforward-composition, as the sources behind the existing general normalization node, not as an exact source for the whole new assertion. For naturality I read lift-exists and lift-unique-up-to-homotopy and their source texts, derived.tex Tags 013P (lemma-morphisms-lift, the degreewise-mono strict-lift clause) and 013S (lemma-morphisms-equal-up-to-homotopy). Their source resolutions are nonnegative injective complexes, precisely the hypotheses here. The signs on the total homotopies are included as conclusions in task 4 and their old calculation is preserved below.

I checked B–E against these files. Each new node is statement-only, all its symbols and hypotheses are introduced, definitions are cited rather than duplicated, and sources admit the agent-formulated gap. The four uses in citations.json quote the actual full new statements verbatim. There is no uncited non-elementary assertion in the short assembly and no reliance on the proof of an unsplit node. New statement-dependency edges only go to existing notions/general results; none goes back to the item. The old module metadata and import/blueprint records were retained, and no SGA source is used.

Small cases: for G=1 or H=1 the unnormalized constant nerve still has positive-degree terms, so none of the new statements kills those terms; the same augmentations apply. For N=0 the zero resolution yields zero maps. For A=0 all modules vanish. For S empty the represented free module is zero and remains flat. For a=b=q=0 both augmentations are the ordinary invariant inclusions, and S_(0,0)=id fixes the normalization. For nontrivial H-cohomology I^H is allowed to have positive cohomology, so there is no accidental replacement of RΓ_H(N) by N^H. These checks retain the original hypotheses, and no projectivity or infinite-product exactness was introduced.

The repair addresses the one return exactly: four new independent queued tasks, with the old arguments below intact, and 1878 characters in the parent assembly (below the 3000-character bound). None of its four proof steps exceeds 2000 characters. The former 10882-character proof was divided rather than shortened away; no mathematical clause or compatibility was dropped. Server preflight results are recorded after validation.

## Preserved argument and task allocation

The following is the original eleven-step proof, verbatim, including every original citation and source. These are implementation notes for the four queued nodes, not proof steps in their unsplit JSON files.

### Original step 1 → lem-sfb-condensed-action-injective-restriction

By [lem-sfb-condensed-product-action-inflation] the three action categories are Grothendieck abelian. Choose a nonnegative injective resolution $N\to I^\bullet$ in $\mathcal A_{G\times H}(A)$, using [lem-sp-grothendieck-enough-injectives] and successive embeddings of the cokernels. By [lem-weil-pbc-bounded-below-injectives-kinjective] this is a K-injective representative of $N[0]$. The exact inflation to $G\times H$ has right adjoint $\Gamma_H^G$, so [lem-sp-right-adjoint-preserves-injectives] makes every $(I^q)^H$ injective in $\mathcal A_G(A)$. Consequently $(I^\bullet)^H$ is also K-injective there, by the same bounded-below lemma. In particular it represents $R\Gamma_H^G(N[0])$, even though it need not resolve the degree-zero module $N^H$.

Original uses: lem-sfb-condensed-product-action-inflation, lem-sp-grothendieck-enough-injectives, lem-weil-pbc-bounded-below-injectives-kinjective, lem-sp-right-adjoint-preserves-injectives.

Original source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), formal product-to-successive augmented internal bar comparison; agent expansion.

### Original step 2 → lem-sfb-condensed-action-injective-restriction

Use [sk-def-sfb-sheaf-tensor] on the small profinite site: abelian sheafification is strong monoidal. Then [def-weil-pbc-internal-abelian-sheaf-module-equivalence] identifies internal $A$-modules with module sheaves over the same section-ring sheaf, preserving underlying sheaves and restrictions. The group actions are the same natural sectionwise families, so this also identifies the action categories. The balanced tensor and internal Hom agree under this equivalence: both balanced tensor products represent the same sectionwise bilinear maps, and their right adjoints agree by the adjunction bijections. We need ordinary injectives after forgetting actions. For a profinite $S$, $A[S]$ is the sheafification of $V\mapsto\bigoplus_{V\to S}A(V)$: maps from this presheaf to a module are precisely maps from the represented condensed set $S$ to its underlying sheaf. Thus it is $j_{S!}A_S$, flat by [lem-pc-sites-modules-j-shriek-flat]. Kernels of equivariant maps inherit their actions by restriction, and cokernels inherit actions on the sheafification of the sectionwise quotient. These constructions satisfy the kernel and cokernel universal properties equivariantly; a zero underlying sheaf has only one action. Hence forgetting actions detects exactness. The left adjoint of restriction $\mathcal A_{G\times H}(A)\to\mathcal A_H(A)$ is $T\mapsto A[G]\otimes_A T$, with $G$ translating the first factor and $H$ acting on $T$. An equivariant map from it is uniquely $[g]\otimes t\mapsto g f(t)$. Flatness makes this adjoint exact. Likewise induction from ordinary modules to $P$-actions is $A[P]\otimes_A-$ for $P=G,G\times H$. By [lem-sp-right-adjoint-preserves-injectives], restriction of $I^q$ to $H$, the underlying $I^q$, and the underlying $(I^q)^H$ are injective. The tensor and Hom used here are the closed module operations of [lem-pc-sheaf-modules-tensor-closed].

Original uses: sk-def-sfb-sheaf-tensor, def-weil-pbc-internal-abelian-sheaf-module-equivalence, lem-pc-sites-modules-j-shriek-flat, lem-sp-right-adjoint-preserves-injectives, lem-pc-sheaf-modules-tensor-closed.

Original source: literature/stacks-project/sites-modules.tex; Tags 03EV (lemma-j-shriek-flat) and 03EO (lemma-internal-hom-adjoint-tensor); explicit induction adjunction and equivariant kernel/cokernel argument.

### Original step 3 → lem-sfb-condensed-product-bar-resolution-model

Set $C^{a,b,q}=\underline{\operatorname{Hom}}_A(A[G^a\times H^b],UI^q)$, with $U$ forgetting both actions. The free universal properties identify $A[P\times Q]$ with $A[P]\otimes_AA[Q]$: maps out of either are the same $A$-bilinear families parametrized by $(p,q)$. The closed adjunction of [lem-pc-sheaf-modules-tensor-closed] then identifies $C^{a,b,q}$ with $\underline{\operatorname{Hom}}_A(A[G^a],\underline{\operatorname{Hom}}_A(A[H^b],UI^q))$. Step 2 and [lem-sp-derived-injective-resolution-naturality] say that the $q$-complex in each bidegree computes exactly the derived internal Hom in the statement. All faces and degeneracies act on this single resolution. The two first faces commute since $(g,1)(1,h)=(1,h)(g,1)$; the other faces and degeneracies only change their own parameters. They also commute with the resolution differential because its maps are equivariant. Thus $C$ is a compatible bicosimplicial nonnegative resolution model of $B(N)$.

Original uses: lem-pc-sheaf-modules-tensor-closed, lem-sp-derived-injective-resolution-naturality.

Original source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), formal product-to-successive augmented internal bar comparison; agent expansion.

### Original step 4 → lem-sfb-condensed-product-bar-resolution-model

Reordering $(G\times H)^n$ into $G^n\times H^n$ identifies the diagonal of $C$ with the single $G\times H$ bar on $I^\bullet$. The diagonal first face acts by $(g_1,h_1)$, because it applies the two commuting actions; an interior face multiplies both adjacent coordinates; the final face drops both final coordinates. The unit insertions agree as well. Apply [lem-sfb-condensed-derived-invariant-bar] to $G\times H$ and $N$: its resolution comparison identifies this diagonal total with $R\Gamma_{G\times H}(N[0])$, normalized by the invariant inclusion. Put $J^\bullet=(I^\bullet)^{G\times H}$. In this model that inclusion gives a quasi-isomorphism $j_D:J^\bullet\to\operatorname{Tot}_\Delta C$ supported in cosimplicial degree zero.

Original uses: lem-sfb-condensed-derived-invariant-bar.

Original source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), formal product-to-successive augmented internal bar comparison; agent expansion.

### Original step 5 → lem-sfb-condensed-successive-bar-quasi-augmentations

For fixed $a,q$ we verify the successive $H$ augmentation without assuming exactness of $\underline{\operatorname{Hom}}_A(A[G^a],-)$. Write $P_{H,b}=A[H^{b+1}]$ with homogeneous $H$-action as in [lem-sfb-condensed-internal-bar-resolution]. Test the augmented $b$-complex on any profinite $S$. Its sections identify, by the closed adjunction, with the ordinary equivariant Hom complex
$$\operatorname{Hom}_{\mathcal A_H(A)}(A[S]\otimes_AA[G^a]\otimes_AP_{H,\bullet},I^q|_H).$$
The tensor factor $T=A[S]\otimes_AA[G^a]$ has trivial $H$-action. The cited bar statement says $T\otimes_AP_{H,\bullet}\to T$ is exact, and step 2 says $I^q|_H$ is injective. Hom into an injective takes this augmented exact complex to an exact cochain complex: each restriction to an image subobject extends across the containing object, and the kernel is the Hom from the quotient. Thus the augmented section complex is exact for every $S$, and so is the sheaf complex. In homogeneous induced coordinates an equivariant map is determined at first coordinate $1$; its other values are $h_0$ times that value. Removing the first coordinate therefore gives the $H$ action face, interior removals multiply adjacent coordinates, and the last removes the last coordinate. Its degree-zero kernel is precisely $\underline{\operatorname{Hom}}_A(A[G^a],(I^q)^H)$. The residual $G$ action respects the augmentation, since it commutes with $H$.

Original uses: lem-sfb-condensed-internal-bar-resolution, lem-pc-sheaf-modules-tensor-closed.

Original source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), formal product-to-successive augmented internal bar comparison; agent expansion.

### Original step 6 → lem-sfb-condensed-successive-bar-quasi-augmentations

Put $K^{a,q}=\underline{\operatorname{Hom}}_A(A[G^a],(I^q)^H)$. The preceding augmentations give a map $k:\operatorname{Tot}_{a,q}K\to\operatorname{Tot}_{a,b,q}C$. To check it is a quasi-isomorphism, first fix $a$ and totalize in $(b,q)$: the augmented rows of step 5 are quasi-isomorphisms from $K^{a,q}$ in $b=0$. Apply [lem-sc-first-quadrant-total-column-comparison] with indices interchanged. The change between the two total conventions multiplies the $(b,q)$ summand by $(-1)^{bq}$, as substitution into $d_b+(-1)^bd_q$ verifies. Now apply the same comparison to the first-quadrant double complexes in $a$ and $b+q$. This proves the claim with the original triple differential $d_G+(-1)^ad_H+(-1)^{a+b}d_q$. Every degree involves only finitely many triples. No product exactness or unbounded convergence assertion is used.

Original uses: lem-sc-first-quadrant-total-column-comparison, def-sp-double-complex-total.

Original source: literature/stacks-project/homology.tex; Tag 0133 (lemma-double-complex-gives-resolution), twice with finite diagonals.

### Original step 7 → lem-sfb-condensed-successive-bar-quasi-augmentations

Apply the homogeneous $G$ bar of [lem-sfb-condensed-internal-bar-resolution] to each $G$-injective $(I^q)^H$. For each profinite $S$ its augmented section complex is $\operatorname{Hom}_{\mathcal A_G(A)}(A[S]\otimes_AP_{G,\bullet},(I^q)^H)$ and is exact by injectivity, exactly as the image-and-quotient argument in step 5. The induced coordinates identify its unaugmented terms with $K^{a,q}$, including the first $G$-action face. The augmentation is $(I^q)^{G\times H}=((I^q)^H)^G$, with the literal equality of [lem-sfb-condensed-product-action-inflation]. By [lem-sc-first-quadrant-total-column-comparison], transposing indices and multiplying by $(-1)^{aq}$ when changing total conventions, these rows give a quasi-isomorphism $j_K:J^\bullet\to\operatorname{Tot}_{a,q}K$. Since $(I^\bullet)^H$ is K-injective in $\mathcal A_G(A)$, its $G$ invariants compute $R\Gamma_G R\Gamma_H^G(N[0])$. Thus $k j_K$ identifies the triple total with this iterated derived object. This argument treats $(I^\bullet)^H$ as a complex, rather than incorrectly applying a module-only bar theorem to it.

Original uses: lem-sfb-condensed-internal-bar-resolution, lem-sfb-condensed-product-action-inflation, lem-sc-first-quadrant-total-column-comparison.

Original source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), formal product-to-successive augmented internal bar comparison; agent expansion.

### Original step 8 → lem-sfb-condensed-product-bar-normalization-naturality

Apply [lem-sfb-bicosimplicial-shuffle-totalization] to $X^{a,b}=C^{a,b,\bullet}$ in the abelian category of internal $A$-modules. It gives the natural diagonal-to-iterated shuffle comparison $S:\operatorname{Tot}_\Delta C\to\operatorname{Tot}_{a,b,q}C$ in the derived category. The inclusion $J^\bullet\to C^{0,0,\bullet}=UI^\bullet$ is killed by both alternating first coface sums, because both groups fix it. The augmentation clause of that lemma therefore gives the equality of actual chain maps $S j_D=k j_K$. This is the augmented product-nerve comparison with $H$ first and $G$ second: its target differential has the ordered signs fixed in the statement, and its restriction along either successive augmentation is the given invariant inclusion. Since $j_D$ is invertible in the derived category, the equality also uniquely determines this comparison there.

Original uses: lem-sfb-bicosimplicial-shuffle-totalization.

Original source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), formal product-to-successive augmented internal bar comparison; agent expansion.

### Original step 9 → lem-sfb-condensed-product-bar-normalization-naturality

Use [lem-sfb-derived-composition-adjunction-normalization] with $L_a:\mathcal A_1(A)\to\mathcal A_G(A)$ the trivial $G$-action inflation, $L_b:\mathcal A_G(A)\to\mathcal A_{G\times H}(A)$ inflation along projection, and $L_c=L_bL_a$. Their right adjoints are respectively $\Gamma_G,\Gamma_H^G,\Gamma_{G\times H}$ by [lem-sfb-condensed-product-action-inflation]. That node also states that the conjugate of the inflation identification is exactly $M^{G\times H}=(M^H)^G$. Thus the normalized derived comparison is represented on $I^\bullet$ by the identity from $J^\bullet$ to $((I^\bullet)^H)^G$. By step 8 the bar comparison, after the identifications of steps 4 and 7, is represented by this same identity. The asserted equality of derived arrows follows; equality of cohomology maps alone has not been substituted for it.

Original uses: lem-sfb-derived-composition-adjunction-normalization, lem-sfb-condensed-product-action-inflation.

Original source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), formal product-to-successive augmented internal bar comparison; agent expansion.

### Original step 10 → lem-sfb-condensed-product-bar-normalization-naturality

For $N\to N'$ choose a lift between the nonnegative equivariant injective resolutions using [lem-weil-pbc-injective-resolution-lift-exists]. It gives maps of $C,K,J$ commuting with all augmentations and the shuffle. By [lem-sp-derived-injective-resolution-naturality], these maps represent the stated derived maps. Two choices of lift are homotopic by [lem-weil-pbc-lift-to-injective-unique-up-to-homotopy]. Their postcomposition homotopies commute with the group operators. Multiply the homotopy on $C^{a,b,q}$ by $(-1)^{a+b}$ (on the diagonal by $(-1)^n$); the group-differential cross terms then cancel and the total homotopy equation is the original equation in resolution degree. The same argument applied to the identity of $N$ between two resolutions proves independence of the choice. This establishes naturality of the derived objects and of the comparison arrow.

Original uses: lem-weil-pbc-injective-resolution-lift-exists, lem-sp-derived-injective-resolution-naturality, lem-weil-pbc-lift-to-injective-unique-up-to-homotopy.

Original source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), formal product-to-successive augmented internal bar comparison; agent expansion.

### Original step 11 → lem-sfb-condensed-product-bar-normalization-naturality

If $G=1$ or $H=1$, all formulas still use the unnormalized constant group nerve in that direction; its positive alternating terms need not be zero. The bar augmentations of steps 5 and 7 and the shuffle lemma include a constant direction, so the same derived identifications and normalized comparison apply. If $N=0$, choose the zero resolution and every displayed complex and map is zero. Every parameter power is profinite in the fixed site and universe bound; all total diagonals are finite. At no point has internal Hom been replaced by sections of an underived continuous-function complex, nor has a free module on an arbitrary profinite set been assumed projective.

Original uses: .

Original source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), formal product-to-successive augmented internal bar comparison; agent expansion.

## Validation

The required deliver.py --no-push process exited 0 and printed OK (not pushed) at 3951a12a260: server preflight passed, including check_dag and review_split. Local metadata inspection confirmed the item statement is unchanged, the four new nodes have no proof/proof_deps, and assembly step lengths are 383, 456, 454 and 585 characters (1878 total). This validation entry and the corrected source line number are the only report changes after that successful dry run; the final dry run checks this report version before push. No compiler or build was run.
