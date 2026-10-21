# Stage-1 direct delivery: Q72

## Files written

- dag/nodes/sec-six-functors-basics/det-lem-int-integral-heart-triangulated.json: unchanged statement; four assembly steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-residue-class-triangle-closure.json: statement-only, status unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-derived-degree-zero-abelian-criterion.json: statement-only, status unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-stratified-constant-model-product-bound.json: statement-only, status unsplit; no Mathlib match.
- citations.json: verbatim current statements for every assembly-step citation.

## Attachments

None. I searched the item tag and notions throughout lean/WeilConjectures and read lean/Sheaf/Paper/IntegralConstantModelHeart.lean. The theorem AlgebraicGeometry.ProEtale.integralConstantModelHeart ends in sorry. The upstream field-coefficient heart declarations concern another coefficient category. The upstream ConstructibleEmbedding module has a proved joint-unit monicity lemma and an embedding into products of presentation pushforwards, but not the particular small family of stratum-representative products and image subsheaves stated in the new size node. Its essential-smallness conclusion alone does not state that stronger interface.

## WANTED

None. The blueprint, Stacks source and local Lean/Mathlib sources used below are present.

## What was wrong and what changed

The human explicitly returned this already reviewed node for granularity, not for a false statement. I leave its statement, statement dependencies, Lean records, import flags, blueprint fields and accepted tool_uses intact. The original proof has 9962 characters, including a substantial set-theoretic/gluing argument. The new assembly has 2078 characters and has no hidden long proof step. Three independent arguments are now new unsplit statements. No Lean is written and no compiler or Lake command is run.

The original proof's warning about Stacks 09C2 remains important: Tag 09C2 is proetale.tex, lemma-describe-constructible-complexes, whose surrounding D_cons definition includes finite Tor dimension. It is not a theorem that arbitrary bounded residue reduction forces boundedness without additional hypotheses. Our assembly takes boundedness from the current cohomological definition, as the earlier reviewed proof did. No dispute or statement correction is necessary.

## Not duplicates

lem-sfb-integral-residue-class-triangle-closure vs det-lem-int-integral-heart-triangulated: The new statement concerns an independently specified completeness/residue-origin predicate on any scheme; it has no Dbc comparison, boundedness or truncation conclusion, nor any heart or size conclusion. The item must supply the Noetherian comparison and transport the closure.

lem-sfb-integral-residue-class-triangle-closure vs sk-lem-integral-models: The existing node identifies two integral coefficient categories under finite-type hypotheses; it does not assert triangle closure of the residue predicate on arbitrary schemes.

lem-sfb-integral-residue-class-triangle-closure vs det-pe-derived-nakayama-first-reduction: That node gives only completeness closure and zero detection, not finite-coefficient constructibility or etale-origin closure of derived reductions.

lem-sfb-integral-residue-class-triangle-closure vs lem-weil-proetale-dbc-triangulated: That node is about finite-coefficient complexes; it does not assert completeness or closure for complexes over the completed integral coefficient sheaf.

lem-sfb-integral-residue-class-triangle-closure vs lem-weil-pbc-uniform-complete-triangulated: That node uses a compatible uniformly bounded adic tower with common models, on finite-dimensional Noetherian schemes with l invertible; the new statement uses only first-residue origin and does not assume or construct such a uniform tower.

lem-sfb-derived-degree-zero-abelian-criterion vs det-lem-int-integral-heart-triangulated: The new criterion works in any abelian derived category with any cohomology-stable strictly full triangulated subcategory. It proves no integral constructibility, boundedness, truncation stability or smallness; these hypotheses and conclusions are supplied separately in the item.

lem-sfb-derived-degree-zero-abelian-criterion vs prop-weil-heart-abelian: That node assumes a t-structure already constructed. The new criterion starts with triangle and cohomology closure and supplies the ambient kernel/cokernel identifications and full degree-zero essential-image statement without assuming a t-structure.

lem-sfb-derived-degree-zero-abelian-criterion vs lem-sfb-weak-serre-bounded-thick: That result goes in the opposite direction: a weak Serre subcategory is assumed and gives thickness of its bounded derived cohomology class. Here no abelian heart is assumed and boundedness is not required.

lem-sfb-derived-degree-zero-abelian-criterion vs lem-sfb-integral-constant-model-heart-closure: That node asserts closure for a specific integral constructible class; it has no abstract triangulated-subcategory criterion and no full single-functor identification.

lem-sfb-stratified-constant-model-product-bound vs det-lem-int-integral-heart-triangulated: The new node supplies specified product targets and set-indexed image subobjects, with explicit adjunction-unit embeddings. It does not assert that those images are constructible or that the heart is abelian or is a degree-zero category; the item filters the set of images to deduce its smallness clause.

lem-sfb-stratified-constant-model-product-bound vs lem-sfb-locally-prescribed-modules-small: That generic local counting lemma is reused; it does not choose the global stratum-product targets, prove their unit embeddings monic, or bound their image subobjects.

lem-sfb-stratified-constant-model-product-bound vs lem-sfb-joint-adjunction-model-embedding: That abstract lemma is reused to prove monicity for each fixed tuple. It does not provide a small family of stratum sheaves or of all target tuples and image subobjects.

lem-sfb-stratified-constant-model-product-bound vs lem-sfb-constructible-module-objects-essentially-small: That node concludes essential smallness for the arbitrary locally finitely presented internal-module class; it does not state the particular stratum-representative product targets, prescribed unit maps, and image-subsheaf parametrization needed here.

lem-sfb-stratified-constant-model-product-bound vs det-lem-coefficient-heart-small: That node concerns E and Qlbar, not the integral ring, and only asserts essential smallness, not the explicit product/subobject interface.

## Search audit

Before writing the new nodes I searched the whole DAG by statement phrases and tag 09C2, inspected the existing local-model smallness, joint-adjunction embedding, constructible module smallness, uniform-complete triangulation and weak-Serre nodes, and ran tools/blueprint_refs.py ancestor and search for local model, essentially small, adjunction unit, jointly monomorphic, locally prescribed, derived complete, degree-zero subcategory, jointly detect zero, residue triangle, triangulated subcategory, finite products, stratum direct, abelian criterion, integral constructible category, constant-model product, residue-class and cohomology-stable. The broad search hits were compared by their statements, not titles. No blueprint node states one of the three new interfaces exactly or as a more general theorem.

All new-node Mathlib searches are actual msearch.py calls retained in searches.jsonl. I read the hits. For residue closure the hits provide ambient triangulation or cohomological bounds, not completed integral coefficients with finite etale residue origin. For the abstract degree-zero criterion I read Mathlib/CategoryTheory/Abelian/Subcategory.lean lines 25–63: the instance at lines 60–62 takes kernel, cokernel and finite-product closure as inputs; the substantial cone/extension and essential-image argument is not supplied by a one-line specialization. For the size interface I read Mathlib/CategoryTheory/Subobject/WellPowered.lean lines 50–77: these results count subobjects of a fixed object but do not supply the set of stratum-product targets or the explicit unit monomorphisms. The other finite-presentation hits concern general local sheaf presentations, not constant scalar models and their stratum products. No search is invented and no unavailable service is treated as an empty result. Existing item searches are retained unchanged.

## Independent work packages and preserved argument

The following is a handoff, not proof steps in the new unsplit nodes. Future workers can carry out the three arguments independently.

1. lem-sfb-integral-residue-class-triangle-closure carries old steps 1–3 below except for the finite-type/Noetherian verification and the comparison theorem, which stay in assembly step 1. Use residue-field finiteness, cone/shift closure of completeness, exact derived scalar extension, finite-coefficient triangulation and finite-ring etale origin. These are the five different existing nodes cited below; do not identify the completed ring with the constant coefficient ring. Rotation proves all three positions of the two-out-of-three assertion. Zero and isomorphism invariance follow from the two defining conditions. No geometry beyond existence of the small site is used.

2. lem-sfb-derived-degree-zero-abelian-criterion carries old step 4's single-complex/degree-zero identification and all of old steps 5–6. Use the full faithfulness, concentration, cone long exact sequence, cone formula, and short-exact-complex triangle nodes cited below. The cohomology-single hypothesis replaces the integral local-model theorem in this abstract setting. It supplies membership of the two cone cohomologies, and every ambient inverse is in the full subcategory. Finite sums follow from the cone of zero, and images/coimages are ambient, so the canonical comparison remains an isomorphism. No smallness is asserted. Boundedness and truncations stay in assembly step 2.

3. lem-sfb-stratified-constant-model-product-bound carries old steps 7–9 in full. Reuse lem-sfb-locally-prescribed-modules-small for the single-stratum counting argument and lem-sfb-joint-adjunction-model-embedding for the exact adjunction-unit kernel argument; neither is recreated. The small family of scalar models consists of cokernels of finite matrices over O_E, not arbitrary morphisms with functions as entries. To apply the local counting node on slice sites, use the pro-etale localization identification and the cartesian coefficient isomorphism; these are already represented by lem-weil-proetale-weakly-etale-localization and sk-prop-sfb-cartesian-coefficients, as in the existing det-brown-hypotheses-small step 5. Count the locally closed scheme strata within the fixed smaller bound. Apply exact stratum pullbacks and the canonical underlying-sheaf identification, then lem-weil-pbc-noetherian-stratum-detection on underlying abelian sheaves, to verify joint zero detection. Do not assume a_s^* a_{s*} is the identity. Images are counted sectionwise as in the old argument; no effectivity of arbitrary descent data is needed.

### Original nine steps, preserved verbatim

Old step 1:

Put $R=R_X$ and $\kappa=\mathcal O_E/\pi_E$. The residue field $\kappa$ is finite by [lem-weil-l-adic-extension-integers-dvr](3), and $\pi_E\mathcal O_E=\mathfrak m_E$ by the choice of uniformizer. By [sk-lem-integral-models](2), an ambient $R$-complex belongs to $\Dbc(X,\mathcal O_E)$ if and only if it is derived complete and its derived reduction $K_1=K\otimes_R^{\mathbf L}\kappa_X$ is a bounded constructible complex pulled back from the étale site. This is a theorem identifying the cohomological definition with the residue criterion, not a redefinition of $\Dbc$. Its hypotheses hold: $\operatorname{Spec}k$ is locally Noetherian because the only ideals of the field $k$ are $0$ and $k$. Apply [pqf-lem-locnoeth-lft] to the structure morphism to obtain local Noetherianity of $X$. Its finite-type hypothesis makes $X$ quasi-compact, since the inverse image of the affine target $\operatorname{Spec}k$ is all of $X$ [def-weil-finite-type-morphism]. Thus $X$ is Noetherian, and $E/\mathbf Q_\ell$ is finite as required. The zero complex satisfies both conditions and hence belongs to $\Dbc$.

Uses: lem-weil-l-adic-extension-integers-dvr, sk-lem-integral-models, pqf-lem-locnoeth-lft, def-weil-finite-type-morphism.

Old step 2:

For $K\in\Dbc$, its shifts $K[n]$ remain derived complete by [det-pe-derived-nakayama-first-reduction]. Derived scalar extension is an exact triangulated functor by [lem-pur-derived-change-of-rings](2), so $(K[n])_1\simeq K_1[n]$. Bounded intrinsically constructible finite-coefficient complexes are shift-stable by [lem-weil-proetale-dbc-triangulated]. Every such bounded complex has bounded constructible étale origin by [lem-weil-pbc-finite-ring-constructible-derived-origin], applied to the finite commutative ring $\kappa$. Thus the residue criterion of step 1 gives $K[n]\in\Dbc$ for every integer $n$.

Uses: det-pe-derived-nakayama-first-reduction, lem-pur-derived-change-of-rings, lem-weil-proetale-dbc-triangulated, lem-weil-pbc-finite-ring-constructible-derived-origin, sk-lem-integral-models.

Old step 3:

Let $K\to L\to M\to K[1]$ be an ambient distinguished triangle with $K,M\in\Dbc$. Rotate it to $M[-1]\to K\to L\to M$. By step 2 and cone closure of derived complete complexes [det-pe-derived-nakayama-first-reduction], $L$ is derived complete. Apply exact derived reduction [lem-pur-derived-change-of-rings] to the original triangle. The outer vertices $K_1,M_1$ have bounded constructible cohomology. The outer-vertex closure in [lem-weil-proetale-dbc-triangulated] gives the same for $L_1$. The finite-ring origin theorem [lem-weil-pbc-finite-ring-constructible-derived-origin] supplies its bounded constructible étale representative. Hence [sk-lem-integral-models](2) gives $L\in\Dbc$. This works for arbitrary ambient triangles and morphisms. Together with zero and all shifts, it is precisely the full-triangulated-subcategory criterion of [def-weil-triangulated-subcategory], so the ambient distinguished triangles and shifts give the asserted triangulation and exact inclusion.

Uses: det-pe-derived-nakayama-first-reduction, lem-pur-derived-change-of-rings, lem-weil-proetale-dbc-triangulated, lem-weil-pbc-finite-ring-constructible-derived-origin, sk-lem-integral-models, def-weil-triangulated-subcategory.

Old step 4:

Boundedness is already part of the current cohomological definition [sk-def-sfb-constructible]: $\Dbc$ consists of bounded complexes with constructible cohomology sheaves. This avoids applying a bounded-reduction assertion without its completeness hypothesis. Both standard truncations remain in $\Dbc$ by [det-lem-int-integral-heart-local-model](3). By the same definition a module placed in degree zero belongs to $\Dbc$ exactly when it belongs to $\Cons$. Conversely, if $K\in\Dbc$ has cohomology only in degree zero, [lem-sf-derived-concentrated-single] with $r=0$ identifies $K$ with $H^0(K)[0]$. Its cohomology is constructible by the definition. The degree-zero single-complex functor is fully faithful by [lem-weil-pbc-derived-single-fully-faithful]. Thus it identifies the full module category $\Cons$ with precisely the full subcategory of degree-zero objects of $\Dbc$, including all their morphisms.

Uses: sk-def-sfb-constructible, det-lem-int-integral-heart-local-model, lem-sf-derived-concentrated-single, lem-weil-pbc-derived-single-fully-faithful.

Old step 5:

Let $f:C\to C'$ be a morphism of constructible $R$-modules and let $D$ be its cone in the ambient derived category. The triangulation proved above, rotated if necessary, implies $D\in\Dbc$. The long exact cohomology sequence [lem-sf-derived-homology-long-exact] of $C[0]\to C'[0]\to D\to C[1]$ reads $0\to H^{-1}(D)\to C\xrightarrow f C'\to H^0(D)\to0$, since $C[0],C'[0]$ have no other cohomology. Thus the ambient kernel is $H^{-1}(D)$ and the ambient cokernel is $H^0(D)$. By [det-lem-int-integral-heart-local-model](2) these sheaves placed in degree zero lie in $\Dbc$, so step 4 puts both in $\Cons$.

Uses: lem-sf-derived-homology-long-exact, det-lem-int-integral-heart-local-model.

Old step 6:

The full subcategory $\Cons$ contains zero and finite direct sums: the cone formula of [def-weil-abstract-derived-category] makes the cone of the zero map $C[-1]\to C'$ equal to $C'\oplus C$ in degree zero, so the triangulation and the degree-zero identification already proved put it in $\Cons$. It inherits addition on morphisms from modules. The kernel and cokernel from step 5 have their ambient universal properties in this full subcategory. Its images and coimages are therefore the ambient ones, and their canonical comparison is an ambient isomorphism with inverse again a morphism of the full subcategory. Hence $\Cons$ is abelian. For an ambient short exact sequence $0\to C'\to C\to C''\to0$ with constructible ends, [lem-weil-pbc-complex-ses-triangle] applied to the degree-zero complexes gives a distinguished triangle $C'[0]\to C[0]\to C''[0]\to C'[1]$. Step 3 puts $C[0]$ in $\Dbc$ and step 4 puts $C$ in $\Cons$, proving closure under ambient extensions.

Uses: def-weil-abstract-derived-category, lem-weil-pbc-complex-ses-triangle, sk-def-sfb-constructible.

Old step 7:

We now supply the set of local data rather than assuming it classifies global gluings. Fix one stratum $S$. In the size convention [def-weil-size-convention], its pro-étale site has a fixed small skeleton [def-weil-pbc-proetale-site]. By [sk-def-sfb-constructible](1), a finite constant local model sheaf is locally $\mathcal O_{E,U}\otimes_{\mathcal O_E}P$ for a finitely presented scalar module $P$. Representatives for such $P$ form a set: use the cokernels of all finite matrices over the set $\mathcal O_E$. Cover families in a small site can be chosen from a set (discard repeated arrows), and assignments of these scalar presentations form a set. For each overlap $W=U_i\times_SU_j$, an overlap module map between the fixed model sheaves $A,B$ is a family in $\prod_{(V\to W)}\operatorname{Map}(A(V),B(V))$, subject to naturality and linearity; the index is the object set of a small slice site and all factors are sets in the chosen universe. Invertibility imposes a further condition on this set of maps. Thus the overlap isomorphisms also form a set. These data determine a sheaf up to isomorphism: for two realizations with the same data, at every test object $V\to S$ use the local identifications on $V\times_SU_i$ and their overlap agreement to glue a unique map on sections; glue their inverses in the same way. The equalizer sheaf axiom in [def-weil-pbc-sites-and-cohomology](1) proves these maps are inverse and natural, and they are module-linear locally and hence globally. The module structures and morphisms are the sectionwise ones of [def-weil-sheaf-of-modules-category]. Consequently there is a set of isomorphism classes of finite constant local model sheaves on each fixed $S$. No effectivity assertion for arbitrary data is needed: retain only data that have a realization.

Uses: def-weil-size-convention, def-weil-pbc-proetale-site, sk-def-sfb-constructible, def-weil-pbc-sites-and-cohomology, def-weil-sheaf-of-modules-category.

Old step 8:

For a finite stratification $(a_s:S_s\to X)_s$ and chosen local-model sheaves $F_s$ from step 7, put $P=\prod_s a_{s*}F_s$, a finite product of $R$-module sheaves. These are the module direct images and adjunctions $a_s^*\dashv a_{s*}$ of [sk-def-sfb-module-pushforward-pullback], with the pulled-back coefficient identifications of [sk-prop-sfb-cartesian-coefficients](1). Its final assertion makes every $a_s^*$ exact and canonically naturally isomorphic to the lift of $a_s^{-1}$ on underlying abelian sheaves, with the $\mathcal O_{E,S_s}$-action obtained through $\alpha_{a_s}^{-1}$. Here we use only the untwisted admissible coefficient $\mathcal O_E$, so none of the extra hypotheses for the Tate-twist clause is needed. For a constructible $C$, choose isomorphisms $\varphi_s:a_s^*C\xrightarrow{\sim}F_s$. Define $u:C\to P$ by its components $u_s=a_{s*}(\varphi_s)\circ\eta_{s,C}$, where $\eta_s$ is the adjunction unit. Let $N=\ker u$. For each $s$, exactness of $a_s^*$ makes $a_s^*N$ the kernel of $a_s^*u$. The component $a_s^*u_s:a_s^*C\to a_s^*a_{s*}F_s$ has the explicit left inverse $\varepsilon_{s,a_s^*C}\circ a_s^*a_{s*}(\varphi_s^{-1})$, where $\varepsilon_s$ is the adjunction counit: its composite with $a_s^*u_s$ is $\varepsilon_{s,a_s^*C}\circ a_s^*\eta_{s,C}=\mathrm{id}_{a_s^*C}$ by the triangle identity. Thus $a_s^*u_s$ is monic; since it is a component of $a_s^*u$, that map has zero kernel. Hence $a_s^*N=0$ for every $s$. The precise underlying-sheaf identification above therefore gives $a_s^{-1}U(N)=0$ for every $s$, where $U$ forgets the module action. The finite-stratum zero-detection statement [lem-weil-pbc-noetherian-stratum-detection], applied to $U(N)$ with the identity covers on the strata and the Noetherianity proved in step 1, gives $U(N)=0$, hence $N=0$. Thus $C\to P$ is monic. Notice that we only need the split monomorphism furnished by the adjunction, not a claim that $a_s^*a_{s*}$ is the identity.

Uses: sk-def-sfb-module-pushforward-pullback, sk-prop-sfb-cartesian-coefficients, lem-weil-pbc-noetherian-stratum-detection.

Old step 9:

There is a set of finite stratifications of the fixed scheme $X$: the locally closed subsets form a set, and their bounded scheme structures and immersion maps are sets in the chosen universes. Step 7 gives a set of possible tuples $(F_s)_s$ for each stratification, hence a set of possible sheaves $P$ in step 8. For each fixed $P$, its subobjects form a set directly: kernels of module sheaf morphisms are sectionwise by [def-weil-sheaf-of-modules-category], so a monomorphism is sectionwise injective; identify it with its image subsheaf. Such an image is specified by a subset of $P(V)$ for each object $V$ of the fixed small site, subject to the module, restriction and sheaf axioms. All such choices lie in the set $\prod_V\mathcal P(P(V))$. Therefore subobjects of all these $P$ form a set, and by step 8 they contain representatives of every constructible sheaf. Its isomorphism classes form a set, as required. For the empty scheme, the empty stratification gives the terminal, zero module sheaf and the same argument applies.

Uses: def-weil-size-convention, def-weil-sheaf-of-modules-category.

## Review by Q72

I read the item statement and all nine old proof steps, the main-20261015 node statement and proof, and the chapter and integral-heart unit records. The unit route uses completeness and finite residue reduction, cohomology/local models for truncations and heart, then finite stratification and small-site gluing data for size. Those are the same three work packages, and the unchanged item still uses that route. I read the Lean theorem and its docstring; its proof is sorry, so this deliberate re-split is not superseded by a finished upstream proof.

For new node 1 I read blueprint paragraph (1), the finite-ring origin and pro-etale triangulation statements, the derived-completeness first-reduction statement and the change-of-rings statement. The finite residue field comes from the coefficient DVR; it is not an assumption on an infinite coefficient ring. The new lemma is about the completed ring throughout and its proof does not need Noetherianity. The main comparison does: assembly step 1 verifies it using the literal locally-Noetherian transfer statement and the literal definition of finite type before applying integral-models(2). I checked that integral-models(2) says an equivalence with exactly completeness and bounded etale-origin residue, not merely one implication. The new residue closure statement supplies every closure used by that assembly step.

For new node 2 I read blueprint paragraph (2), the concentration and fully faithful single-functor statements, the long exact cohomology statement, the cone formula and the complex short-exact triangle statement. The abstract assumption explicitly supplies H^q(K)[0] membership, so no truncation-stable t-structure is smuggled in. In assembly step 2 the local-model theorem's clauses (2) and (3) literally give that cohomology membership and both truncations, and constructibility's definition gives boundedness. In assembly step 3 the module category is abelian by the sectionwise module-category statement, and the same constructibility definition identifies B with Cons. Thus the abstract criterion gives all the asserted heart clauses under hypotheses actually verified. The Mathlib abelian-subcategory instance alone is insufficient until its closure hypotheses are established.

For new node 3 I read blueprint paragraph (2)'s size sentence, Stacks sites.tex Tag 04TQ lemma-glue-maps (unique local gluing of morphisms), and the full statements of the existing local-prescribed-smallness and joint-adjunction-model-embedding nodes. I also read the cartesian coefficient, module adjunction and finite stratum zero-detection statements used in the preserved handoff. The first gives exact pullback together with its underlying abelian-sheaf identification, so the detection statement applies to the kernel's underlying sheaf; it is not an unsupported module detection assertion. A single fixed product does not bound the whole category without first counting all stratifications and tuples, so the new statement requires that set as well as the subobject sets. Assembly step 4 uses precisely the new statement's small family and explicit monomorphisms; taking an image identifies C with one of its small family of subobjects. Filtering for constructible images is a subset operation, not a gluing theorem. This also explains why the existing essential-smallness node is not being treated as a statement of explicit embedding targets.

I checked small cases: empty X gives the empty stratification and zero product; no connectedness or nonempty stratum hypothesis is imposed. Zero complexes and zero maps satisfy the residue and cone statements; an isomorphism has zero cone. For multiplication by pi on O_E the cone cohomologies give kernel 0 and cokernel O_E/pi, so integral torsion is included rather than accidentally excluded. The abstract degree-zero criterion works for T=0 and T=D(A). The size argument allows arbitrary overlap automorphisms and keeps only realizable descent data. I corrected a C4-style citation in new node 1 before final delivery: sk-def-sfb-change-of-scalars defines ordinary extension, so the derived tensor now cites sk-def-sfb-derived-tensor-hom and the actual derived scalar-extension functor cites lem-pur-derived-change-of-rings(2). Its mathematical assertion is unchanged. I used no SGA source. Every assembly citation has a verbatim quote in citations.json. The new node statements introduce all their own objects and hypotheses, contain no proofs, have empty proof dependencies, and do not depend on the item. Their mathematical arguments and the old argument are available above for the workers; the assembly itself contains no step longer than 2000 characters.

## Unfinished work

The proofs of the three new statements are intentionally left unsplit, as the human requires for parallel work. The item itself is fully assembled. There are no additional missing documents or unresolved mathematical claims beyond those three designated work packages.

## Validation

The first required deliver.py --no-push exited successfully with OK at 36d14e8297f. The subsequent reference correction is rechecked in a new dry run before push.
