# Stage 1 repair: lem-cbc-coherent-square-comparison-data

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-coherent-square-comparison-data.json`: repaired statement and six proof steps; status split.
- `dag/nodes/sec-smooth-purity/lem-cbc-hom-functor-composition-coherence.json`: one new statement-only node, status unsplit, no Mathlib match.
- `citations.json`: local verbatim-citation check input. Since deliver.py does not package this file, its full content is reproduced below under “Delivered citation evidence”.

The sandbox's returned item, report, citations and searches were read before editing. The original returned JSON is retained in `work/returned-item.json` as local repair evidence. The current repository has the original item unsplit; compared with the retained sandbox, only the split-owned proof fields differed before this repair. Its source statement and inherited chapter/unit/blueprint ancestry agree. No reviewed live split or attachment was overwritten. Packaging uses the delivery tool's fresh origin overlay rather than any git operation in the shared read-only tree.

## Attachments

None. Searches of the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, coherent nerve, rigidification, pinched spaces, and Hom bifunctors found no exact finished declaration for this item or the new node. The related Mathlib nerve construction is not a project attachment. No declaration of upstream master with sorry was treated as a finished proof.

## WANTED

WANTED: archived Lurie, Higher Topos Theory, Theorem 2.2.5.1 and Proposition 2.2.4.1, for the replacement and actual alpha mapping comparisons. The relevant statements were inspected in the existing DAG; no HTT archive was found in literature/.

WANTED: archived Kerodon 046J, 03PD, 03N3 and 0309 for the new composition-normalized Hom interface, and 03N6/03N7 and 03MT for the enriched Hom/twisted-arrow identification. I read these online, as well as 03N2 and Subsection 4.6.7 (01LA). These are Kerodon identifiers, not Stacks tags. The source statements at 046J/03PD concern one functor; they are not falsely cited as already asserting functor-composition coherence. No Stacks tag states this quasicategorical result. The boundary-cube expansion remains agent-written, and no SGA source is used.

## STATEMENT-DISPUTED: unspecified commutation and parameter naturality

The imported statement leaves the homotopy H in (i) unnamed and asserts “natural in p,e,a, retaining higher simplices” without defining a category of varying functors p or the corresponding morphisms. That phrase is not a typed naturality assertion. Moreover an arbitrary homotopy cannot substitute for the chosen one when comparing coherent squares: even when A=U=V is a point and Z is K(Z,1), the square's commutation homotopy can be any loop at the base point, and distinct loop classes do not admit a relative-endpoint comparison with the four side faces held constant. This example diagnoses the missing specification, not a counterexample to the intended normalized comparison theorem.

As requested in return point 4, the statement now specifies H to be the canonical naturality homotopy of p_* and H-prime that of (W_p)_*, in a single simultaneous twisted-arrow normalization. The unsupported global phrase is replaced by the precise restriction to this fixed finite diagram. The parent uses the cube data, not global naturality in p. The general Cartesian criterion still has an unspecified “canonical map” in its statement; the intended interpretation for the parent is its canonical postcomposition/naturality square, not an arbitrary choice of loop H. I have not edited that unowned node or the parent. This clarification should be retained when their interfaces are formalized.

The unspecified possible zigzag is replaced by actual map representatives of the coherent Hom equivalence at the four Kan corners. Thus the second comparison is direct and no unexplained intermediate squares are required. The two cubes, their corner equivalences, and all hypotheses needed by the parent are retained. This is an explicit interface repair; the unsupported statement clause was not silently retained.

## Return points repaired

1. C4/E5, old Step 2: the new composition-coherence node specifies the comparison of t_(UT) with t_U t_T, normalized constant on the actual equal corner maps. New Step 2 applies it to the two factorizations alpha_B p and W_p alpha_E. It writes both pasted paths, identifies their common h_(alpha_B p), and composes the relative-endpoint homotopies. The old single-functor citation is no longer used for this stronger fact.
2. C4/E5, old Step 3: new Steps 4–5 cite the existing enriched-Hom/twisted-arrow equivalence and the full transport mapping-space comparison. The former explicitly says it is natural for simplicial functors and respects higher pre/postcomposition, while the latter explicitly preserves composition and pullback. Applying them to the enriched transformation induced by Rp compares that transformation with the same normalized (W_p)_*. Restricting this comparison in the arrow functor category to the edge (id_a,alpha_E e) gives a transformation of square diagrams. The coherent cube has the constant enriched source face and the prescribed target face. Step 5 spells out its six-tetrahedron boundary restriction instead of asserting that unrelated composition witnesses agree.
3. C4, alpha corner equivalences: new Step 3 explicitly cites lem-coef-rigidification-postcomposition-comparison. Its first paragraph says that alpha is a categorical equivalence and that its actual map of right-pinched mapping spaces is a weak equivalence. The replacement statement alone is not used for this conclusion.
4. C4, unspecified H and parameter naturality: repaired as in STATEMENT-DISPUTED above. No inner-fibration or Cartesian-edge hypothesis was added to this item. These hypotheses belong only to the consumer that uses it.

C8/shape: split_report.tool_uses declares the five generic statements from sk-prop-sf-biduality-general. They are foundations for the same Cartesian mapping-square branch, not replacements for the compact-support unit route. Definitions and same-unit Kan functor-space input are kept as such. All proof dependencies equal the union of step uses. The citation audit is delivered in the report itself, not only referenced as a local file.

## Review by NC

I read the chapter sec-smooth-purity and unit sk-prop-sf-cbc, the current main-20261015 ancestor thm-cbc-finite-level-proetale.proof.md, the entire parent lem-cbc-coherent-cartesian-postcomposition, and the coherent-cube invariance and Cartesian criterion consumers. The ancestor proves finite-level site transport and contains no proof of this categorical auxiliary comparison; accordingly I keep agent proof origin and preserve the historical ancestry rather than attribute the new argument to a nonexistent sentence. I compared all original and newly used dependency statements with the uses below. Online Kerodon 046J/03PD confirms the return's distinction between object-variable naturality and composition in the functor. Kerodon 03N3/0309 explains the normalized Hom universal property; 03N6/03N7 identifies the enriched Hom model. The new node records the additional composition refinement honestly as an agent-formulated, still-unsplit lemma.

Step 1 takes the object-preserving functorial locally Kan replacement and the coherent-nerve adjunction from lem-coef-coherent-nerve-comparison; the right-pinched simplices from def-cbc-enhanced-diagrams-cones; the postcomposition action from lem-coef-infinity-hom-bifunctor-functoriality; and the simultaneous normalization from the new node. The equality of alpha composites follows by adjunction from Rp r_E = r_B C[p] on every simplex. All categories are small in containing fixed universes and both E and B are quasicategories, so the cited interfaces apply. The naturality homotopies are fixed here, before any comparison.

Step 2 uses only the new lemma's actual composition clause, which explicitly gives a relative-endpoint homotopy comparing h_(UT) with U h_T followed by h_U T. Applying it to the two factorizations produces the two paths printed in the step; the equality of the composite simplicial maps identifies their h_(UT). The two vertical side faces are constant because applying equal functors to a right-pinched simplex gives exactly equal simplices. This is the missing argument of return point 1, now isolated at its genuine general lemma rather than disguised as naturality of one functor.

Step 3 uses the alpha-induced weak-equivalence clause of lem-coef-rigidification-postcomposition-comparison for all four pairs. Its hypotheses are small quasicategories and an object-preserving locally Kan replacement; these are exactly those constructed. No full-faithfulness assertion was attributed to the wrong node.

Step 4 constructs the enriched transformation explicitly by F(vtu)=F(v)F(t)F(u). The first sentence of the enriched-Hom/twisted-arrow result identifies the classifier, and its final sentence supplies naturality for F and the higher action homotopies. The full mapping-space equivalence in space-transport-classification says that this comparison is coherent and compatible with composition and pullback. These two statements identify whole transformations, so restriction in the arrow functor category is licensed. The normalization in the new lemma ensures that the target is exactly the H-prime already fixed, rather than some unrelated homotopy. Locally Kan is satisfied for A=RD_E and C=RD_B. F preserves the vertex r_E[e] by replacement naturality, so the enriched face is constant exactly as claimed.

Step 5 takes the corner comparison and its normalization on vertices from the enriched-Hom statement and its weak equivalence from the coherent-nerve mapping equivalence statement. In the chosen space model S=N_hc(Kan), components of a coherent transformation are actual maps of Kan complexes; hence a direct representative is available. A transformation of square diagrams includes the prism, so its six tetrahedra restrict to the six faces named H,H-prime,L,M,N,O. Their shared faces agree, giving the stated two boundary paths with fixed endpoints. Fun(A,Z-prime) is Kan by lem-cbc-kan-functor-space-kan, which permits representation after fillers. This step reads the coherence already present in the transformation; it does not infer a cube from an equality on pi_0. Step 6 merely assembles the two established comparisons.

I tested the new composition lemma with an identity functor, an identity edge, discrete ordinary categories, empty Hom spaces and the terminal quasicategory. Composition of actual simplex maps is strict in each case; the new comparison can be degenerate for identities, and no nonemptiness is assumed. For the item I checked p=id, e degenerate, B=Delta^0, and empty corner spaces. These introduce no extra hypotheses; where an edge and a point supply postcomposition, an empty source is harmless. A small strict diagram with coinciding functor composites needs their common normalization; the new lemma states this rather than assuming independently chosen transformations agree.

B–E audit: the one new node has a standalone statement, no proof or hidden sketch in its statement, all notions cited or explicitly described, exact TeX, explicit source limitations and genuine logged searches. It is neither an elementary equality nor a clause restating the replacement/cube theorem: it concerns normalized Hom transformations for arbitrary composable quasicategory functors, contains no replacement or enriched comparison, and asserts no homotopy pullback. The item itself performs both cube constructions and the two distinct weak-equivalence arguments. I did not create the initially considered enriched-Hom refinement, because the existing enriched/twisted-arrow node already supplies it. No cycles were introduced. None of the six nontrivial arguments exceeds 2000 characters; the only elementary step is the final assembly, and no long argument conceals a further lemma.

## New-node proof plan and Mathlib audit

For the new node, Tw(UT)=Tw(U)Tw(T) is a strict equality on every simplex sigma, and Tw(id) is the identity. Use the full composition/pullback-compatible mapping-space comparison of transport classification on the base K_C to carry this equality and the associated degenerate higher simplices to the normalized Hom transformations. The normalization on mapping-space models must retain the actual simplex maps, not merely their classes. Restriction to a second-variable edge then gives the displayed comparison of naturality paths, with the compositor constant on the strict corner equalities. This is the extra technical lemma left unsplit for the next stage-1 worker; it is not being asserted to follow from the old Hom node's statement in one line. The enriched comparison needed separately by the item is already present in the DAG.

All new-node Mathlib searches were run with msearch.py and logged as returned in searches.jsonl. The first semantic phrasing searched the coherence of Hom transformations for composable functors; the second searched twisted-arrow classification compatible with identity/composition. LeanFinder returned component homotopy-category facts and Quillen-fibration facts. LeanSearch returned ordinary NatTrans/FunctorHom and Grothendieck/pseudofunctor constructions. Loogle's broad quoted SSet/comp query included irrelevant compiler and combinatorial names; a second valid query CategoryTheory.Functor.map_comp returned the ordinary functor law. I read Mathlib/CategoryTheory/Functor/Basic.lean:40–49: this law is for ordinary category morphisms, not coherent Hom transformations. The enriched search returned SSet.QCat.catEnrichedOrdinaryCategory; its source StrictBicategory.lean:19–30 explicitly uses homotopy categories of internal Homs, losing the higher data required here. I also read Mathlib/AlgebraicTopology/SimplicialNerve.lean:13–39 and its nerve definition: it constructs the simplicial nerve and lists local-Kan quasicategory foundations as future work, and does not give this comparison. No result is an exact match or a one-line specialization. No service-down response was relabelled as a negative result. The original logged item searches and inherited earlier search records were retained.

## Not duplicates

lem-cbc-hom-functor-composition-coherence vs lem-cbc-coherent-square-comparison-data: the item compares two specific squares involving rigidification and Kan replacement; the new lemma only supplies the independent compatibility of Hom transformations with functor composition, without any enriched replacement or cube-comparison conclusion.

lem-cbc-hom-functor-composition-coherence vs lem-coef-infinity-hom-bifunctor-functoriality: the existing statement treats one functor and naturality in its two object variables; the new lemma adds normalized comparators for composing functors, including the relative-endpoint comparison of their naturality paths.

lem-cbc-hom-functor-composition-coherence vs lem-coef-infinity-relative-hom-evaluation: the existing statement concerns one parameterized functor with a fixed restriction and compares its Hom action to relative arrow transport; it does not compare transformations for T, U and UT.

lem-cbc-hom-functor-composition-coherence vs lem-coef-pointwise-lan-mapping-property: the existing statement is the general mapping-space universal property for a given pointwise Kan extension; it neither identifies the normalized Hom maps nor states their composition comparators.

lem-cbc-hom-functor-composition-coherence vs lem-coef-inner-anodyne-pointwise-lan-invariance: the existing statement compares pointwise Kan-extension tests after an inner-anodyne restriction; it has no assertion about composing Hom transformations.

lem-cbc-hom-functor-composition-coherence vs lem-coef-relative-join-left-kan-reduction: the existing statement realizes one transformation on a relative join and tests its Kan extension; the new lemma instead compares Hom transformations of composable functors.

lem-cbc-hom-functor-composition-coherence vs lem-coef-right-fibration-constant-right-kan: the existing statement computes right Kan extension of a constant space along one right fibration; it does not concern the compositors of Hom transformations.

lem-cbc-hom-functor-composition-coherence vs lem-coef-right-fibration-fiberwise-kan: the existing statement computes right Kan extensions by fiberwise limits along a right fibration; it does not supply functor-composition coherence for Hom.

lem-cbc-hom-functor-composition-coherence vs lem-weil-pbc-normal-domain-ring-equivalence: 0309 is a Stacks tag in this ring-theoretic node, whereas the new source uses the Kerodon identifier 0309; preservation of normality by a ring isomorphism is unrelated to coherent Hom.

lem-cbc-hom-functor-composition-coherence vs def-weil-pbc-normal-ring: the tag collision is between Stacks and Kerodon 0309; the existing node defines normal rings, while the new node is a statement about quasicategory Hom transformations.

## What could not be finished

No attachment or Mathlib leaf was found. The new node is intentionally statement-only under the one-level split contract. No Lean was written or compiled, no other agents were started, and no project/launcher file was changed. The remote check_dag and review_split checks passed on the repaired sandbox; the required deliver.py dry run and push are the final gates.

## Delivered citation evidence

The following is the full content of citations.json, packaged here because only the node files and this report enter the delivery.

```json
[
 {
  "step": 1,
  "node": "lem-coef-coherent-nerve-comparison",
  "quote": "There is a functorial locally Kan replacement $A\\to RA$ fixing its objects and inducing weak homotopy equivalences on every mapping set. The replacement may be chosen to fix discrete simplicial categories and their maps."
 },
 {
  "step": 1,
  "node": "def-cbc-enhanced-diagrams-cones",
  "quote": "For objects $x,y$ of a quasicategory, use the mapping space with $n$-simplices the maps $\\Delta^{n+1}\\to\\mathscr C$ whose restriction to the entire initial face $\\Delta^{\\{0,\\ldots,n\\}}$ is the constant simplex at $x$, and whose last vertex is $y$. Simplicial operators are induced by extending each weakly increasing map $[m]\\to[n]$ to $[m+1]\\to[n+1]$ by sending the new last vertex to the new last vertex. This is the right-pinched mapping space $\\operatorname{Map}_{\\mathscr C}(x,y)$."
 },
 {
  "step": 1,
  "node": "lem-cbc-hom-functor-composition-coherence",
  "quote": "Use small quasicategories, right-pinched mapping spaces, coherent functors and transformations of [def-cbc-enhanced-diagrams-cones], the space category of [def-coef-infinity-category-of-spaces], and the Hom bifunctors and single-functor transformations of [lem-coef-infinity-hom-bifunctor-functoriality]. Write $K_C=C^{\\mathrm{op}}\\times C$. Normalize a Hom bifunctor $H_C:K_C\\to\\mathcal S$ as the classifier of the twisted-arrow left fibration $\\lambda_C:\\operatorname{Tw}(C)\\to K_C$ of [lem-coef-twisted-arrow-left-fibration], using the composition- and base-pullback-compatible transport comparison of [lem-coef-space-transport-classification]. Then the Hom functors and their transformations can be chosen simultaneously on any small strict ordinary diagram of small quasicategories so that the following holds.\n\nFor every functor $T:C\\to D$, the transformation $t_T:H_C\\to H_D(T^{\\mathrm{op}}\\times T)$ is represented under classification by the map $\\operatorname{Tw}(C)\\to K_C\\times_{K_D}\\operatorname{Tw}(D)$ sending a simplex $\\sigma$ to $T\\sigma$. Its components, in the right-pinched mapping-space models, are the actual maps $T_{x,y}$ obtained by applying $T$ to simplices. The identity transformation is normalized to the identity."
 },
 {
  "step": 1,
  "node": "lem-coef-infinity-hom-bifunctor-functoriality",
  "quote": "There are coherent Hom bifunctors\n$$H_{\\mathcal E}:\\mathcal E^{\\mathrm{op}}\\times\\mathcal E\\longrightarrow\\mathcal S_{\\mathcal U}\\qquad(\\mathcal E=\\mathcal C,\\mathcal D),$$\nwhose values identify with $\\operatorname{Map}_{\\mathcal E}(a,b)$ as spaces. Their action in the first variable is precomposition and their action in the second is postcomposition, with the canonical unit and composition homotopies. For any coherent functor $T:\\mathcal C\\to\\mathcal D$, the induced maps of right-pinched mapping spaces assemble, under these identifications, to a coherent natural transformation\n$$T_*:H_{\\mathcal C}\\longrightarrow H_{\\mathcal D}\\circ(T^{\\mathrm{op}}\\times T).$$\nAt $(a,b)$ its homotopy class is the simplicial map obtained by applying $T$ to every simplex $\\Delta^{n+1}\\to\\mathcal C$ in the right-pinched mapping space. Naturality is in the infinity category $\\operatorname{Fun}(\\mathcal C^{\\mathrm{op}}\\times\\mathcal C,\\mathcal S_{\\mathcal U})$, retaining higher simplices; it is not merely naturality on component sets. These induced maps preserve the canonical composition and identity classes."
 },
 {
  "step": 2,
  "node": "lem-cbc-hom-functor-composition-coherence",
  "quote": "For composable functors $T:C\\to D$ and $U:D\\to F$, there is a specified coherent comparison from $t_{UT}$ to the composite of $t_T$ with the restriction of $t_U$. Its components are constant homotopies on the strict equalities $(UT)_{x,y}=U_{Tx,Ty}T_{x,y}$. For an edge $h:y\\to z$ and vertex $x$ of $C$, write $c_C(h)$ for the chosen postcomposition representative and write $h_T$ for the naturality homotopy\n$$T_{x,z}c_C(h)\\simeq c_D(Th)T_{x,y}.$$\nThe comparison supplies a homotopy relative endpoints between $h_{UT}$ and the pasted path\n$$U_{Tx,Tz}T_{x,z}c_C(h)\\xrightarrow{\\ U h_T\\ }U_{Tx,Tz}c_D(Th)T_{x,y}\\xrightarrow{\\ h_U T\\ }c_F(UTh)U_{Tx,Ty}T_{x,y}.$$\nIf two composites in the strict diagram are equal as simplicial maps, their $t_{UT}$ and $h_{UT}$ are the same chosen data."
 },
 {
  "step": 3,
  "node": "lem-coef-rigidification-postcomposition-comparison",
  "quote": "Let $S$ be a small quasicategory, put $D=\\mathfrak C[S]$, and write $r:D\\to RD$ for an object-preserving locally Kan replacement. Let $W=N_{\\mathrm{hc}}(RD)$ and $a:S\\to W$ be adjoint to $r$. Then $a$ is a categorical equivalence, and for every pair of vertices its map $\\operatorname{Map}_S(x,y)\\to\\operatorname{Map}_W(ax,ay)$ is a weak homotopy equivalence."
 },
 {
  "step": 4,
  "node": "lem-coef-coherent-nerve-comparison",
  "quote": "Use simplicial sets [def-weil-pbc-simplicial-set], quasicategories, Kan complexes, weak homotopy equivalences and mapping spaces [def-cbc-enhanced-diagrams-cones], in sufficiently large fixed universes. A small simplicial category $A$ has a set of objects, simplicial mapping sets $A(x,y)$, identity vertices and associative unital simplicial composition maps. Its category $\\pi_0A$ has the same objects and the components of its mapping sets as morphisms. A Dwyer--Kan equivalence is a simplicial functor inducing weak homotopy equivalences on all mapping sets and an equivalence on $\\pi_0$."
 },
 {
  "step": 4,
  "node": "lem-coef-enriched-hom-twisted-arrow-comparison",
  "quote": "There is an equivalence over $C^{\\mathrm{op}}\\times C$ between $\\operatorname{Tw}(C)$ and $(C^{\\mathrm{op}}\\times C)\\times_{H,\\mathcal S,r}W$. On a vertex represented by an edge $a\\to b$, comparison with the fiber $\\mathcal A(a,b)$ is the coherent-nerve mapping comparison. It carries the identity edge to the enriched identity point with its unit homotopy. The equivalence is natural for simplicial functors and respects the simplicial precomposition and postcomposition maps, including their higher composition and unit homotopies."
 },
 {
  "step": 4,
  "node": "lem-coef-space-transport-classification",
  "quote": "For two such representatives there is an equivalence of spaces\n$$\\operatorname{Map}_{\\operatorname{Fun}(A,\\mathcal S_{\\mathcal U})}(F,G)\\simeq\\operatorname{Fun}_{/A}(E_F,E_G),$$\nwhere the right side has $n$-simplices the maps $E_F\\times\\Delta^n\\to E_G$ whose composite with $q_G$ is $q_F$ on the first factor. This simplicial set is Kan. The comparison is coherent in both functors and compatible with composition and pullback along maps of base simplicial sets."
 },
 {
  "step": 4,
  "node": "lem-cbc-hom-functor-composition-coherence",
  "quote": "Use small quasicategories, right-pinched mapping spaces, coherent functors and transformations of [def-cbc-enhanced-diagrams-cones], the space category of [def-coef-infinity-category-of-spaces], and the Hom bifunctors and single-functor transformations of [lem-coef-infinity-hom-bifunctor-functoriality]. Write $K_C=C^{\\mathrm{op}}\\times C$. Normalize a Hom bifunctor $H_C:K_C\\to\\mathcal S$ as the classifier of the twisted-arrow left fibration $\\lambda_C:\\operatorname{Tw}(C)\\to K_C$ of [lem-coef-twisted-arrow-left-fibration], using the composition- and base-pullback-compatible transport comparison of [lem-coef-space-transport-classification]. Then the Hom functors and their transformations can be chosen simultaneously on any small strict ordinary diagram of small quasicategories so that the following holds.\n\nFor every functor $T:C\\to D$, the transformation $t_T:H_C\\to H_D(T^{\\mathrm{op}}\\times T)$ is represented under classification by the map $\\operatorname{Tw}(C)\\to K_C\\times_{K_D}\\operatorname{Tw}(D)$ sending a simplex $\\sigma$ to $T\\sigma$. Its components, in the right-pinched mapping-space models, are the actual maps $T_{x,y}$ obtained by applying $T$ to simplices. The identity transformation is normalized to the identity."
 },
 {
  "step": 5,
  "node": "lem-coef-enriched-hom-twisted-arrow-comparison",
  "quote": "There is an equivalence over $C^{\\mathrm{op}}\\times C$ between $\\operatorname{Tw}(C)$ and $(C^{\\mathrm{op}}\\times C)\\times_{H,\\mathcal S,r}W$. On a vertex represented by an edge $a\\to b$, comparison with the fiber $\\mathcal A(a,b)$ is the coherent-nerve mapping comparison. It carries the identity edge to the enriched identity point with its unit homotopy. The equivalence is natural for simplicial functors and respects the simplicial precomposition and postcomposition maps, including their higher composition and unit homotopies."
 },
 {
  "step": 5,
  "node": "lem-coef-coherent-nerve-comparison",
  "quote": "For every locally Kan $A$, the coherent nerve is a quasicategory, and there are natural equivalences of spaces\n$$A(x,y)\\simeq\\operatorname{Map}_{N_{\\mathrm{hc}}A}(x,y).$$\nThese are induced by the coherent-nerve adjunction, send a vertex of $A(x,y)$ to its corresponding edge, and preserve enriched composition with its coherent homotopies."
 },
 {
  "step": 5,
  "node": "def-coef-infinity-category-of-spaces",
  "quote": "Let $\\mathbf{Kan}_{\\mathcal W}$ be the simplicial category of $\\mathcal W$-small Kan complexes, with morphism simplicial set $\\operatorname{Fun}(S,T)_n=\\operatorname{Hom}_{\\mathrm{sSet}}(S\\times\\Delta^n,T)$ and composition induced by evaluation and composition of simplicial maps. Define $\\mathcal S_{\\mathcal W}=N_{\\mathrm{hc}}(\\mathbf{Kan}_{\\mathcal W})$, the infinity category of $\\mathcal W$-small spaces. This is the coherent nerve, retaining homotopies between maps, rather than the ordinary nerve of the underlying category."
 },
 {
  "step": 5,
  "node": "lem-cbc-kan-functor-space-kan",
  "quote": "Let $Z$ be a Kan complex and let $K$ be any simplicial set in the same universe. With the internal functor simplicial set $\\operatorname{Fun}(K,Z)$ defined in [def-cbc-enhanced-diagrams-cones], $\\operatorname{Fun}(K,Z)$ is a Kan complex."
 }
]
```
