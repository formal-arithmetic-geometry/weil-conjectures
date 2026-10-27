# Repair of lem-sfb-field-profinite-galois-site

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-field-profinite-galois-site.json: existing statement, split; statement and stmt_deps retained verbatim.
- dag/nodes/sec-six-functors-basics/lem-sfb-field-geometric-fibre-construction.json: statement, unsplit; no Mathlib match, no proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-ind-etale-galois-fibre-reconstruction.json: statement, unsplit; no Mathlib match, no proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-field-geometric-fibre-covering-test.json: statement, unsplit; no Mathlib match, no proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-field-profinite-tensor-fibres.json: statement, unsplit; no Mathlib match, no proof steps.

## Attachments

None. The exact project theorem AlgebraicGeometry.ProEtale.FieldGaloisSite.field_profinite_galois_site in lean/Sheaf/Paper/FieldProfiniteGaloisSite.lean still ends in sorry. A search by blueprint tag and by profinite/Galois concepts in lean/WeilConjectures found no complete declaration of the item. The finite Galois classification and condensed_point_basis cover useful proper parts only.

## WANTED

None: the Bhatt–Scholze PDF and supporting Stacks sources are present.

## Returned issue and repair

The returned proof was 8945 characters in eight steps. The sandbox initially held only dispatcher markers: there was no report, search log or node copy to continue. I copied the currently returned node, including its maintainer metadata and old searches, to the sandbox; returned-proof.json saves that exact starting version. No repository or launcher file was written and no compiler was run. Four new work items now carry substantial independent arguments. The original statement is unchanged. This is a re-split, not a new proof route.

The new responsibilities are:

- lem-sfb-field-geometric-fibre-construction: returned steps 1, 2, 3; Affine reduction and construction of profinite geometric fibres over a field. Assigned old argument: 2960 characters.
- lem-sfb-ind-etale-galois-fibre-reconstruction: returned steps 4, 5; Algebra reconstruction from continuous profinite Galois fibres. Assigned old argument: 2116 characters.
- lem-sfb-field-geometric-fibre-covering-test: returned steps 6, 7; Split geometric fibres and the finite fpqc covering test. Assigned old argument: 2283 characters (the density paragraph of old step 7 stays in parent step 3).
- lem-sfb-field-profinite-tensor-fibres: returned steps 8; Geometric fibres of profinite tensor schemes over intermediate fields. Assigned old argument: 1586 characters.

Original parent assembly: 2043 characters; the clarified return-L assembly is 2296 characters, four steps, each below 2000. None of the new nodes includes the whole site equivalence and its normalizations. In particular the reconstruction node has algebraic Hom and realization assertions, the covering node proves a split-spectrum homeomorphism and an affine fpqc test, and the tensor node treats all intermediate fields. The latter generality exposes the restriction map needed for the canonical projection. Each is statement-only, so future workers can split and prove them independently.

## Review by Q82

I read Bhatt–Scholze, Definition 4.1.1, Example 4.1.4, Lemmas 4.1.6–4.1.8 and Examples 4.1.9–4.1.10 on PDF pages 27–28. For the affine reduction I also read Stacks 0CKV, properties.tex, lemma-dimension-zero: quasi-separatedness and quasi-compactness are both required. For the finite classification I read 03QR, pione.tex, lemma-sheaves-point, and 03QS, remark-covering-surjective. These give the finite embedding labels with left postcomposition, which fixes the orientation throughout. I opened the statements of all 29 dependencies of the old proof; they are retained with the old proof below so that the new workers receive the original reasoning and its precise inputs.

For parent step 1, field-geometric-fibre-construction supplies affineness, the coordinate-algebra presentation, the actual continuous action and precomposition functor. ind-etale-galois-fibre-reconstruction supplies exactly the displayed Hom bijection and realization of every continuous profinite action. def-weil-affine-spectrum explicitly states the bijection between ring maps and maps of spectra, so it supports the conversion to a covariant scheme functor, rather than merely defining primes. All algebras involved are ind-etale and all partition systems are small under the inherited universe convention. The finite-quotient choices made during realization are legitimate because the finite classification covers disconnected objects through finite products, as explained in retained step 2.

For parent step 2, the first two new nodes are applicable to the separably closed field as its own separable closure. Its relative automorphism group is trivial. The third new node explicitly gives both ind-etaleness of the tensor algebra and the natural homeomorphism on embedding spaces. The existing fibre-product-affine-spectra statement identifies base change with that tensor algebra and specifies both ring maps. Thus this step uses the statements, not any construction hidden in their proofs.

For parent step 3, the third new statement is an iff for arbitrary small families with a finite jointly surjective subfamily, including the empty family over the empty target. It therefore gives exactly the covering criterion required here. def-weil-pbc-proetale-site explicitly defines its coverings to be the fpqc families. The first new statement applies to affine opens of a weakly etale field scheme (restriction remains weakly etale) and makes them qcqs. The remaining density argument is written in the parent: refine intersections by affine opens and select finitely many over each quasi-compact affine target open. It uses no quasi-separatedness assertion about the arbitrary larger object.

For parent step 4, the fourth new statement is the evaluation homeomorphism for LC(P,L), the identification with the actual test scheme, the restriction formula in L and the parameter formula in P. These formulas, not an arbitrary chosen equivalence, pin the structural map to the projection. The node also states that self-embeddings of the separable closure are automorphisms with Krull topology; that is essential when L=Omega. The hypotheses are separable algebraic intermediate fields, never algebraic closures or perfect fields.

For the first new node I checked the zero algebra, a field, finite products, and infinite directed unions. It retains the all-primes-maximal argument and 0CKV affine reduction, the finite transitive classification and products, and the inverse-limit action and surjective projection arguments from old steps 1–3. Surjective projections are asserted only for a nonzero algebra. For the second node I checked B=0, C=0, P empty, finite transitive actions and an infinite profinite action. The full finite-stage factorization, equivariance descent, common-stage uniqueness, finite-presentation factorization and quotient-algebra realization remain in its assigned argument below; none was replaced by an appeal to the parent equivalence. The empty partition is included.

For the third node I checked split finite products, the zero tensor algebra, empty covering families and both directions of the covering test. Its assigned argument retains residue fields over a separably closed base, topology from finite spectra, surjectivity under base change, flatness of arrows, and the finite affine-open fpqc test. For the fourth node I checked L=k, L=Omega, P empty, P a singleton and finite disjoint unions; for an arbitrary intermediate L the same finite-stage argument runs over its finite subfields together with finite partitions of P. Every locally constant function has finite image, so its values lie in a finite separable subextension. This is why the extension from the returned endpoints to all intermediate fields is valid; it changes no parent hypothesis.

The first dry run passed at 0fd0c6ffd0b. In my final citation check I made the affine-open clause explicit in the first new statement: an affine open of an arbitrary weakly etale field scheme is qcqs and remains weakly etale. This clause prevents a circular use of the qcqs hypothesis in the density step. Its argument was already present in returned steps 1 and 7. I then regenerated the affected verbatim quotes and ran the final dry run.

I checked delivery-errors B–E: statements introduce their own objects and inline the topology and action; definition dependencies refer to the notions actually used; new nodes are unsplit with no proof sketch; TeX has ordinary single escapes; search records are copied from the real search log, with unavailable LeanSearch marked unavailable. Every parent citation has a verbatim statement quote in citations.json. No missing non-elementary input remains in the parent assembly. No new node cites the parent, and none of the retained tool dependencies was used to change the unit route. The inherited unit and chapter are unchanged. No SGA source was used.

On the resumed return-L review I compared the retained returned-proof.json with the shared current item: every field agrees. The proposed delivery changes only proof, proof_deps and split_report; the released re-split order still applies, and all four helper ids remain absent from the current DAG. I reread every assembly citation and each helper statement dependency against the current files, including the finite-family clause of def-weil-pbc-proetale-qcqs-subsite. All twelve step/node pairs in citations.json are complete and verbatim. The k-linear spectrum correspondence in step 1 and the finite-family topology comparison in step 3 are the retained substantive corrections for this return. The current assembly is 2296 characters after those corrections, with no step over 2000. I reread Bhatt–Scholze pp. 27–29 and the full zero-dimensional affineness statement at Stacks 0CKV, and reviewed the retained actual search results rather than repeating the same questions. The initial dry run of this resumed session exited successfully at 68b4ac1f4c1; the final dry run below validates this report and the corrected character count.

## Not duplicates

- lem-sfb-field-geometric-fibre-construction vs lem-weil-pbc-weak-etale-field: the existing node only classifies weakly etale algebras; the new node also reduces arbitrary qcqs schemes to affines and constructs the profinite geometric-point functor and its surjective finite projections.
- lem-sfb-field-geometric-fibre-construction vs lem-sfb-qcqs-zero-dimensional-affine: the existing result is a generic affineness criterion, not the field-algebra and geometric-fibre construction.
- lem-sfb-field-geometric-fibre-construction vs lem-exc-etale-field-gsets: the existing classification concerns discrete actions and etale schemes, not infinite ind-etale algebras with profinite rather than discrete geometric fibres.
- lem-sfb-ind-etale-galois-fibre-reconstruction vs lem-exc-etale-field-gsets: the existing node concerns discrete etale objects; the new Hom factorization and realization treat profinite continuous actions and filtered colimits of algebras.
- lem-sfb-ind-etale-galois-fibre-reconstruction vs det-pe-condensed-point-basis: the existing node assumes a separably closed field and has no nontrivial Galois action; the new result treats arbitrary fields with equivariant reconstruction.
- lem-sfb-ind-etale-galois-fibre-reconstruction vs lem-sfb-profinite-action-finite-quotients: the existing node supplies invariant partitions and their inverse limit, not realization by field algebras or the algebraic Hom bijection.
- lem-sfb-field-geometric-fibre-covering-test vs lem-weil-pbc-geometric-field-profinite-dense-subsite: the existing node assumes an algebraically closed base and states density of a specified test functor; the new result gives the tensor base-change homeomorphism for an arbitrary field and an affine fpqc covering test.
- lem-sfb-field-geometric-fibre-covering-test vs det-pe-condensed-point-basis: the existing node gives a separably closed algebra and scheme classification, not natural comparison under k to Omega or fpqc detection for arbitrary fields.
- lem-sfb-field-profinite-tensor-fibres vs lem-weil-pbc-profinite-test-object-functor: the existing node constructs test objects for any base, but does not classify their geometric embeddings, compute their Galois action, or identify the embedding-space product for intermediate fields.
- lem-sfb-field-profinite-tensor-fibres vs det-pe-condensed-point-basis: the existing result treats Omega-algebra maps; the new statement treats k-algebra maps from LC(P,L), their full embedding-space factor and Galois action.

The whole DAG was searched for the source places, profinite geometric fibres, ind-etale Galois reconstruction, and locally constant Hom calculations. Whole-blueprint searches included profinite Galois, geometric fibre, ind-etale, finite continuous, tensor objects, locally constant, weakly etale and finite jointly surjective. No existing blueprint node states any complete new argument. The ancestor command returns None for this created branch; the inherited null ancestor is preserved, with the parent and the existing via chain recorded.

## Mathlib searches

search-plan.json and search-results/ retain the actual search output; searches.jsonl is the command's original log. Each new node records LeanFinder, Loogle, source grep and LeanSearch, plus a second natural-language phrasing. The final LeanSearch call was rate-limited and is marked unavailable; LeanFinder and Loogle succeeded, and two further LeanFinder formulations checked the tensor calculation. I read the candidate sources: RingTheory/Etale/Weakly.lean, RingTheory/Etale/Field.lean (especially Algebra.Etale.iff_exists_algEquiv_prod), AlgebraicGeometry/Sites/Proetale.lean, and Topology/LocallyConstant/Algebra.lean (comap as an algebra map). These supply parts only, not any new statement. Krull inverse-limit hits construct the Galois group itself, not embeddings of general ind-etale algebras.

## Retained complete argument and handoff to future workers

The following is the returned eight-step proof verbatim, with its sources and dependency lists. It is preserved here as proof material for the four statement-only work items; it is not inserted into their statements or proof arrays. The assignment above accounts for every paragraph; the sole part retained in the parent is affine-open density. The old step 2 finite classification serves both the construction and reconstruction arguments.

### Returned step 1

First reduce the qcqs objects to affines. For every affine open $V=\operatorname{Spec}B$ of a weakly etale $k$-scheme $U$, the field-algebra theorem says that $B$ is reduced with separable algebraic residue fields and is a union of finite etale $k$-subalgebras. Every prime of $B$ is maximal: its quotient is an algebraic domain over $k$, and the minimal polynomial of each nonzero element expresses its inverse as a polynomial in that element. If $x$ specializes to $y$ in $U$, an affine neighbourhood of $y$ contains $x$; hence $x=y$ by maximality of primes there. Thus all points of $U$ are closed. When $U$ is qcqs, apply the zero-dimensional affineness input. Conversely an affine weakly etale object is qcqs. We may therefore write every object of $\mathcal B_s$ as $\operatorname{Spec}B$, with $B$ the directed union of its finite etale $k$-subalgebras.

Uses: lem-weil-pbc-weak-etale-field, lem-sfb-qcqs-zero-dimensional-affine, lem-weil-pbc-affine-scheme-qcqs, sk-lem-pe-weakly-etale-stability.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Example 4.1.4 and Example 4.1.10; affineness detail: Stacks Tag 0CKV.

### Returned step 2

For a finite etale $k$-algebra $A$, put $F(A)=\operatorname{Hom}_{k\text{-alg}}(A,k^s)$ and let $g$ act by $f\mapsto g\circ f$. The finite product decomposition of $A$ identifies this with the finite disjoint union of embedding sets of finite separable extensions. The finite transitive classification on each factor, and componentwise maps between finite coproducts, give full faithfulness and essential surjectivity onto finite continuous $G$-sets. A map from a connected field spectrum to a finite disjoint union lands in exactly one component; this proves the componentwise assertion. This is a contravariant equivalence for algebras, hence a covariant one for finite etale schemes. Base change to $k^s$ splits each factor with one copy of $k^s$ per embedding: apply the same finite classification over the separably closed field, whose Galois group is trivial. The resulting fibre labels are the embeddings, by the point/residue-map description.

Uses: lem-exc-etale-field-galois-classification, lem-weil-pbc-etale-algebra-over-field-product, lem-weil-pbc-finite-affine-coproduct-spectrum, lem-weil-pbc-morphism-from-spec-field.

Source: literature/stacks-project/pione.tex, Tags 03QR (lemma-sheaves-point), 03QS; finite product decomposition Tag 00U3.

### Returned step 3

The separable closure is Galois over $k$, and the Krull finite-limit theorem identifies $G$ with an inverse limit of finite groups; the finite-group limit input makes $G$ profinite. For $B=\bigcup_i B_i$ as in step 1 define $F(B)=\varprojlim_i\operatorname{Hom}_{k\text{-alg}}(B_i,k^s)$ with inverse-limit topology and coordinatewise action. The generic finite-action limit input makes this compact Hausdorff totally disconnected with continuous action. Compatible maps on the stages are exactly maps $B\to k^s$. If $B=0$, its fibre is empty. Otherwise all the finite fibres are nonempty. Inclusions of finite etale algebras induce surjections on finite fibres: by finite full faithfulness an inclusion is a categorical monomorphism, and its corresponding map of finite sets must be surjective (a proper invariant image would give a nonzero component ideal in the kernel). Therefore the finite-set inverse-limit surjectivity theorem makes every projection $F(B)\to F(B_i)$ surjective. An algebra map $C\to B$ acts by precomposition; this proves functoriality. The topology is canonical, since the finite subalgebras are the canonical directed system.

Uses: lem-weil-pbc-weak-etale-field, lem-exc-etale-field-galois-classification, lem-sfb-profinite-action-finite-quotients, lem-galois-inverse-limit-surjective, lem-weil-pbc-separable-closure-exists-galois, lem-exc-galois-krull-finite-limit, lem-dl-a1-finite-group-limit-profinite.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Example 4.1.10: geometric fibre as a pro-object in finite discrete G-sets; compactness argument expanded.

### Returned step 4

Here is full faithfulness, including the finite-stage argument. A continuous equivariant map $F(B)\to F(C)$ is the same as compatible maps to $F(C_j)$ for the finite etale subalgebras $C_j\subset C$. Each such map factors continuously through some $F(B_i)$ by profinite function factorization. Its factor is equivariant because $F(B)\to F(B_i)$ is surjective and equivariant: evaluate at a lift of any point of $F(B_i)$ and at its translate. Step 2 gives a map $C_j\to B_i\subset B$. Two finite-stage factors give the same map into $B$: pass to a common larger subalgebra, and use surjectivity of its projection from $F(B)$ and finite full faithfulness. Conversely, any $C_j\to B$ factors through a finite subalgebra $B_i$, by finite-presentation factorization. Thus the compatible maps just constructed glue uniquely to $C\to B$. This proves the required bijection on morphisms, with the specified precomposition formula. If $B=0$, there is a unique algebra map $C\to0$ and a unique map $\varnothing\to F(C)$. If $C=0$ and $B\ne0$, both Hom sets are empty because $F(B)$ is nonempty. These cases handle every empty-stage exception.

Uses: lem-weil-pbc-profinite-limit-function-factorization, lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Example 4.1.10, pro-object identification; finite-presentation step: Stacks Tag 00QO.

### Returned step 5

For essential surjectivity take a profinite continuous $G$-set $P$. Its invariant finite clopen partitions give $P=\varprojlim_i P_i$ by the equivariant quotient input. Choose the finite etale schemes $\operatorname{Spec}A_i$ corresponding to $P_i$ using step 2; full faithfulness gives all transition maps and their coherence. Set $A=\varinjlim_i A_i$. The spectrum-colimit theorem identifies $\operatorname{Spec}A$ with their inverse limit. This is weakly etale because ind-etale maps are weakly etale and are stable under filtered colimits. Its geometric fibre is $\varprojlim_i P_i=P$, since maps from a colimit of algebras to $k^s$ are compatible maps on the stages. The coordinate topology is the same: every finite subalgebra of $A$ has finitely many generators, so is contained in the image of a stage, while each image is a finite etale subalgebra by step 1 (a finite-dimensional image is generated by finitely many elements). This proves $\mathcal B_s\simeq\mathbf{Prof}_G$.

Uses: lem-sfb-profinite-action-finite-quotients, lem-weil-pbc-spec-small-colimit-limit, lem-weil-pbc-ind-etale-stability.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Example 4.1.10: pro-objects and continuous profinite G-sets.

### Returned step 6

Base change to $k^s$ forgets the action. On affine rings it sends $B$ to $k^s\otimes_k B$; a $k^s$-algebra map from this tensor product to $k^s$ is uniquely $a\otimes b\mapsto a f(b)$ for a $k$-algebra map $f:B\to k^s$. These bijections are natural. They are homeomorphisms, since on every finite etale subalgebra they are the finite splitting of step 2, and tensoring commutes with the directed colimit by the cited tensor theorem (the ring compatibility follows on pure tensors). Over the separably closed field the construction of steps 1–5 has trivial Galois group, yielding $\mathcal B_{\bar s}\simeq\mathbf{Prof}$. Every point of an affine weakly etale $k^s$-scheme has residue field $k^s$, so the point/residue-map bijection identifies its entire underlying spectrum with its set of $k^s$-points; the topology agrees because the spectrum topological-limit theorem identifies it with the limit of the split finite-stage spectra.

Uses: lem-weil-pbc-fibre-product-affine-spectra, lem-weil-pbc-weak-etale-field, lem-weil-pbc-morphism-from-spec-field, lem-weil-pbc-tensor-commutes-with-colimits, lem-a1-filtered-spectrum-topological-limit.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Example 4.1.10, separably closed case and geometric base change.

### Returned step 7

For an arrow in $\mathcal B_s$ both schemes are affine; it is weakly etale and hence flat. A family with a finite jointly surjective subfamily of geometric fibres is jointly surjective on schemes: the projection $U_{k^s}\to U$ is surjective by surjective base change, and step 6 identifies every point above with a $k^s$-point. Choosing such a lift and lifting its fibre coordinate proves the assertion. For every affine open of the target its inverse images under the finitely many selected arrows are affine, since a morphism between affines is affine. These inverse images therefore give exactly the finite affine opens required in the fpqc covering definition. Conversely a pro-etale covering of an affine target has finitely many affine source opens mapping onto it, so the finitely many source objects containing them are jointly surjective. Their geometric base changes remain jointly surjective by stability of surjectivity under base change, and step 6 identifies their points with the profinite fibres. This proves the covering criterion. Finally arbitrary weakly etale objects have covers by their affine open subschemes, which are qcqs and remain weakly etale; any affine open of the target has a finite refinement by affine opens in this open cover. Thus $\mathcal B_s$ is cover dense, and its topology is the induced one just computed.

Uses: sk-lem-pe-weakly-etale-stability, def-weil-weakly-etale-morphism, lem-weil-pbc-morphism-affine-schemes-affine, lem-weil-pbc-surjective-base-change, def-weil-pbc-fpqc-covering, def-weil-pbc-proetale-site, lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-weak-etale-field.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Definition 4.1.1, Examples 4.1.7 and 4.1.10; affine open coverings for density.

### Returned step 8

For finite $P_i$, the fibre of $\coprod_{P_i}s$ is $P_i$ with trivial $G$-action. Each finite stage $\coprod_{P_i}s$ is $\operatorname{Spec}k^{P_i}$ by the finite coproduct-spectrum theorem, so by the spectrum-colimit theorem the limit $s[P]$ of the test-object construction is $\operatorname{Spec}\varinjlim_ik^{P_i}$, an affine object of $\mathcal B_s$; as in step 5, its fibre is the limit of the stage fibres with the same topology. Passing to the finite-quotient inverse limit therefore gives $F(s[P])=P$ with trivial action; the same applies to $\bar s[P]=\operatorname{Spec}\varinjlim_i(k^s)^{P_i}$. On the other hand $\operatorname{Hom}_{k\text{-alg}}(k^s,k^s)=G$: every such embedding is an automorphism. Indeed every element lies in a finite Galois intermediate field; a $k$-embedding preserves that field and permutes its finitely many roots, hence is surjective on it. The union is therefore surjective. The separable algebraic extension $k^s/k$ is ind-etale by its finite separable presentation, so $\bar s[P]$ is itself an object over $s$. Its topology is the Krull topology since restrictions to finite subextensions are the finite coordinates. Hence the fibre of $\coprod_{P_i}\bar s$ is $G\times P_i$, with $g(h,p)=(gh,p)$. Passing to the limit gives $F(\bar s[P])=G\times P$. Precomposition by the structural map $k\to k^s$ forgets the embedding coordinate, so the morphism $\bar s[P]\to s[P]$ is $(h,p)\mapsto p$. A continuous map of profinite parameters acts by $(h,p)\mapsto(h,f(p))$ and by $p\mapsto f(p)$; these formulas prove all the asserted naturality squares.

Uses: lem-weil-pbc-profinite-test-object-functor, def-pd-separable-closure, lem-weil-pbc-separable-closure-exists-galois, lem-exc-galois-krull-finite-limit, lem-weil-pbc-finite-set-in-finite-galois-subextension, lem-kun-algebraic-separable-smooth, lem-weil-pbc-finite-affine-coproduct-spectrum, lem-weil-pbc-spec-small-colimit-limit.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Example 4.1.9 and Example 4.1.10: tensor objects and Galois action normalization.

## Unfinished work

The four new nodes intentionally remain statement-only work items. Their arguments are fully preserved above for independent workers. This repair makes no claim of a Lean proof. The resumed repair and current validation are recorded below.


## Return L: rebase onto the live DAG (resumed 2026-10-22)

The landing return concerns side completion that was never promoted into the live DAG. I retained all four new statements, the complete returned argument, the original searches and their raw results, and every citation. No delivery process was still running when this turn resumed. The required initial dry run completed with `OK (not pushed)` at e396fa5b460 on the delivery tool's freshly fetched origin/sheaf-dag. The tool constructs its delivery on current origin rather than using the old delivery head 2303db565a1 from the retained receipt.

I compared returned-proof.json with the current live item field by field: they are identical. The live item still has the eight-step, 8945-character proof and its released stage-1 repair order; none of the four proposed new nodes is present in the shared live DAG. The sandbox is therefore still the substantive re-split of the live proof, not an unchanged copy of a completed live split. I reread every current statement used by the four assembly steps and the definition dependencies of all four new statements. Each existing quoted assembly statement still contains its verbatim citation. No source or hypothesis correction is required by the current live statements.

I made two assembly clarifications during this rebase review: step 1 explicitly restricts the spectrum Hom correspondence to k-linear maps by commutation with the structure morphisms; step 3 explicitly identifies the finite covering precoverage with the induced topology, using the existing qcqs-subsite definition. That definition says finite families, whereas the covering-test node admits arbitrary small families having finite covering subfamilies; this is exactly the comparison needed, with no new compactness hypothesis. Its full verbatim statement has been added to citations.json. These changes and this report update make the resumed repair reviewable beyond a bare re-push.

The review of steps 1–4 above remains applicable. I reopened Bhatt–Scholze pp. 27–29, Definition 4.1.1, Lemmas 4.1.6–4.1.8 and Examples 4.1.9–4.1.10: the functor is the geometric-point functor, covers have finite jointly surjective subfamilies, and scalar base change forgets the action. I checked again that all new statements include the zero algebra and empty parameter, that the action is left postcomposition, and that the tensor restriction is (h,p) mapped to (h restricted to L,p). The existing project theorem still ends in sorry, so it is not an attachment. The real search results give only proper components of these new statements; the existing log is reused without inventing or repeating searches.

All four new nodes remain unsplit with empty proof and proof_deps. The item statement and stmt_deps remain verbatim, and its assembly remains below 3000 characters. The delivery script will preserve current maintainer-owned metadata while overlaying the reviewed split fields. A final dry run is required after these edits, followed by the explicitly authorized direct push; neither approval nor merging is claimed here.
