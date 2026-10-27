# Worker report: lem-a1-fpqc-invariant-intersection-neighbourhoods

## Files written

- Item: dag/nodes/sec-purity-real-sheaves/lem-a1-fpqc-invariant-intersection-neighbourhoods.json; statement unchanged; split with 2953 characters in six assembly steps.
- New statement-only node: lem-a1-flat-relation-qc-image-intersections — unsplit; no Mathlib match; all four search kinds recorded.
- New statement-only node: lem-a1-flat-relation-invariant-open-complement — unsplit; no Mathlib match; all four search kinds recorded.
- citations.json: verbatim statement quotations for every citation in the six assembly steps.
- searches.jsonl: actual official msearch output log; repair.py: sandbox-only JSON/report preparation.

## Attachments

None. Searched the live WeilConjectures source by the item blueprint tag, invariant neighbourhood terminology, source-target/saturation terminology and the relation, image and complement arguments. The corresponding Sheaf module is present, but its main theorem ends in sorry (lines 104–117); its construction-only helper is not the item's conclusion. The existing orbit-saturation theorem is an ingredient, not the item. No compiler was run.

## WANTED

None. All mathematical sources used are in literature/stacks-project/.

## Returned work and repair

The sandbox initially contained only .brief2 through .brief5; no earlier node, report or searches.jsonl was present. I continued from the current shared repository's node, whose eight proof texts and lengths match the return, rather than discarding that reviewed argument. The source SHA256 was 246126cf1acfe27dc865a0730c1beca226a8acaf9ebaa435a6d36b3dc5b0fb50. No git command was run in the shared repository, and every write is in this sandbox. Delivery tooling rebases its overlay onto current origin while retaining maintainer metadata.

The single return asks for genuine parallel work, at least two comparable new statement-only lemmas, and an assembly of at most 3000 characters, while retaining the statement and every old argument. Two lemmas now distribute the substantial arguments: the image/intersection lemma carries old steps 3,6,7 (2787 characters, including the same image argument used twice); the complement lemma carries old steps 4–5 (1741 characters). Old steps 1–2 remain verbatim in the parent as applications of existing geometric inputs and the elementary union argument, and old step 8 remains as the final translation. The parent proof is 2953 characters. Neither new lemma states the whole conclusion: one concerns arbitrary flat quasi-compact maps with no invariance, and one constructs a bounded invariant open for prescribed K,H without any intersection assertion. Each has its own self-contained hypotheses, empty proof and proof_deps, status unsplit, precise Stacks source, blueprint provenance, and authentic search record. The detailed old arguments below remain available for the workers who take these nodes.

The first dry run passed a three-node candidate. My final self-review folded its proposed relation/saturation node back into the parent: affineness and flatness follow immediately from the existing base-change interfaces, the section follows from the existing diagonal-identity lemma, and arbitrary saturation from the existing singleton lemma by unions. These applications do not warrant a new node under the elementary-fact rule. The final delivery has two new substantial nodes, and receives a fresh dry run after this correction.
## Searches and duplication checks

I searched the entire DAG by tags 0APA, 0APB, 03LO, 0APF, saturation, invariant open, generalization and closed complement, and read the relevant existing statements. I also ran blueprint_refs.py ancestor on the item and blueprint searches for invariant, saturation, invariant open, generalization, descent datum, quasi-compact opens, flat relation, intersection of quasi-compact, and cartesian groupoid. The nearest ancestor is lem-a1-affine-hc0, and the new nodes prepend the item to its inherited via chain. No blueprint node states a new lemma. Searches of unrelated invariant group actions do not supply a result for arbitrary flat affine descent maps.

Each new node has its own semantic query and differently phrased second semantic query, plus Loogle and official Mathlib grep. The exact tool/query records and actual hit lists are in the JSON and searches.jsonl. The image node's closest results are QuasiCompact.isCompact_preimage, Scheme.Hom.isCompact_preimage and Flat.generalizingMap: none constructs the image, containing open, and intersection description in one specialization. I read UniversallyOpen.lean lines 133–143 to check the direction of Flat.generalizingMap, and AffineTransitionLimit.lean around line 1301 (the grep hit is a compact-intersection calculation in a limit argument). The other image hits concern quasi-separated equalizers and morphism composition. The relation hits concern ring-local flatness, affine charts and generic categorical descent. The complement hits are Haar measure results, specialization stability of complements, and closure-disjointness requiring an open subset, whereas K need not be open. Consequently none is a Mathlib leaf; there are zero leaves in this delivery.

## Not duplicates

lem-a1-flat-relation-qc-image-intersections vs lem-a1-fpqc-invariant-intersection-neighbourhoods: The item concerns invariant W and E from descent; this lemma is the geometric image/intersection argument for arbitrary flat quasi-compact maps and never produces an invariant open.

lem-a1-flat-relation-invariant-open-complement vs lem-a1-fpqc-invariant-intersection-neighbourhoods: The item needs an invariant intersection containing a point; this lemma starts with prescribed invariant K inside H and identifies the closure/complement construction only, with no intersection conclusion.

The singleton statement lem-pd-descent-orbit-saturated is reused directly in assembly step 2; its union consequence is elementary and becomes no new node. The existing lem-weil-pbc-spectral-generalizations-of-quasi-compact concerns a subset of an already spectral space; the new image node must construct that subset from two maps and a containing spectral open in a potentially non-quasi-compact scheme. The closure-specialization lemma says points specialize from an image; it says nothing about invariance or disjointness. I read these candidate statements as interfaces. Neither new lemma requires a finite locally free groupoid, a finite group action, or the affine invariant quotient theorem; those existing nodes have different hypotheses and conclusions.
## Review by Q47

I read groupoids.tex, lemma-constructing-invariant-opens (03LO), lemma-first-observation (0APA), lemma-second-observation (0APB), and lemma-cartesian-equivalent-descent-datum (0APF); more-groupoids.tex, lemma-ind-quasi-affine (0APK), the groupoid paragraph and translation (a),(b); topology.tex, lemma-make-spectral-space (0A31); and morphisms.tex, lemma-reach-points-scheme-theoretic-image (02JQ) and lemma-generalizations-lift-flat. The original item statement exactly matches the needed translation, with affine flat surjective p, V quasi-separated, an open W containing v, an invariant subset E containing W and a nonempty set-indexed family of quasi-compact opens. I retained the statement byte for byte. These sources require no SGA, finite presentation or Noetherian hypotheses.

Retained relation assembly (steps 1–2): p between affines is affine, so both projections (one identified through phi) are affine, quasi-compact and flat. The existing diagonal-identity statement gives the common section, and the existing singleton-orbit statement plus unions gives all subset saturations. This is old steps 1–2. These retained steps define R,s,t,e and sigma from the actual descent datum; they do not introduce an unrelated relation. Quasi-separatedness of V is not needed for these two assembly steps.

New image node: 0APA's proof uses only quasi-compactness of s, flatness of t and quasi-separatedness of V, so it applies to the stated pair of maps without groupoid laws. Compactness is in the induced topology, without a Hausdorff assumption. Flat generalization lifting proves stability of the image of the open preimage. A finite affine cover contains that quasi-compact image in a quasi-compact open H2. The inherited quasi-separatedness is checked by the two-clause affine-cover criterion, without assuming affine intersections are affine. H2 is spectral; 0A31 applied there gives the intersection of all quasi-compact open neighbourhoods. This family contains H2 and is a set; its members remain quasi-compact open in V. These are precisely old steps 3,6,7. The same lemma is applied twice in the assembly; it does not repeat its argument inline.

New complement node: the common section gives Z contained in sigma(Z); invariance of K and K contained in H give K disjoint from T. The closed subset s inverse Z is realized as a closed subscheme; its morphism to V through affine t is affine and hence quasi-compact. Thus 02JQ applies, even though T need not be constructible and V need not be quasi-compact. Both directions of closure invariance lift generalizations along s and t. Since K is closed under generalization, K remains disjoint from the closure. The complement is therefore the required invariant open between K and H. These are old steps 4–5. The explicit auxiliary assertions in the new statement retain the specific argument and its assumptions; this is not a renamed clause of the item.

Assembly citation check, with cited node statements open:

1. def-pc-fibre-product and def-pd-descent-datum identify the actual relation and its two projections through phi. lem-weil-pbc-morphism-affine-schemes-affine gives p affine from the item hypotheses. Clauses (1),(3) of lem-weil-pbc-affine-morphism-permanence give the base changes affine and quasi-compact, and lem-weil-pbc-flat-morphism-base-change gives flatness. lem-galois-descent-datum-diagonal-identity states exactly the diagonal identity needed for the common section. The explanatory pullback equality does not assume an effective descent datum.
2. lem-pd-descent-orbit-saturated states invariance for every singleton orbit under precisely these source-target maps. Inverse images commute with unions, so the union of these orbits is invariant; the identity section gives extensivity. This is elementary and the entire old argument is retained verbatim. This generic off-unit tool remains declared in split_report.tool_uses.
3. lem-weil-pbc-affine-opens-basis gives Q around the actual v. lem-weil-pbc-affine-scheme-qcqs supplies quasi-compactness. lem-a1-flat-relation-qc-image-intersections gives K stable under generalization and a quasi-compact containing H. V is quasi-separated by hypothesis, and flatness/quasi-compactness were supplied by step 1; invariance and Q contained in K come from step 2.
4. lem-a1-flat-relation-invariant-open-complement applies because steps 1–2 supply its section and its arbitrary-subset saturation axiom, and step 3 supplies precisely K,H with K invariant, generalization-stable and contained in H. Its conclusion gives the explicit W and all inclusions.
5. The second application of lem-a1-flat-relation-qc-image-intersections is to H, which is a quasi-compact open from step 3. The same maps and V satisfy the same hypotheses. The statement gives the nonempty family in V; step 2 gives H contained in E and invariance of E.
6. The two inverse-image identities follow by substituting s and t and applying the isomorphism phi. def-weil-open-immersion identifies open subschemes with their underlying opens and induced structure sheaves; it is precisely the fact used for W. E stays a subset. This final step is elementary. citations.json copies the verbatim used statements and gives every step/node pair.

B1–B9: both new nodes are statements with no proof or proof sketch inside the statement; every object and nonstandard notion is introduced or has a matching definition dependency. TeX is encoded once, no tag supplies a notion's meaning, and exact sources include tag and label. Searches were actually run and their results read; none is called a Mathlib match. Provenance is filled, no existing statement was duplicated, no new proof dependency points back to the item, and no compiler or Lean file was used. C1/C3/C4: the short assembly uses only the named node statements and the final elementary inverse-image calculation. It never reads another node's proof as a stronger interface. The retained old proof's generic inputs are requirements for the future splitting of the two children, not hidden claims in the parent assembly. D1/D2: two substantial arguments, independently usable, replace the long proof, rather than the whole item moved to one lemma. The most difficult new argument (image/intersection) is shared by two applications. E1–E7: no unproved openness of flat maps is used, no finite-presentation assumption is introduced, and no intersections of affine opens are asserted affine.

I tested V empty (parent vacuous), Q/H empty (sigma empty, with the empty open an allowed member of the nonempty neighbourhood family), p=id (sigma is identity), H=V when quasi-compact (Z=T=B empty and W=V), and the one-point scheme. For the complement node with K empty all assertions still hold; with the identity relation, W=H. The image node allows R empty and arbitrary non-quasi-compact V, since the containing H2 is built from finitely many affine opens. Quasi-compactness of E is never confused with openness of E or quasi-compactness of W. All new generalization statements explicitly use y in closure of {y-prime} so the specialization direction is unambiguous.

## Existing interface warning

The pre-existing statement lem-weil-pbc-flat-generalizations-lift reverses the direction: it asks to lift a point v specializing to f(t), whereas the source lemma and its name assert lifting of generalizations. An open immersion Spec Z[1/2] into Spec Z is flat; its generic point maps to (0), which specializes to (2), but there is no lift of (2). That is a concrete counterexample to the existing statement as written. I did not modify that other worker's node. The repaired item's assembly does not cite it; the two new statements use the correct direction explicitly. Future splits must use the correct Mathlib Flat.generalizingMap (UniversallyOpen.lean:134) or a corrected existing interface. The old proof itself always used the correct direction, as does Stacks. This does not dispute or change the item statement.

## Preserved returned argument, verbatim

Each paragraph below is copied verbatim from the current repository proof that the return named. Its uses and source are retained as well. It is the detailed handoff for parallel workers, not proof steps on the new unsplit nodes.

### Old step 1 — assigned to assembly steps 1–2

Write $a:V\to X$ for the structure morphism and put $R=V\times_S X$, $s=\operatorname{pr}_V:R\to V$, and $t=\operatorname{pr}_V\circ\varphi:R\to V$. The map $s$ is the base change of $p$ along $V\to S$; via $\varphi$, so is $t$. Since $X$ and $S$ are affine, [lem-weil-pbc-morphism-affine-schemes-affine] makes $p$ affine. Thus [lem-weil-pbc-affine-morphism-permanence](1),(3) and [lem-weil-pbc-flat-morphism-base-change] show that $s,t$ are affine, quasi-compact and flat. By [lem-galois-descent-datum-diagonal-identity], the pullback $\Delta^*\varphi:V\to V$ of $\varphi$ along the diagonal $\Delta:X\to X\times_S X$ is $\mathrm{id}_V$ (pulling the cocycle back along $X\to X\times_S X\times_S X$ gives $\alpha=\alpha\circ\alpha$ for this automorphism $\alpha$). Under the identifications of that node, $\varphi\circ(\mathrm{id}_V,a)=(a,\mathrm{id}_V)\circ\Delta^*\varphi$. Consequently the map $e:V\to R$ given by $(\mathrm{id}_V,a)$ satisfies $s e=t e=\mathrm{id}_V$.

Cited nodes: def-pc-fibre-product, def-pd-descent-datum, lem-galois-descent-datum-diagonal-identity, lem-weil-pbc-morphism-affine-schemes-affine, lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-flat-morphism-base-change.

Source: literature/stacks-project/groupoids.tex; Tag 0APF, lemma-cartesian-equivalent-descent-datum, specialized maps s and t; hypotheses of Tags 0APA and 0APB.

### Old step 2 — assigned to assembly steps 1–2

For any subset $A\subset |V|$ put $\sigma(A)=t(s^{-1}(A))$. For each $z\in A$, [lem-pd-descent-orbit-saturated] applied to the transport defined by $\varphi$ gives $s^{-1}(O_z)=t^{-1}(O_z)$ for $O_z=t(s^{-1}(\{z\}))$. Since $\sigma(A)=\bigcup_{z\in A}O_z$ and inverse images commute with unions, $s^{-1}(\sigma(A))=t^{-1}(\sigma(A))$. Moreover $A\subset\sigma(A)$ by the identity section in step 1. These assertions also hold for $A=\varnothing$. Here the orbit lemma applies to precisely $R=V\times_S X$ and the target $t$ defined by universal transport, not to an unrelated action.

Cited nodes: lem-pd-descent-orbit-saturated.

Source: literature/stacks-project/groupoids.tex; Tag 03LO, lemma-constructing-invariant-opens (1), using the existing singleton-orbit interface and unions.

### Old step 3 — assigned to lem-a1-flat-relation-qc-image-intersections

Choose an affine open $Q\subset V$ containing the prescribed point $v$ by [lem-weil-pbc-affine-opens-basis]. It is quasi-compact by [lem-weil-pbc-affine-scheme-qcqs], and $s^{-1}(Q)$ is quasi-compact by [lem-weil-pbc-quasi-compact-morphism-preimage-qc-open]. Hence $K=\sigma(Q)$ is quasi-compact: pull any open cover back along the continuous map $t$, choose a finite subcover of $s^{-1}(Q)$, and take its images. Also $K$ is closed under generalization. Indeed, if $y=t(r)\in K$ and $y'\leadsto y$, flatness of $t$ and [lem-weil-pbc-flat-generalizations-lift] give $r'\leadsto r$ with $t(r')=y'$. The open $s^{-1}(Q)$ contains $r'$ because it contains $r$, so $y'\in K$. Cover $K$ by affine opens of $V$ using the affine basis and take a finite subcover. Each affine open is quasi-compact by [lem-weil-pbc-affine-scheme-qcqs], so their finite union is a quasi-compact open $H\subset V$ containing $K$. In particular $Q\subset K\subset H$.

Cited nodes: lem-weil-pbc-affine-opens-basis, lem-weil-pbc-quasi-compact-morphism-preimage-qc-open, lem-weil-pbc-flat-generalizations-lift, lem-weil-pbc-affine-scheme-qcqs.

Source: literature/stacks-project/groupoids.tex; Tag 0APA, lemma-first-observation, quasi-compactness and generalization stability of the saturation; finite affine covering.

### Old step 4 — assigned to lem-a1-flat-relation-invariant-open-complement

Let $Z=|V|\setminus H$ and $T=\sigma(Z)$. Step 2 gives $Z\subset T$ and $s^{-1}(T)=t^{-1}(T)$. The subsets $K$ and $T$ are disjoint: if $y=t(r)$ were in both with $s(r)\in Z$, invariance of $K$ would give $s(r)\in K\subset H$, a contradiction. The subset $s^{-1}(Z)$ is closed. By [lem-weil-pbc-closed-subset-closed-subscheme] choose a closed immersion $j:C\to R$ with exactly this image. The morphism $h=t\circ j:C\to V$ is affine: for each affine open $L\subset V$, $t^{-1}(L)$ is affine, and [def-weil-closed-immersion] makes $j^{-1}(t^{-1}(L))$ affine. This is the affine-morphism definition [pqf-def-affine-morphism]. By [lem-weil-pbc-affine-morphism-permanence](3), $h$ is quasi-compact and its image is $T$. Therefore [lem-sc-picard-closure-specialization] gives, for every $y\in B=\overline T$, a point $y'\in T$ with $y'\leadsto y$. No constructibility or finite-presentation hypothesis on $T$ is needed.

Cited nodes: lem-weil-pbc-closed-subset-closed-subscheme, def-weil-closed-immersion, pqf-def-affine-morphism, lem-weil-pbc-affine-morphism-permanence, lem-sc-picard-closure-specialization.

Source: literature/stacks-project/groupoids.tex; Tag 0APB, lemma-second-observation, closed subset image; Tag 02JQ, morphisms-lemma-reach-points-scheme-theoretic-image (closure formulation).

### Old step 5 — assigned to lem-a1-flat-relation-invariant-open-complement

The closed subset $B$ is invariant. If $s(r)=y\in B$, choose $y'\in T$ with $y'\leadsto y$ by step 4. Flatness of $s$ and [lem-weil-pbc-flat-generalizations-lift] give $r'\leadsto r$ with $s(r')=y'$. Invariance of $T$ implies $t(r')\in T$, and continuity gives $t(r')\leadsto t(r)$, hence $t(r)\in B$. Conversely, starting with $t(r)\in B$, use the same specialization assertion and flatness of $t$ to lift a generalization into $t^{-1}(T)=s^{-1}(T)$; its image under $s$ specializes to $s(r)$, proving $s(r)\in B$. Thus $s^{-1}(B)=t^{-1}(B)$. Further, $K\cap B=\varnothing$: if $y\in K\cap B$, a generalization $y'\in T$ supplied by step 4 belongs to $K$ by step 3, contradicting $K\cap T=\varnothing$. Put $W=V\setminus B$. It is an invariant open with $v\in Q\subset K\subset W$, and $W\subset H$ since $Z\subset T\subset B$.

Cited nodes: lem-weil-pbc-flat-generalizations-lift.

Source: literature/stacks-project/groupoids.tex; Tag 0APB, lemma-second-observation, closure invariance and the open complement; both inclusions written out.

### Old step 6 — assigned to lem-a1-flat-relation-qc-image-intersections

Now put $E=\sigma(H)$. It is invariant by step 2, and $W\subset H\subset E$. Since $H$ is quasi-compact open, [lem-weil-pbc-quasi-compact-morphism-preimage-qc-open] makes $s^{-1}(H)$ quasi-compact, and pulling back an open cover shows that its continuous image $E$ is quasi-compact. If $y=t(r)\in E$ and $y'\leadsto y$, [lem-weil-pbc-flat-generalizations-lift] lifts $y'$ to $r'\leadsto r$; the open $s^{-1}(H)$ contains $r'$, hence $y'\in E$. Thus $E$ is closed under generalization. The affine basis [lem-weil-pbc-affine-opens-basis] and compactness give a finite union $H_2$ of affine opens of $V$ containing $E$. Each constituent is quasi-compact by [lem-weil-pbc-affine-scheme-qcqs], so this is a quasi-compact open; neither $W$ nor $E$ is asserted quasi-compact open.

Cited nodes: lem-weil-pbc-quasi-compact-morphism-preimage-qc-open, lem-weil-pbc-flat-generalizations-lift, lem-weil-pbc-affine-opens-basis, lem-weil-pbc-affine-scheme-qcqs.

Source: literature/stacks-project/groupoids.tex; Tag 0APA, lemma-first-observation, applied to H after the bounded invariant open of Tag 0APB.

### Old step 7 — assigned to lem-a1-flat-relation-qc-image-intersections

The open subscheme $H_2$ is quasi-separated. To check this without assuming that intersections of affines are affine, cover $H_2$ by affine opens of $V$ contained in $H_2$, using [lem-weil-pbc-affine-opens-basis]. Their pairwise intersections are quasi-compact by [lem-weil-pbc-quasi-separated-affine-cover-criterion](1) for the given quasi-separated scheme $V$. Clause (2) of that node applied to this cover of $H_2$ proves the assertion. Hence [lem-weil-pbc-qcqs-scheme-spectral] makes $|H_2|$ spectral. The subset $E$ remains quasi-compact in $H_2$ and is closed under generalization there. Its set of generalizations is therefore itself, so [lem-weil-pbc-spectral-generalizations-of-quasi-compact] identifies $E$ with the intersection of all quasi-compact opens of $H_2$ containing $E$. This family is a set and nonempty, since it contains $H_2$. Each member is also open and quasi-compact in $V$: openness composes for open subspaces, and the induced topology on each member is the same. This gives the required nonempty set-indexed family of quasi-compact opens of $V$.

Cited nodes: lem-weil-pbc-affine-opens-basis, lem-weil-pbc-quasi-separated-affine-cover-criterion, lem-weil-pbc-qcqs-scheme-spectral, lem-weil-pbc-spectral-generalizations-of-quasi-compact.

Source: literature/stacks-project/groupoids.tex; Tag 0APA, lemma-first-observation, spectral containing open; Tag 094L and Tag 0A31 (lemma-make-spectral-space).

### Old step 8 — assigned to assembly step 6

Finally $s^{-1}(F)=t^{-1}(F)$ is exactly $\varphi^{-1}(X\times_S F)=F\times_S X$ for any subset $F\subset |V|$, by the definitions of $s$ and $t$. Apply $\varphi$ to obtain the two asserted equalities for $F=W$ and $F=E$. For $W$ both inverse images are open subschemes, and equality of their underlying opens is equality of the induced open subschemes [def-weil-open-immersion]. For $E$ only subsets are used. Steps 5--7 provide $v\in W\subset E$ and the intersection description, so all clauses hold. If $V$ is empty the assertion quantified over $v$ is vacuous.

Cited nodes: def-weil-open-immersion.

Source: literature/stacks-project/groupoids.tex; Tag 0APF and Tag 0APK, more-groupoids-lemma-ind-quasi-affine, translation to clauses (a),(b).

## Unfinished work

The two new lemmas are intentionally statement-only and unsplit, as this return requires, ready for separate workers. No step of the original mathematical argument was dropped; all eight are preserved above. No requested repair remains pending. Dry run and delivery are performed with the official tools after this report is written.
