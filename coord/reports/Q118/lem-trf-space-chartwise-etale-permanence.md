## Worker report

Files written:

- dag/nodes/sec-trace-formula/lem-trf-space-chartwise-etale-permanence.json — existing statement retained verbatim; four assembly steps, 2027 characters in their text.
- dag/nodes/sec-trace-formula/lem-trf-space-representable-etale-scheme-tests.json — statement-only, unsplit, no Mathlib match. This is the scheme-test and comparison-map task.
- dag/nodes/sec-trace-formula/lem-trf-space-etale-source-atlas-detection.json — statement-only, unsplit, no Mathlib match. This is the source-descent and cover-detection task.
- dag/nodes/sec-trace-formula/lem-trf-presheaf-field-lift-family-calculus.json — statement-only, unsplit, no Mathlib match. This is the underlying presheaf point-lifting task.
- citations.json — one literal statement quote per assembly-step citation.
- searches.jsonl — actual search-command records, retained without editing. Each new node records its own two semantic phrasings, Loogle, whole-Mathlib grep and the unavailable LeanSearch attempt; the source-cover task also has a third semantic query for its arbitrary-space cover.

Attachments: none. The project WeilConjectures tree contains no declaration for this item or the three new statements. The existing Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence theorem ends in sorry, and is not an attachment. No Lean was written or compiled.

WANTED: none.

The sandbox initially contained only the four launcher brief markers, with no node, report or search log from an earlier attempt. I recovered the current shared item's full ten-step returned split and Q58's earlier report, rather than starting from the old unsplit import. The exact returned node and report are retained as returned-node.json and prior-report-Q58.md in the sandbox. Existing item search records, statement, statement dependencies, source, historical blueprint ancestry and maintainer metadata are unchanged. The delivery tool rebases the owned split fields on current server main; no git command was run in the shared repository.

What was wrong: the returned proof concentrated 8171 characters of work in one item. This repair follows the human's explicit 2026-10-21 instruction to spread it among independent future workers. There is no statement dispute or source correction. In particular, shortening the parent alone would not repair the return. Three comparable new tasks are added, all with empty proof and proof_deps and null proof_origin; their statements have 1437, 1262 and 1393 characters. Their argument responsibilities are approximately 2672, 2410 and 1882 characters of the old proof. The remaining identity, composition and scheme-source equivalence arguments remain explicit in the parent. The full old argument is reproduced below, grouped by its new owner, so no verification, graph calculation, reassociation or field-extension argument disappears.

Nothing remains to repair mathematically. The new nodes intentionally join the unsplit queue: other workers are to supply their proofs, not this delivery. The present parent's short proof invokes their statements and carries the base-change and cancellation constructions explicitly.

## Blueprint and searches

Read GOAL.md, the three blueprint levels in SETUP.md, sec-trace-formula and sk-i-curve-zero, and the current main-20261015 statement and proof of lem-trf-local-term-locality. This remains a tool below the historical polarized-descent/enlarged-site chain. No unit or chapter route changes, no target statement changes, and no realized fields are appropriate. New nodes have from.node = lem-trf-local-term-locality and via = the parent followed by its existing via chain. Their from.place names the same enlarged-etale-site role and the precise returned proof steps they extract. The imported ancestor's unrelated contracting-correspondence proof is not replaced.

Before creating any node I searched the whole DAG by Stacks tags 025W, 03EC, 03FS, 03BU and 041F, by representable/atlas/etale/presheaf/field-lift keywords, and by the proposed names. Whole-blueprint searches included representable etale, representable diagonal, source atlas, scheme tests, field-valued, jointly surjective, surjective family, etale-local, and the tags above. None states these new tasks; same_as is empty. Existing definitions, scheme permanence leaves, source-descent theorem and fibre-product closure are reused as inputs to the handoff arguments below. I read the existing realization node, atlas presentation and stack calculus to distinguish statement content from facts appearing only inside proofs. The realization node actually depends on this item, so taking its proof as a source-atlas theorem would also be circular.

Each new node was searched with the required msearch.py command under Q118 and this item. The logged queries are copied exactly into mathlib_searches, with their actual JSON result records. I read all returned hit types. LeanFinder gives Scheme.Etale, IsEtale.of_comp and scheme permanence for the first two tasks. Those have Scheme source and target; no one-line specialization changes the target to an arbitrary algebraic space or establishes the representable-diagonal comparison. For the third task it gives Scheme.IsJointlySurjectivePreserving, Scheme.Cover and unrelated affine transition limit lemmas. I read Mathlib/AlgebraicGeometry/Morphisms/Etale.lean:39-157 and Mathlib/AlgebraicGeometry/Sites/MorphismProperty.lean:31-105, confirming the scheme scope. The latter's precoverage is induced from the underlying point set of a scheme; the new statement is for arbitrary presheaves and field-extension lifts. Loogle gives no hits for the three queries. Whole-Mathlib grep has no AlgebraicSpace/IsChartwiseEtale match; the joint-surjectivity grep gives only scheme declarations. LeanSearch returned an explicit rate-limit error for each query, recorded as unavailable, never as absence. There are zero new Mathlib leaves.

## Review by Q118

I checked delivery-errors B through E against the actual node files and source text. For the parent I read spaces-properties.tex 03FR and the paragraph after it, 03FT, 03FU and 03FV, and spaces-topologies.tex 041F with its preceding covering definition. For the scheme-test task I read spaces.tex 025W and spaces-properties.tex 03EC(1),(2), and the existing scheme composition, base-change, surjectivity and open-immersion statements. For source detection I read 03EC(3), 03FS, and descent.tex 036W, including its proof and the actual statement of lem-trf-etale-descent-through-source-cover. For field lifting I read spaces-properties.tex 03BU with its preceding common-extension relation and spaces-topologies.tex 041F(1)-(3). The point arguments omitted in 041F are preserved in full below; they are not asserted merely by naming the tag. No SGA route is used.

Parent step 1 uses exactly the new scheme-test statement's identity/isomorphism and representable-composition clauses. Testing on the scheme's identity gives one direction; composing a representable etale map with each scheme chart gives the other. For identity and chartwise composition the quantifiers themselves supply the argument. This is elementary relative to the cited statement. It never says that all chartwise etale maps are representable.

Parent step 2 uses def-trf-algebraic-space for the existing representable surjective etale atlas U to X, and only the first, closure sentence of lem-trf-space-fibre-products-etale-covers. The new scheme-test node supplies two genuinely representable base changes: R to P is the base change of U to X, and R to X' is the base change of U to Y. Chartwise etaleness of f makes that latter map representable etale before any chartwise base-change result has been used. The source-detection node's part (2) permits R to be an algebraic space, which is essential: R need not be a scheme. The reassociation R = P times_X U follows by keeping the same compatible pair (u,x'), with its image (p(u),x') in P. Thus every hypothesis of source-cover detection is present.

Parent step 3 uses the same atlas definition and the new scheme-test node for W = U times_Y V being a scheme and p being surjective etale. Here the source and target of the comparison r really are schemes. The chartwise hypotheses give ga and hb representable etale; composing ga with the scheme etale p gives gap. The exact comparison clause of the scheme-test node then applies over Z to (hb)r = gap and gives r etale. Representable composition gives br = fap representable etale. Source-detection part (1) has (W,V,q,p) specialized to (U,W,fa,p), and its scheme surjective etale cover hypothesis is exactly the one just checked. No separation, finite type, Noetherian or quasi-compactness hypothesis has been inserted.

Parent step 4 uses all three clauses of the presheaf lifting node, under the parent covering family's joint-surjectivity hypotheses. Its objectwise compatible-pair presheaf is exactly the underlying sheaf fibre product: pairs of sheaf sections with equal image glue uniquely coordinatewise. No sheafification change or surjectivity of points over the original field is asserted. The existing fibre-product node is again used only for algebraic-space closure, not its narrower representable-etale covering clause. Chartwise etaleness comes from the parent steps 1 and 2. The quotations in citations.json are full verbatim statements, exposing each hypothesis and every clause taken. proof_deps is exactly the union of the four uses lists.

For the new statements I checked that every object is introduced and every named notion is either written inline or cited in stmt_deps. None uses the parent statement as a dependency: chartwise etaleness is written out in the source-detection node. The scheme-test and source-detection statements need only the existing fibre-product closure, so they do not form a cycle through chartwise permanence. The presheaf node deliberately needs neither a sheaf nor an algebraic-space hypothesis. The scheme-test task is not simply scheme permanence: the hard boundary is the representable diagonal and scheme tests over an arbitrary algebraic space, including the graph-section comparison. The source-detection task is a local criterion, not a new node saying base change or cancellation is true. The presheaf task separates point lifting from etaleness rather than restating the etale covering clauses. These are the actual arguments of the returned proof. The human's explicit re-split instruction requires extracting even the longer point-lift work formerly marked elementary, instead of leaving that work in a large parent or silently discarding it.

Small-case checks: an identity atlas gives the scheme-source test; the empty scheme gives empty scheme tests and an empty surjective cover only over an empty target. A chartwise etale morphism need not be representable: this is why source-detection part (2) is one-way for an arbitrary-space cover R, whereas part (3) is an equivalence only for a scheme atlas. No incorrect converse is present. Non-separated and disconnected spaces still have the required representable diagonals and atlases. For field lifting, test the separable extension Spec L to Spec K to see why extensions, rather than K-rational lifts, are needed. In the presheaf assertion, an empty jointly surjective family forces no target field-valued sections; a map F' to F then forces no F' field-valued sections, so the empty pullback family works. Restriction of a compatible pair keeps equality by naturality, and a K to L to M tower yields the original section restricted along the composite embedding. No common algebraic closure or geometric-point lifting theorem is hidden here.

All four parent steps are below 2000 characters, and their total is below 3000. I checked the three constructions rather than relying only on this bound: the fibre-product reassociation, the graph-section comparison (handed to the first node), and source descent (handed to the second) are accounted for. All three new nodes are statement-only. B's and E's self-containedness and edge-case requirements, C's exact-statement citation and non-elementary-input requirements, and D's prohibition on moving the entire item into one node are met by the explicit ownership map and full handoff arguments below. No file outside the sandbox was written.

## Not duplicates

lem-trf-space-representable-etale-scheme-tests vs lem-trf-space-chartwise-etale-permanence: the new task concerns representable morphisms, arbitrary scheme tests, and comparison maps between schemes over an algebraic space; it does not assert chartwise base change, chartwise cancellation or covering axioms.
lem-trf-space-representable-etale-scheme-tests vs lem-sfb-stack-chartwise-smooth-etale-calculus: the latter concerns chartwise properties of stack morphisms representable by algebraic spaces, not representability by schemes of scheme-source maps or the scheme comparison-map conclusion; these conclusions are not specializations of its statement.
lem-trf-space-etale-source-atlas-detection vs lem-trf-space-chartwise-etale-permanence: the new task supplies source-cover detection and the atlas criterion, not the parent's permanence or covering clauses. The base-change and cancellation constructions stay in the parent.
lem-trf-space-etale-source-atlas-detection vs lem-trf-etale-descent-through-source-cover: the existing theorem is exclusively for three schemes; the new task detects representable or chartwise etaleness with an arbitrary algebraic-space target, and permits a cover with arbitrary algebraic-space source in part (2).
lem-trf-space-etale-source-atlas-detection vs lem-sfb-stack-chartwise-smooth-etale-calculus: open-source-cover locality in the stack calculus does not state descent along a surjective etale source cover, nor the scheme-test criterion for representable etaleness. The common 03FS tag is an input, not equality of statements.
lem-trf-space-etale-source-atlas-detection vs lem-a1-etale-sheaf-algebraic-space-realization: realization is an equivalence with sheaves on a scheme's small etale site; source-atlas detection occurs only in its proof and it already depends on the parent, so it cannot be cited for this statement.
lem-trf-presheaf-field-lift-family-calculus vs lem-trf-space-chartwise-etale-permanence: the new lemma has arbitrary presheaves and natural transformations, imposes no etaleness, and proves the underlying point-lifting assertions. It does not state any etale permanence or covering axiom.
lem-trf-presheaf-field-lift-family-calculus vs lem-trf-space-fibre-products-etale-covers: that existing statement concerns algebraic spaces and a representable etale covering family; the new statement is for arbitrary presheaf maps and also includes family composition and isomorphisms.
lem-trf-presheaf-field-lift-family-calculus vs def-trf-algebraic-space-jointly-surjective-family: the existing definition states the lifting condition and its interpretation on point classes, but no family composition or pullback theorem.
lem-trf-presheaf-field-lift-family-calculus vs def-a1-algebraic-space-point-classes: the existing definition constructs point classes, not the lifting calculus for presheaf families.
lem-trf-presheaf-field-lift-family-calculus vs def-a1-space-point-topology: the existing definition introduces the topology and images, not stability of the lifting condition.
lem-trf-presheaf-field-lift-family-calculus vs lem-a1-space-affine-etale-cover: that theorem constructs an affine atlas and proves topological properties of algebraic-space points; it does not state the arbitrary-presheaf composition or compatible-pair lifting assertion.

## Source-detection handoff: the generalized cover argument

This is proof material for the future worker, kept out of the statement-only node. Part (1) is precisely returned step 4 below. For part (2), take a representable etale scheme chart a:W to X and set Q = W times_X R. Representability of p makes Q a scheme and Q to W surjective etale. Scheme-test base change makes Q to R representable etale, and its composite with fp is representable etale. Part (1), with scheme cover Q to W, makes fa representable etale. Since a was arbitrary, f is chartwise etale. This argument neither assumes chartwise base change nor claims R is a scheme. Part (3) follows from part (2) and the chartwise test on the given scheme atlas; its existence is part of def-trf-algebraic-space. The scheme-test operations here are exactly the first new task, and scheme source descent is the existing lem-trf-etale-descent-through-source-cover after arbitrary scheme tests, as in returned step 4.

The generic cover argument subsumes precisely the compatible-tuple calculation of returned step 6. The parent still constructs R and both its maps explicitly, and parent cancellation keeps the compatible presentation from returned step 8. No lifting of an atlas along a map is assumed without constructing U times_Y V.

## Full returned argument, with ownership

The following texts are copied without shortening from the returned head. Steps 1,2,7 belong to the scheme-test task; steps 4,6,8 belong to the source-cover task and its two explicit applications retained in the parent; steps 9,10 belong to the presheaf lifting task. Steps 3,5 remain the direct assembly in parent step 1. The square-bracket citations in these handoff texts refer to existing nodes whose actual statements were read; references to an old step refer to the old numbering below. Their proof fields are not put in the three new nodes, as the return requires statement-only deliveries.

### Returned step 1

Every map $U\to F$ from a scheme to an algebraic space is representable. Indeed, for a scheme $T\to F$, the sheaf $U\times_F T$ is the pullback of the representable diagonal $F\to F\times F$ along the scheme $U\times_S T\to F\times F$. It is therefore a scheme by [def-trf-algebraic-space] and [def-pc-fibre-product]. The identification follows on each test scheme: both sides consist of a pair of maps to $U,T$ with equal images in $F$. In all later steps, this also proves that a fibre product of two schemes over an algebraic space is a scheme.

Uses: def-trf-algebraic-space, def-pc-fibre-product.

Source: literature/stacks-project/spaces.tex; Tag 025W (lemma-representable-diagonal), the formal diagonal test; algebraic-space definition Tag 025Y.

### Returned step 2

We first record the scheme-test calculations for representable maps; these do not assume chartwise permanence. For representable etale maps $A\to B\to C$ and a scheme $T\to C$, the pullback of their composite factors as the two etale scheme maps $T\times_C A\to T\times_C B\to T$. It is etale by [lem-weil-pbc-etale-composition-cancellation](2). For a base change along $C'\to C$, its pullback to a scheme $T\to C'$ is just $T\times_C A\to T$, so representable etaleness is preserved by definition [def-trf-algebraic-space]. Isomorphisms are representable etale: their scheme tests are isomorphisms, hence open immersions by [def-weil-open-immersion], hence etale by clause (1) of the same scheme lemma. For representable surjective etale maps these arguments also preserve surjectivity: in the composite both scheme projections are surjective and [lem-trf-surjective-morphism-composition] applies; for a base change the scheme test is the original test. When a surjective etale scheme map is pulled back along another scheme map, the two properties follow from [lem-weil-pbc-surjective-base-change] and [lem-weil-pbc-etale-scheme-base-change]. In particular an etale scheme morphism is representable etale, since all its scheme tests are etale by the same base-change lemma. All fibre-product identifications here send a compatible tuple of sections to the same tuple and are inverse by their projections.

Uses: def-trf-algebraic-space, lem-weil-pbc-etale-composition-cancellation, def-weil-open-immersion, lem-trf-surjective-morphism-composition, lem-weil-pbc-surjective-base-change, lem-weil-pbc-etale-scheme-base-change.

Source: literature/stacks-project/spaces.tex; Representable-property scheme tests used in spaces-properties.tex Tag 03EC(1); scheme Tags 02GN, 02GP, 02GO, 01RZ, 01S1.

### Returned step 3

If $f:U\to Y$ has scheme source and is chartwise etale, test it on $\operatorname{id}_U$, which is representable etale by step 2. This says exactly that $f$ is representable etale. Conversely, if $f$ is representable etale, its composite with every representable etale scheme chart of $U$ is representable etale by step 2; thus it is chartwise etale. This uses the scheme-test meaning of representability and etaleness in [def-trf-algebraic-space], rather than asserting that all chartwise etale maps with arbitrary source are representable.

Uses: def-trf-algebraic-space.

Source: literature/stacks-project/spaces-properties.tex; Tag 03FR, paragraph immediately following the definition; scheme-source specialization.

### Returned step 4

Here is the source descent calculation needed below. Let $q:U\to F$ have scheme source, and let $p:V\to U$ be a surjective etale scheme map such that $qp$ is representable etale. For any scheme $T\to F$, step 1 makes $U_T=U\times_F T$ and $V_T=V\times_F T$ schemes. The projection $V_T\to U_T$ is the scheme base change of $p$, hence surjective etale by [lem-weil-pbc-surjective-base-change] and [lem-weil-pbc-etale-scheme-base-change]. The composite $V_T\to T$ is etale by the hypothesis on $qp$. Apply [lem-trf-etale-descent-through-source-cover] with its $(T,X,Y)=(T,U_T,V_T)$ to obtain that $U_T\to T$ is etale. Since $T$ was arbitrary, $q$ is representable etale by [def-trf-algebraic-space].

Uses: def-trf-algebraic-space, lem-weil-pbc-surjective-base-change, lem-weil-pbc-etale-scheme-base-change, lem-trf-etale-descent-through-source-cover.

Source: literature/stacks-project/spaces-properties.tex; Tag 03EC(3), scheme-test proof; descent.tex Tag 036W (lemma-etale-etale-local-source).

### Returned step 5

For the identity of an algebraic space, composition with a representable etale scheme chart is that same chart; hence the identity is chartwise etale. If $X\xrightarrow{f}Y\xrightarrow{g}Z$ are chartwise etale and $U\to X$ is a representable etale scheme chart, first $U\to Y$ is representable etale by the definition of $f$, and then $U\to Z$ is representable etale by the definition of $g$. This proves composition. An isomorphism is representable etale by step 2, so its composite with a scheme chart is representable etale by the same step. It is therefore chartwise etale too. The maps and the charts here have exactly the meanings in [def-trf-algebraic-space].

Uses: def-trf-algebraic-space.

Source: literature/stacks-project/spaces-properties.tex; Tags 03FR and 03FT (lemma-composition-etale); identity and isomorphism cases of the definition.

### Returned step 6

Let $f:X\to Y$ be chartwise etale, let $X'\to Y$ be arbitrary, and put $P=X\times_Y X'$, an algebraic space by [lem-trf-space-fibre-products-etale-covers]. Choose a representable surjective etale atlas $U\to X$ from [def-trf-algebraic-space]. Since $f$ is chartwise etale, $U\to Y$ is representable etale. Consequently $R=U\times_Y X'\to X'$ is representable etale by step 2. Given any representable etale scheme chart $W\to P$, form $Q=W\times_P R=W\times_X U$. The second expression makes $Q$ a scheme and $Q\to W$ a surjective etale scheme map, by the atlas's scheme tests. The first makes $Q\to R$ representable etale, as the base change of $W\to P$. Step 2 then makes $Q\to X'$ representable etale. Apply step 4 to $Q\to W\to X'$ to conclude that $W\to X'$ is representable etale. Since $W$ was arbitrary, $P\to X'$ is chartwise etale. The equality between the two expressions for $Q$ is the explicit reassociation of the compatible tuples $(w,u)$ with their common image in $X$.

Uses: def-trf-algebraic-space, lem-trf-space-fibre-products-etale-covers.

Source: literature/stacks-project/spaces-properties.tex; Tag 03FU (lemma-base-change-etale): atlas proof with its omitted verification supplied by scheme tests and source descent.

### Returned step 7

For later cancellation, suppose $A,B$ are schemes, $F$ is an algebraic space, $a:A\to F$ and $b:B\to F$ are representable etale, and $r:A\to B$ satisfies $br=a$. By step 1 the fibre product $E=A\times_F B$ is a scheme, and both projections $\pi_A,\pi_B$ are etale by the scheme-test definition [def-trf-algebraic-space]. The graph $s=(\operatorname{id}_A,r):A\to E$ satisfies $\pi_A s=\operatorname{id}_A$. The identity is etale by step 2, so [lem-weil-pbc-etale-composition-cancellation](3), applied to the scheme maps $s,\pi_A$, makes $s$ etale. Clause (2) then makes $r=\pi_Bs$ etale. This is a two-application consequence of scheme cancellation and composition, not a separate algebraic-space permanence assumption.

Uses: def-trf-algebraic-space, lem-weil-pbc-etale-composition-cancellation.

Source: literature/stacks-project/spaces-properties.tex; Tag 03EC(2); elementary graph-section argument using morphisms.tex Tags 02GW and 02GN.

### Returned step 8

Suppose $g:X\to Z$, $h:Y\to Z$ are chartwise etale and $hf=g$. Given a representable etale scheme chart $a:U\to X$, choose a representable surjective etale atlas $b:V\to Y$ by [def-trf-algebraic-space]. The fibre product $W=U\times_Y V$ is a scheme by step 1, and $p:W\to U$ is surjective etale by the scheme tests for $b$. Let $r:W\to V$ be the other projection. Both $ga:U\to Z$ and $hb:V\to Z$ are representable etale by the two chartwise hypotheses. Therefore $gap:W\to Z$ is representable etale by step 2. Since $(hb)r=gap$, step 7 makes $r$ an etale scheme map. Step 2 makes $br=fap$ representable etale; step 4 then makes $fa:U\to Y$ representable etale. This proves that $f$ is chartwise etale, for every $U$ as required.

Uses: def-trf-algebraic-space.

Source: literature/stacks-project/spaces-properties.tex; Tag 03FV (lemma-etale-permanence); choose the source presentation by U times_Y V and use Tag 03EC(2),(3).

### Returned step 9

Use the definition of covering in the statement. An isomorphism is chartwise etale by step 5, and its inverse lifts every field-valued section over the same field, so it is a singleton covering. For composable covering families $X_i\to X$ and $X_{ij}\to X_i$, the composites are chartwise etale by step 5. Given a section $x$ of $X$ over a field $K$, [def-trf-algebraic-space-jointly-surjective-family] gives $i$, an extension $K\hookrightarrow L$, and $y\in X_i(L)$ mapping to $x|_L$. Applying the same definition to $y$ gives $j$, an extension $L\hookrightarrow M$, and $z\in X_{ij}(M)$ mapping to $y|_M$. The composite field embedding $K\hookrightarrow M$ and $z$ lift $x|_M$, because restrictions and the given natural transformations compose. Thus the composite family is jointly surjective and is a covering. This also handles empty index sets: whenever a target field-valued section exists, the covering hypothesis supplies the required index.

Uses: def-trf-algebraic-space-jointly-surjective-family.

Source: literature/stacks-project/spaces-topologies.tex; Tag 041F (lemma-etale), clauses (1),(2); omitted point-lifting argument expanded using spaces-properties.tex Tag 03BU.

### Returned step 10

Finally let $\{X_i\to X\}$ be a covering and $a:X'\to X$ any map. By [lem-trf-space-fibre-products-etale-covers] each sheaf $P_i=X'\times_X X_i$ is an algebraic space; step 6 makes $P_i\to X'$ chartwise etale. For $x'\in X'(\operatorname{Spec}K)$, apply [def-trf-algebraic-space-jointly-surjective-family] to $a(x')$. Obtain $i$, a field extension $K\hookrightarrow L$, and $y\in X_i(\operatorname{Spec}L)$ with $f_i(y)=a(x')|_L$. The pair $(x'|_L,y)$ is exactly a section of the sheaf fibre product $P_i$ and lifts $x'|_L$. Thus the new family is jointly surjective and is a covering. No representability of $X_i\to X$ is used: from the existing fibre-product node we use only closure under fibre products, not its covering clause, which assumes representable etaleness. If the given index set is empty, any field-valued section of $X'$ would give one of $X$, contradicting the covering hypothesis; hence the same conclusion holds.

Uses: lem-trf-space-fibre-products-etale-covers, def-trf-algebraic-space-jointly-surjective-family.

Source: literature/stacks-project/spaces-topologies.tex; Tag 041F (lemma-etale), clause (3); field-extension lifting supplies its omitted proof.
