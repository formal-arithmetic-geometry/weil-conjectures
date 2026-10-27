## Worker report

Repair by Q14, 2026-10-22, of lem-trf-sharpening-fan-bijection.

The sandbox initially contained only dispatcher brief markers, with no node, report or searches.jsonl. I copied the current shared-repository item, which carries the returned fourteen-step argument, and preserved its statement byte for byte. No earlier sandbox argument or search result was discarded. I read AGENTS.md, SETUP.md's three levels, GOAL.md, the stage-1 brief, worker role, stage-1 specification, tools/README.md, and delivery-errors B--E. No repository, launcher or Lean file was written; no compiler or build was run, and no agent was started.

Files written: the item dag/nodes/sec-trace-formula/lem-trf-sharpening-fan-bijection.json, four new node files in the same chapter listed below, this report, and citations.json (sandbox evidence, one verbatim statement quotation per citation per assembly step). Search outputs and searches.jsonl are retained in the sandbox. The original fourteen proof steps are also retained in returned-proof.json and copied verbatim below.

## New nodes

- lem-trf-sharpening-blowup-chart-comparison: statement, unsplit, no Mathlib match. Covers old steps 1--3: ideal inverse operations, explicit product fraction charts, saturation, overlaps, closure of the domain, and ordered-tower induction with pullbacks.
- lem-trf-smooth-tower-index-synchronization: statement, unsplit, no Mathlib match. Covers old steps 4--6: smooth objects and the forward morphism assertion, exact contraction indices, smooth-surjective reflection of removability, and the two-map disjoint-union comparison.
- lem-trf-affine-lift-tower-descent: statement, unsplit, no Mathlib match. Covers old steps 8--10: one finite disjoint-union tower, smallest overlap neighborhoods and common product lifts, cocycle-compatible ideals, finite gluing and global contraction.
- lem-trf-fan-descent-refinement-pullback: statement, unsplit, no Mathlib match. Covers old steps 11--13: combined-cover index comparison, independence of lifts, smooth affine model maps and their localizations, synchronized local pullbacks, identity/composition and iterated contraction.

All four have empty proof and proof_deps and null proof_origin. These are separate arguments awaiting other workers; none asserts the bijection of rules or the two inverse composites. Their statements specify intermediate computations, maps and indices, rather than concealing that work behind a generic existence claim. The parent keeps the two constructions and checks their inverse composites in four assembly steps, with 2400 characters of proof text. The four old argument blocks contain respectively 2176, 1851, 2495 and 2301 characters (the original text below is authoritative); their sizes are comparable. Old steps 7 and 14 remain in the parent's assembly, in addition to its application of the four blocks.

Attachments: none. The exact blueprint tag and monoidal notions were searched in lean/WeilConjectures, and the existing lean/Sheaf/TraceFormula/SharpeningFanBijection.lean was read. Its final AlgebraicGeometry.sharpening_fan_bijection at line 539 and its sharp_blowup theorem contain sorry. Ordinary category-theoretic Fan.IsLimit.ofBijective is a product theorem, not a Kato-fan theorem. No project declaration without sorry states the item.

WANTED: none. The source is available locally.

What was wrong: the returned proof concentrated 14 arguments in one work item. This repair distributes them as requested without changing the statement or replacing the route. No additional mathematical statement correction is made. The already accepted domain restriction and source-error correction are retained, as explained below. Nothing remains unfinished in the authorized stage-1 delivery; proving the four statement-only nodes is subsequent work.

## Sources and searches

For the item and all four new nodes I read ILO, Travaux de Gabber, Expose VIII, printed pp.98--102, especially 3.1.4(iii), 3.1.11, 3.1.13--3.1.26, Lemma 3.1.25 and Theorem 3.1.27; I also read Remark 2.3.5(i)--(iii), printed p.92. A is the chart comparison of 3.1.17--3.1.25 expanded in the old proof. B uses smooth product charts of 3.1.13--3.1.16 and synchronization of 2.3.5(i),(iii), with the saturated whole-ideal convention. C realizes 3.1.26--3.1.27 and 2.3.5(ii) using the minimal-neighborhood statements of 3.1.4 and 3.1.11. D (file id ending refinement-pullback) expands refinement and pullback compatibility from 3.1.26--3.1.27, 3.1.14 and 2.3.5(ii)--(iii). No Stacks tag states these specific monoidal-space results, so their sources identify these exact places instead of an unrelated tag.

Before creating any new node I searched the whole DAG for sharpening, monoscheme, KatoFan, uncontracted towers, affine lifts, synchronization, the source places 3.1.25--3.1.27/2.3.5 and the proposed ids; I read the nearby statements discussed below. Whole-blueprint searches with tools/blueprint_refs.py used sharpening, saturated blowup, smooth surjection, affine lift, monoid, blowup tower, desingularization, blow up, monoscheme, coherent monoid and 3.1.25. The sharpening hit in the Fourier chapter is unrelated. No existing blueprint node states any new subargument. All blueprint.same_as fields are accordingly empty. The nearest ancestor is lem-trf-local-term-locality, with the inherited via chain, and each new node prepends this item and specifies the exact old steps and ILO place it serves. I read the current main-20261015 ancestor proof: it now follows contracting correspondences. This item is a historical auxiliary branch; neither that updated proof nor its unit/chapter route is changed here.

Each new node has five actual queries run through the required msearch.py: two differently phrased LeanFinder queries, a LeanSearch query, a Loogle query, and a grep of the pinned Mathlib source. The semantic queries name the new node id. Their exact outputs are in the node's mathlib_searches and in separate sandbox search-output files. I read every returned type: ordinary scheme ideal-sheaf maps and projective localizations do not sharpen monoid sheaves; scheme/ring smoothness theorems do not give product charts of monoids or contraction indices; ordinary scheme gluing and affine transition limits do not descend a monoscheme rule to fans. The number-field Associates and direct-limit hits in A's second phrasing likewise do not state that claim. Loogle's Monoscheme query found instances for Mono morphisms of ordinary schemes, not monoschemes. All four greps returned no hits. LeanSearch succeeded for A and B; for C and D it returned a rate-limit error, recorded as unavailable. Both have successful LeanFinder, Loogle and grep searches, so no unavailable search is represented as a negative result. The item's historical searches are retained unchanged, since its statement and search question did not change.

## Not duplicates

lem-trf-sharpening-blowup-chart-comparison vs lem-trf-fine-monoid-unit-splitting: the existing node splits a single monoid off its unit group; the new node compares ideals, saturated blowup fraction charts, glued towers and their pullbacks.
lem-trf-sharpening-blowup-chart-comparison vs lem-trf-toric-monoid-comparison: the existing comparison is with monoid algebras and normalized scheme blowups; this comparison is with sharp fans, with no field or ring realization.
lem-trf-sharpening-blowup-chart-comparison vs lem-trf-fine-monoid-finite-saturation: finite generation and localization of saturation alone do not identify sharp blowup charts or towers.
lem-trf-smooth-tower-index-synchronization vs def-trf-monoscheme-toric-realization: the definition only specifies smooth stalk maps and contracted towers; it does not prove reflection of removable stages, or the two-map equality.
lem-trf-smooth-tower-index-synchronization vs lem-trf-functorial-fan-desingularization: existence of a fan rule does not state smooth-surjective synchronization for any given rule, nor compare sharp and unsharp indices.
lem-trf-affine-lift-tower-descent vs lem-trf-affine-fan-localization-sections: the existing node identifies sections and stalks; it does not construct common monoscheme lifts or descend their synchronized towers.
lem-trf-affine-lift-tower-descent vs lem-trf-strict-fan-chart-local-comparison: the existing statement compares strict log-scheme fan charts; the new statement compares two unsharp monoscheme lifts of overlap fans and glues towers.
lem-trf-affine-lift-tower-descent vs lem-trf-functorial-log-blowup-etale-descent: the existing descent is for fs log schemes and strict etale charts, not arbitrary fine torsion-free fans and local monoscheme lifts, and assumes chart independence.
lem-trf-fan-descent-refinement-pullback vs lem-trf-affine-fan-hom-universal: the existing Hom/sections bijection does not identify cover refinements, pullback centers or contracted indices.
lem-trf-fan-descent-refinement-pullback vs lem-trf-functorial-log-blowup-etale-descent: the latter assumes chart independence and identity/composition comparisons and extends a log rule; this node proves these comparisons for the fan descent construction from a monoscheme rule.
lem-trf-affine-lift-tower-descent vs lem-trf-fan-descent-refinement-pullback: C proves overlap equality and existence for one fixed cover; D compares different covers and smooth maps. D uses C's constructed tower through stmt_deps, with no circular edge.

None of the new nodes is an elementary lemma: each contains the several-step argument reproduced in the allocated block below. None is a duplicate of the parent's entire statement: A is local geometry, B is synchronization, C is fixed-cover gluing, and D is comparison of that gluing; the parent still constructs both directions and proves the inverse identities. Sharing ILO 3.1.25--3.1.27 with the parent is precisely the requested re-split and is not a transfer of the whole statement to one node.

## Review by Q14

I checked the return's size and distribution requirements directly: four new statement-only nodes, comparable old argument blocks, no proofs in those nodes, unchanged parent statement, and four parent proof steps totaling 2400 characters. No non-elementary assembly step exceeds 2000 characters. Each old step is copied in full below with its new owner. I did not replace an explicit calculation by an assertion that it is standard. The new statements retain those calculations as precise intermediate claims for the next workers, and this report preserves the arguments they will formalize.

Assembly step 1 cites A for inverse image/image on coherent ideals, the fraction-chart isomorphism, closure of the domain and the unique tower correspondence; every one is explicitly in A's statement. It cites B for smooth terminal objects and the same contracted indices. B explicitly includes a nonidentity initial saturation and only claims that smooth monoscheme maps sharpen to smooth fan maps. I checked these exact quotations in citations.json against the node statements.

Assembly step 2 defines L(Q) using the unique tower lift in A; A's recursive pullback and chart substitution clauses give the comparison, while B gives smoothness of the sharpened map, smooth last objects, and the contraction convention. The identity and composite comparisons use the uniqueness and prescribed fraction maps, not an unquoted theorem on arbitrary functors. Q is on all fine torsion-free fans with finite affine covers; B and the domain hypotheses ensure every M-sharp used lies in that category.

Assembly step 3 uses exactly C's fixed-cover existence of a finite globally contracted smooth-ending tower and D's explicit cover/lift independence and smooth-pullback comparison with identity/composition laws. C takes R on the whole stated category, including finite disjoint unions; it does not assume independently chosen affine resolutions synchronize. D introduces its constructed tower explicitly and cites C through stmt_deps. Its formula with a Z^t factor is for the localized unsharpened monoscheme map, not a sharp fan stalk map; I clarified this wording in the self-check. I also clarified that the basic-open element in C sums only the generators outside the prime from a fixed generating set.

Assembly step 4 uses A for lifting then sharpening and uniqueness of the recovered towers, B for smooth-surjective synchronization (explicitly stated also for fans), C/D for the overlap and refinement identifications already established in step 3, and lem-trf-fine-monoid-unit-splitting for the affine smooth-surjective projections to sharp models. I opened this existing node: its statement requires both P-gp and B-gp to be torsion free and gives P = B + Z^s over B, exactly the projection used here. Both assumptions hold for every localized affine chart in our corrected category. Equality of centers on an open cover is elementary sheaf membership, and induction on the finite stages then identifies the complete towers via A. The inverse argument retains all original global indices, not only the contracted component towers.

For the argument delegated to A I opened the existing unit-splitting, finite-saturation and fs-face-sharpening statements. The first gives a splitting over B; the second states finite generation and saturation/localization compatibility; the third gives fine saturated sharp localized quotients with free abelian group completion. These are the facts the old chart argument actually uses. The new node does not silently use them as proved: its proof is empty and the old detailed calculation, including the product saturation formula and overlap localizations, is allocated below for its future split. For C/D I opened affine-fan-localization-sections and affine-fan-hom-universal: the former gives sections of D(a) and sharp localized stalks, and the latter states the full Hom/sections bijection, not just full faithfulness. Thus the old local map and neighborhood arguments have the necessary statements available when those workers split them.

I tested the new statements on the zero monoid and a pure unit group (sharp fan is one point, all whole-ideal saturated stages are identities), zero-length towers, r=0 and s=0 product factors, empty coherent ideals (only the ideal bijection includes these, never a blowup along an empty ideal), and empty fans/covers (identity functoriality forces the length-zero assigned tower). For P generated by 2 and 3 inside N, the whole-ideal saturated blowup is the nonidentity saturation N -> P, so both the sharp and unsharp towers retain that initial stage. The product formula with Z^s has the same property. In a cover, a stage can be a whole-ideal identity on just one component; C keeps that component's index and only tests removability globally. Repeated or enlarged finite covers are handled by D's combined-cover comparison; neither C nor D assumes affine overlaps globally, since the smallest neighborhoods cover them. Fans without global monoscheme lifts are explicitly included by C.

Against delivery-errors B--E: each node introduces its category, objects, hypotheses, constructions and conclusions, cites the existing definition nodes, uses ordinary TeX escaping, and carries an exact source place and blueprint provenance. I read every assembly citation and supplied its verbatim statement quote; every non-elementary assembly claim is an explicit conclusion of a cited node. There is no use of a cited proof instead of its statement, no off-unit tool, and no reverse edge to the parent. Empty proof fields respect B1. The new nodes are independent mathematical arguments rather than a single renamed parent clause. The source route and both torsion-free assumptions were checked, not replaced by an easier scheme result. The repairs during self-review were the two precision clarifications in C/D and making B's meaning of corresponding towers explicit. The first delivery dry run also rejected combined bracket citations in the new statements; I replaced each pair with two individual bracket citations, retaining both definition dependencies and updating citations.json.

## Retained source corrections

The item already restricts the monoscheme domain to objects with torsion-free sharp stalk groups. This is essential: let P in Z^2 be generated by (2,0), (-2,0), (0,1), (1,1). It is fine with P-gp = Z^2 and units 2Z x {0}, but (P/P-units)-gp = Z/2 + Z. Thus torsion-free ordinary stalk groups alone do not put its sharpening in the fan domain fixed by the definitions. This re-split preserves the accepted corrected domain and does not reopen or remove it.

ILO VIII 3.1.15 ends with a biconditional for smooth morphisms and sharpening; the reverse implication is false for the definitions used here. Multiplication by 2 on the group Z sharpens to 0 -> 0, but Z -> Z by multiplication by 2 is not a smooth product extension. Only the forward implication for morphisms and the valid equivalence for smooth objects are used in A/B and the assembly. This is the already reviewed source error, not a new change to the statement.

## Full allocation of the returned argument

The following is the complete returned proof text, without abbreviation. It is working material for the separate statement-only nodes, not proof steps entered into their JSON files. The parent's construction and inverse argument are retained as assembly steps 2 and 4.

### Returned step 1 -> lem-trf-sharpening-blowup-chart-comparison

An ideal of an integral monoid is stable under translation by every unit and its negative. Thus $\lambda^{-1}\lambda(I)=I$ and $\lambda\lambda^{-1}(J)=J$. The same formulas on germs define inverse operations on ideal subsheaves. A finite generating set maps to a generating set, and finitely many local representatives of generators generate the inverse image. Hence coherence, nonemptiness and the whole ideal are preserved. For any sheaf map the ideal generated by images commutes with these operations, since changing a representative by a unit does not change the generated ideal.

Source: VIII 3.1.18 and 3.1.25(i), pp.101--102.

Existing cited statements: def-trf-fine-fan-blowup, def-trf-monoscheme-toric-realization.

### Returned step 2 -> lem-trf-sharpening-blowup-chart-comparison

Work on an affine monoscheme chart with monoid $P$ and sharp quotient $B$. By [lem-trf-fine-monoid-unit-splitting] choose $P=B\oplus U$, $U\simeq\mathbf Z^s$, over $B$. The ideal corresponding to $J\subset B$ is $J\oplus U$. For a generator $a\in J$, its unsharpened blowup chart is $B[J-a]\oplus U$, because translating a lift of a generator by a unit adds only a unit to its differences. Its saturation is $(B[J-a])^{\rm sat}\oplus U$: a positive multiple lies in the product exactly when its first coordinate lies in $B[J-a]$. The sharpened spectrum is consequently exactly the fan chart for $J$. These charts are fine by [lem-trf-fine-monoid-finite-saturation], and their sharp stalk group completions are torsion free by [lem-trf-fs-face-sharpening]. In particular subsequent levels stay in the stated categories.

Source: VIII 3.1.17, 3.1.19--3.1.25(ii), pp.101--102; explicit product-chart calculation.

Existing cited statements: def-trf-fine-fan-blowup, def-trf-monoscheme-toric-realization, lem-trf-fine-monoid-unit-splitting, lem-trf-fine-monoid-finite-saturation, lem-trf-fs-face-sharpening.

### Returned step 3 -> lem-trf-sharpening-blowup-chart-comparison

On the overlap of the $a$- and $b$-charts the comparison of Step 2 localizes at $b-a$ and $a-b$. Both maps are the identity on the displayed fractions modulo units, so they agree on every triple overlap. The gluing prescription in [def-trf-fine-fan-blowup] gives a canonical global comparison. Starting with an ordered fan tower on $M^\sharp$, pull back its first ideal by Step 1, apply this comparison, and repeat at the next level. Induction on the finite length gives its unique corresponding ordered monoscheme tower. Conversely sharpening this construction recovers every stage and every center. This also proves compatibility with recursive pullback, since Step 1 commutes with generated image ideals and the chart comparison is unchanged by substituting their images.

Source: VIII 3.1.25(ii)--(iii), p.102, with overlap and induction details.

Existing cited statements: def-trf-fine-fan-blowup, def-trf-monoscheme-toric-realization.

### Returned step 4 -> lem-trf-smooth-tower-index-synchronization

Smooth monoscheme maps sharpen to smooth fan maps: at each stalk $P\to P\oplus\mathbf N^r\oplus\mathbf Z^t$ becomes $\overline P\to\overline P\oplus\mathbf N^r$. For objects, a smooth sharp stalk is $\mathbf N^r$; unit splitting identifies the corresponding unsharp stalk with $\mathbf N^r\oplus\mathbf Z^s$, which is smooth. The converse follows by taking its sharp quotient. For a whole-ideal stage, the saturated blowup is saturation itself; Step 2 shows that it is an isomorphism exactly when its sharp counterpart is. Thus corresponding towers have the same contracted indices, including on a nonsaturated initial object. No reflection of smoothness for arbitrary morphisms is used.

Source: VIII 3.1.15, 3.1.21--3.1.26, pp.100--102; only the valid direction of the morphism assertion is used.

Existing cited statements: def-trf-fine-fan-blowup, def-trf-monoscheme-toric-realization, lem-trf-fine-monoid-unit-splitting.

### Returned step 5 -> lem-trf-smooth-tower-index-synchronization

Here is the synchronization argument for any monoscheme rule $R$ in the statement. Along a smooth surjective map no stage is lost: localness of stalk maps reflects a whole pulled-back ideal; and, at a whole-ideal stage, a local smooth product $P\oplus\mathbf N^r\oplus\mathbf Z^s$ is saturated exactly when $P$ is. This product description persists after recursive blowups, since adjoining differences for the center affects only $P$, and saturation acts on that factor. Thus a removable stage after this surjective pullback was already removable before pullback. Functoriality for the identity implies $R(X)=R(X)^c$, so its assigned tower has no such stages. Therefore a smooth surjection gives equality of full ordered towers before contraction.

Source: VIII 3.1.13--3.1.16, 3.1.22--3.1.26; analogue of 2.3.5(i), p.92. Product verification includes the initial nonsaturated level.

Existing cited statements: def-trf-fine-fan-blowup, def-trf-monoscheme-toric-realization.

### Returned step 6 -> lem-trf-smooth-tower-index-synchronization

For two smooth maps $f,g:Y\to X$, adjoin the identity component and use $f\amalg1,g\amalg1:Y\amalg X\to X$. They are smooth surjections, so Step 5 identifies both full pullbacks with the single tower $R(Y\amalg X)$. Restricting to the $Y$ component proves $f^*R(X)=g^*R(X)$ as uncontracted towers with centers and indices. This argument uses neither a global lift of a fan nor a choice of separate affine resolutions.

Source: VIII Remark 2.3.5(iii), p.92, applied to the tower definition of 3.1.26.

Existing cited statements: def-trf-fine-fan-blowup, def-trf-monoscheme-toric-realization.

### Returned step 7 -> parent assembly step 2

Given a fan rule $Q$, define a monoscheme rule $L(Q)(M)$ by lifting the tower $Q(M^\sharp)$ through Step 3. Its last object is smooth by Step 4. For a smooth map of monoschemes, sharpen it, apply the given functoriality of $Q$, and lift the resulting centers one after another. Steps 1--4 identify the result with the contracted pullback. Since each ideal lift and each chart comparison is prescribed, identity and composite comparisons lift to the same comparisons. This constructs one direction on exactly the corrected monoscheme category.

Source: VIII 3.1.25--3.1.27, p.102.

Existing cited statements: def-trf-fine-fan-blowup, def-trf-monoscheme-toric-realization, lem-trf-fine-monoid-unit-splitting.

### Returned step 8 -> lem-trf-affine-lift-tower-descent

Conversely let $R$ be a monoscheme rule. For a finite affine cover $F=\bigcup_i S(P_i)$ take the sharp affine models $L_i=\operatorname{Spec}_{\rm mon}P_i$ and $L=\coprod_i L_i$. Here $P_i$ and all its localized sharp stalks have torsion-free group completions by the hypothesis on $F$, so every $L_i$ belongs to our domain. Take the ONE finite tower $R(L)$, and restrict it to each component without contraction. Sharpen these restricted towers. Empty stages on a component are retained at their original indices. We now compare their centers on overlaps before attempting to glue them.

Source: VIII 3.1.11, 3.1.26--3.1.27, pp.100,102; synchronization in 2.3.5(ii), p.92.

Existing cited statements: def-trf-fine-fan-blowup, def-trf-monoscheme-toric-realization, lem-trf-affine-fan-localization-sections.

### Returned step 9 -> lem-trf-affine-lift-tower-descent

Fix a point in the overlap of two cover charts. For a finite monoid generating set, sum the generators outside the point's prime ideal; its basic open is exactly the generalizations of that point. This is the smallest open neighborhood, affine in each chart, and its sharp sections are the sharp localized stalk monoid $B$ [lem-trf-affine-fan-localization-sections]. Unit splitting writes the two unsharp localizations as $B\oplus\mathbf Z^{s_i}$ and $B\oplus\mathbf Z^{s_j}$ over this same $B$. The common monoscheme $V=\operatorname{Spec}_{\rm mon}(B\oplus\mathbf Z^{s_i+s_j})$ maps smoothly and surjectively onto each. Composing with the two inclusions into $L$ gives two smooth maps $V\to L$. By Step 6 their full pullbacks of $R(L)$ coincide. By Steps 1--3 their sharpenings are precisely the two restricted fan towers on this neighborhood, with all original indices. They therefore have the same ideals at each stage. Such neighborhoods cover the overlap; their comparisons are the identity on the common ideals and fraction charts, so satisfy the cocycle condition.

Source: VIII 3.1.4(iii), 3.1.11, 3.1.25--3.1.27, pp.98,100,102; expands the local-lift comparison.

Existing cited statements: def-trf-fine-fan-blowup, def-trf-monoscheme-toric-realization, lem-trf-affine-fan-localization-sections, lem-trf-fine-monoid-unit-splitting.

### Returned step 10 -> lem-trf-affine-lift-tower-descent

Glue the first-stage ideals just shown equal: a section belongs to the glued ideal exactly when its restriction belongs to every local ideal. These ideals are coherent because that condition is local and each chart ideal is finitely generated. Glue their saturated blowup charts by the fraction identifications in [def-trf-fine-fan-blowup]; Step 9 identifies the restrictions of the next stage. Repeat for the common finite number $n$ of stages of $R(L)$. This constructs a finite tower on $F$, and its terminal sharp stalks are smooth by Step 4 applied to the terminal restrictions of $R(L)$. Each center is nonempty locally. A removable whole-ideal isomorphism globally would pull back to a removable stage on all components of $L$, contradicting identity functoriality for $R(L)$. Thus the glued tower is already contracted globally.

Source: VIII 3.1.26--3.1.27, p.102; explicit gluing in 2.3.5(ii), p.92.

Existing cited statements: def-trf-fine-fan-blowup, def-trf-monoscheme-toric-realization.

### Returned step 11 -> lem-trf-fan-descent-refinement-pullback

For two covers, use their combined finite cover and the rule on the disjoint union of all its lifts. Restriction to either subunion, followed by contraction, is its assigned rule there. The overlap equality in Step 9 shows that a stage of the combined tower is a whole-ideal isomorphism on one subcover exactly when it is so on the other: each subcover covers all of $F$, so this is a stalkwise test on $F$. Deleting precisely those common indices therefore gives the same glued tower from each cover. The same argument compares two choices of affine lifts, using the common product lifts of Step 9. Denote the resulting cover-independent tower by $S(R)(F)$.

Source: VIII 3.1.26--3.1.27, p.102; 2.3.5(ii)--(iii), p.92, refinement and index check.

Existing cited statements: def-trf-fine-fan-blowup, def-trf-monoscheme-toric-realization, lem-trf-fine-monoid-unit-splitting.

### Returned step 12 -> lem-trf-fan-descent-refinement-pullback

For a smooth fan map $g:G\to F$, work on the smallest affine neighborhoods of a point and its image. Their sharp monoids are the corresponding stalks, and [lem-trf-affine-fan-hom-universal] identifies the restricted map with the homomorphism on those stalks. It has form $B\to B\oplus\mathbf N^r$. This is a smooth map of the sharp monoscheme models: after localization, a local map has the form $B'\to B'\oplus\mathbf N^{r-t}\oplus\mathbf Z^t$, because localizing a free orthant inverts exactly a set of coordinates. Apply the smooth functoriality of $R$ to these models. To synchronize all local comparisons, include the finitely many source and target charts in one disjoint union, as in Steps 8--11; the uncontracted comparisons of Step 6 then put every local center at its inherited index. Steps 1--3 identify the sharpened centers with the recursive pullback along $g$. A stage disappears globally exactly when its pulled-back ideal is the whole sheaf and its morphism is an isomorphism, a local test. Thus $S(R)(G)=(g^*S(R)(F))^c$.

Source: VIII 3.1.13--3.1.16 and 3.1.26--3.1.27, pp.100,102; local smooth maps and synchronized pullbacks.

Existing cited statements: def-trf-fine-fan-blowup, def-trf-monoscheme-toric-realization, lem-trf-affine-fan-localization-sections, lem-trf-affine-fan-hom-universal.

### Returned step 13 -> lem-trf-fan-descent-refinement-pullback

The comparisons in Step 12 respect identities and composition. Before contraction, generated image ideals satisfy $(gh)^*I=h^*(g^*I)$; the maps on every fraction chart make exactly these substitutions. After contraction, the remaining indices are the ordered subsequence of stages that survive these same local tests. Removing an earlier whole-ideal isomorphism cannot change a later ideal or its pullback. Iterating contraction therefore gives the same indices and fraction maps as contracting once. The gluing comparisons are identities on the same local centers, so also obey these equalities globally.

Source: VIII 3.1.22, 3.1.25--3.1.27, pp.101--102.

Existing cited statements: def-trf-fine-fan-blowup, def-trf-monoscheme-toric-realization.

### Returned step 14 -> parent assembly step 4

Finally $S(L(Q))=Q$: on the disjoint union of the sharp affine models, lifting and sharpening recover $Q$ by Step 3, and its smooth-surjective cover pullback retains every global index by the argument of Step 5; gluing hence recovers $Q(F)$. In the other direction cover $M$ by affine monoschemes and apply unit splitting to each. Each is a smooth surjective lift of the sharp model. On disjoint unions these maps are still smooth surjections. Functoriality and Step 5 therefore identify $R$ on this cover with the lifted towers used to form $L(S(R))(M)$. Their ideals agree on the cover and hence agree globally, at every stage. Step 3 identifies the towers and their ordered centers. Thus $L(S(R))=R$, with the identity and composition compatibilities already checked. This proves the corrected rule bijection without requiring a global lift of $F$.

Source: VIII 3.1.25--3.1.27, p.102; finite-cover reconstruction of 2.3.5(ii), p.92.

Existing cited statements: def-trf-fine-fan-blowup, def-trf-monoscheme-toric-realization, lem-trf-fine-monoid-unit-splitting.
