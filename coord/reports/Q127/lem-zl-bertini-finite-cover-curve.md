# Worker report: Q127 repair

## Files written

- dag/nodes/sec-deligne-laumon-general/lem-zl-bertini-finite-cover-curve.json: unchanged statement, three-step assembly.
- dag/nodes/sec-deligne-laumon-general/lem-zl-bertini-prescribed-point-smooth-system.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-deligne-laumon-general/lem-zl-bertini-finite-cover-irreducible-system.json: statement, unsplit; no Mathlib match.
- citations.json: verbatim statements for every cited node at every assembly step.

## Attachments

None. I read WeilConjectures/AlgebraicGeometry/Bertini.lean:73-90; AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_connectedSpace_pullback has a sorry body, so cannot attach. Source searches over the project for prescribed points, jet separation, finite base loci and independent differentials found no finished declaration of either extracted statement.

## WANTED

None; all sources used are available locally.

## What was wrong / repaired

This is the deliberate re-split requested on 2026-10-21. No saved node/report existed in this sandbox (only dispatcher markers), so I used the live reviewed node, preserving its statement, blueprint_update, citations, Lean record and maintainer fields. The live split is the returned 5755-character proof; being split/reviewed does not supersede this assignment. Two independent substantive arguments are now separate statement-only tasks, rather than one replacement for the full theorem. Both work over arbitrary algebraically closed k, so the induction never assumes a finite-field model of an intermediate cut. The assembly proof has 1987 characters (below 3000).

There is no statement dispute. I corrected a bibliographic detail in the extracted jet argument: in the local Stacks checkout the proper-scheme Serre vanishing lemma is Tag 0B5T, coherent.tex lemma-coherent-proper-ample (4), not 0B5U (lemma-vanshing-gives-ample). The existing serre-vanishing node states the needed vanishing correctly and is not edited.

## What remains

The two new nodes intentionally have status unsplit, empty proof/proof_deps and null proof_origin. Their proofs are future parallel work; all of the argument they inherit is preserved below as handoff material, not smuggled into their statements. No Lean was written, no compiler/build was run, no repository or launcher file was edited.

## Review by Q127

I read the current main-20261015 item proof, the fixed chapter and unit records, and Stacks varieties.tex lemma-generate-over-complement (0FD5), Situation family-divisors (0FD3), lemma-bertini (0FD6), and more-morphisms.tex lemma-bertini-irreducible (0G4F). For the first new node I also read coherent.tex lemma-coherent-proper-ample (0B5T), and algebra.tex 00NQ, 00NP and 00TV. For the second I read varieties.tex 0B2G and 038X and algebra.tex 00NP, 00NQ, 00KW. I opened every formerly cited node's statement, including Serre vanishing, the smooth/geometric-regularity criterion, regular local hypersurface criterion, regular-closed-point smoothness, rational unramified cotangent criterion, domain theorem, height bound, all three Bertini inputs, and finite-field descent. The old argument uses the actual statements of those tools; the complete argument is allocated below.

Step 1 now cites precisely the new smooth-system and finite-cover irreducible-system statements. The first supplies the same V_n, generation and immersion off S, and the nonempty smooth open, including pure dimension d-1 and affineness. The second accepts exactly that system, the given connected finite etale cover, and the same nonempty finite S; it supplies the second nonempty open, both geometric irreducibilities, and the finite etale connected pullback for a smooth member. No 0FD6 application is made to T, whose map need not be an immersion. Intersection of two nonempty opens of affine space and the existence of a point over algebraically closed k are elementary. Step 2 is explicit induction on e, with base case e=1, quotient-ring composition of the closed immersions, and pullback associativity; it needs no additional geometric theorem. The input X is connected by the original geometric-connectedness assumption. Step 3 cites the existing descent statement, which I read in full: finite type X_0 and a closed subscheme suffice, and it gives the actual model and displayed automorphism, not just a field of definition for unrelated data. Smooth plus affine implies finite type since affine morphisms are quasi-compact. citations.json quotes exact substrings of these three statements.

I checked B--E against the actual files: every new object is introduced, all notions have definition dependencies or explicit definitions, single-escaped TeX is used, no proof occurs in the new nodes, every original non-elementary assembly fact is cited, and there is no cycle back from either new statement. The blueprint ancestor is this item with empty via; whole-blueprint searches for jet, prescribed points, unramified linear, linear system and tags were made and no equivalent statement was found. All recorded Mathlib queries were really run through msearch.py and all hits read: the local etale/base-change APIs, smooth-chart lemmas and polynomial/manifold results do not state either extracted theorem in one specialization; the two semantic phrasings and grep give no leaf. The same-tag distinctions are listed below. No new assembly step exceeds 2000 characters.

Small cases: d=2 produces a smooth one-dimensional cut immediately, with finite base locus still codimension two. For S a singleton, the nonzero cotangent-vector condition is still nonempty because d>=2; for several points surjectivity is simultaneous, not a separate choice of n for each vector. For the identity cover the second node reduces to the ordinary irreducibility criterion. For a nontrivial connected finite etale cover, nonemptiness and connectedness force surjectivity onto connected X; an empty cover is excluded by connectedness. Requiring d>=2 excludes the curve case where prescribing several points would obstruct irreducible zero-dimensional cuts. Positive characteristic causes no separability defect: immersion downstairs and etaleness upstairs give the needed cotangent surjections. The first new node does not claim smoothness for all sections, only on a specified nonempty open, and the second does not claim that every member is smooth.

## Allocation of every old argument (proof handoff, new nodes remain statement-only)

### lem-zl-bertini-prescribed-point-smooth-system

This task carries old steps 1 and 2 in full, and the affine/dimension verification in old step 4. Begin with the chosen projective closure. Use existing lem-zl-bertini-sections (0FD5) to get generation and immersion outside S. Let J be the ideal of the disjoint union of the first infinitesimal neighborhoods of S, so J is the square of the reduced ideal locally at each s. Its coherence follows from the noetherian projective closure. For n large, H^1(J(n))=0 by existing lem-pc-serre-vanishing (correct local tag 0B5T); the exact sequence J(n) -> I_S(n) -> (I_S/J)(n) gives surjectivity onto the direct sum of cotangent spaces. At s the stalk of the closure equals that of X because X is open in its closure. In particular V_n is finite-dimensional by proper coherent H^0 finiteness, and every derivative nonzero condition is a nonempty open complement of a proper linear kernel. Intersect those finitely many conditions with the smooth-member open of 0FD6 on X minus S. At a point of S, a nonzero first derivative is f in m minus m^2; the old regularity, hypersurface and regular-closed-point smoothness nodes turn it into smoothness. This is exactly why base points do not invalidate the use of smooth Bertini away from S. The cut is a closed subscheme of affine X. On smooth connected X the local rings are regular domains and the nonzero section is a Cartier equation; at each closed point on the smooth zero scheme its quotient has dimension d-1 (00NQ/00KW). This yields the pure relative dimension claimed. The finite set S makes the cut nonempty. This task contains neither cover connectedness nor iteration nor arithmetic descent.

### lem-zl-bertini-finite-cover-irreducible-system

This task carries all of old step 3, the smoothness-on-the-cover sentence in old step 2, and stability of finite etaleness in old step 4. Smooth connected X over algebraically closed k is regular with disjoint irreducible components, hence integral and geometrically irreducible. Finite etaleness and connectedness give the same facts for T, of dimension d; the finite etale map is surjective since its nonempty image is open and closed in connected X. The base loci of the two systems have supports S and pi^{-1}(S), finite closed sets of codimension d. On either Y in {X,T}, choose a closed point y away from this base locus. Generation supplies v_1 nonvanishing at y. The associated map Y minus base locus -> P(V) is unramified: it is an immersion on X and an etale map followed by that immersion on T. The existing rational-unramified-cotangent criterion gives surjectivity on cotangent spaces; projective coordinate ratios give v_2,v_3 vanishing at y with independent cotangent images. In the regular local ring R at y, R/(f_2) and R/(f_2,f_3) are regular, using the nonzero image of f_3 in the cotangent space after the first quotient. Both quotients are domains by the existing regular-local-domain node. Thus p=(f_2,f_3) is prime and is the unique local component of the common zero scheme. The strict prime chain 0 < (f_2) < p gives height at least two; the existing noetherian-height-quotient bound gives height at most two. Hence its corresponding global component W has codimension exactly two and is not contained in H_{v_1}, since v_1(y) is nonzero. This is the additional hypothesis (3) of 0G4F, not a consequence merely of finite base locus. Apply the existing irreducible-member node separately on X and on T, then intersect its two nonempty opens in the same A(V). This gives the claimed simultaneous geometric irreducibility. If the X-member is smooth, the T-member is smooth because it is etale over it; finiteness and etaleness survive base change. Irreducibility gives connectedness of both. This task constructs no curve, imposes no smoothness condition at S by itself, and makes no descent claim.

### Arguments retained directly in the item

The finite intersection choice is the end of old step 3. Explicit dimension induction is all of old step 4 not allocated above. Existing finite-field-descent remains old step 5 with its precise model and automorphism. Thus none of the previous work was discarded or replaced by an unproved assertion hidden in the assembly.

## Former proof, verbatim for continuity

Old step 1 (uses: lem-zl-bertini-sections, lem-pc-serre-vanishing):

Use the sections-vanishing Bertini input [lem-zl-bertini-sections] (Stacks Tag 0FD5) on a projective closure $\overline X$ of $X$ and the reduced finite closed subscheme supported on $S$. For a sufficiently large $n$, its space $V$ of sections of $\mathcal O_{\overline X}(n)$ vanishing on $S$ generates the twist away from $S$ and induces an immersion on $X\setminus S$. Apply [lem-pc-serre-vanishing] to the ideal of the union of the first infinitesimal neighborhoods of the points of $S$; after increasing $n$, restriction to the direct sum of the cotangent spaces at $S$ is surjective. Thus the conditions that a section have nonzero first derivative at every point of $S$ are nonempty open conditions on $V$.

Old step 2 (uses: lem-zl-bertini-smooth-member, lem-weil-pbc-geometric-regularity-smooth-field-criterion, lem-weil-pbc-regular-local-hypersurface-criterion, lem-weil-pbc-regular-closed-point-smooth-source):

Let $s\in S$ and let $v\in V$ have nonzero image in $(\mathfrak m_s/\mathfrak m_s^2)\otimes\mathcal O_{\overline X}(n)|_s$ (Step 1). Since $X$ is smooth over $k$, $\mathcal O_{X,s}$ is a regular local ring [lem-weil-pbc-geometric-regularity-smooth-field-criterion] (with $L=k$). In a trivialization of $\mathcal O(n)$ at $s$, $v$ is an element $f\in\mathfrak m_s\setminus\mathfrak m_s^2$, so $\mathcal O_{X,s}/(f)=\mathcal O_{H_v,s}$ is regular [lem-weil-pbc-regular-local-hypersurface-criterion], and $H_v\cap X$ is smooth over $k$ at the closed point $s$ [lem-weil-pbc-regular-closed-point-smooth-source] ($k$ algebraically closed, applied on an affine open of $H_v\cap X$ containing $s$). The restriction $\psi:V\to\Gamma(X\setminus S,\mathcal O(n))$ generates and gives an immersion $X\setminus S\to\overline X\setminus S\to\mathbf P(V)$ (an open immersion followed by an immersion), and $X\setminus S$ is smooth, so [lem-zl-bertini-smooth-member] gives a nonempty open $U_{\rm sm}\subseteq\mathbf A(V)$ whose $k$-points cut $X\setminus S$ smoothly. Intersecting with the finitely many nonempty open derivative conditions of Step 1 gives a nonempty open whose $k$-points $v$ have $H_v\cap X$ smooth over $k$ everywhere. For such $v$, $T\times_X(H_v\cap X)$ is étale over $H_v\cap X$ (base change of $T\to X$), hence smooth over $k$; no Bertini theorem is applied to $T$ for smoothness.

Old step 3 (uses: lem-zl-bertini-irreducible-member, lem-sc-rational-unramified-cotangent-criterion, lem-weil-pbc-geometric-regularity-smooth-field-criterion, lem-weil-pbc-regular-local-hypersurface-criterion, lem-sc-regular-local-domain, lem-weil-pbc-noetherian-height-quotient-bound):

Both $X$ and $T$ are smooth and connected over the algebraically closed field $k$, hence irreducible and so geometrically irreducible; $T$ has dimension $d$ since it is finite étale over $X$. Base loci: the base locus of $V$ on $X$ is $S$ (all sections vanish on $S$, and $V$ generates off $S$), and that of the pulled-back system on $T$ is the finite inverse image of $S$; finite sets of closed points have codimension $d\ge2$. Hypothesis (i) of [lem-zl-bertini-irreducible-member] on $Y\in\{X,T\}$: choose a closed point $y\in Y$ over some $x\in X\setminus S$. The morphism $Y\setminus(\text{inverse image of }S)\to\mathbf P(V)$ is unramified at $y$ (an immersion, or an étale morphism followed by an immersion), so by [lem-sc-rational-unramified-cotangent-criterion] the cotangent space of $\mathbf P(V)$ at the image point surjects onto $\mathfrak m_y/\mathfrak m_y^2$; as the former is spanned by ratios of sections of $V$ vanishing at that point, and $\dim\mathfrak m_y/\mathfrak m_y^2=d\ge2$ ($\mathcal O_{Y,y}$ is regular of dimension $d$ [lem-weil-pbc-geometric-regularity-smooth-field-criterion]), there are $v_2,v_3\in V$ vanishing at $y$ with independent images in $\mathfrak m_y/\mathfrak m_y^2$, and by generation some $v_1$ with $v_1(y)\neq0$. With $R=\mathcal O_{Y,y}$ and $f_2,f_3$ local equations, $R/(f_2)$ and $R/(f_2,f_3)$ are regular [lem-weil-pbc-regular-local-hypersurface-criterion] (the image of $f_3$ lies outside the square of the maximal ideal of $R/(f_2)$ by independence), hence domains [lem-sc-regular-local-domain]. So $\mathfrak p=(f_2,f_3)$ is prime, exactly one irreducible component $W$ of $H_{v_2}\cap H_{v_3}$ passes through $y$, and $\operatorname{codim}(W,Y)=\operatorname{ht}\mathfrak p$. Now $0\subsetneq(f_2)\subsetneq\mathfrak p$ is a chain of primes ($f_2\neq0$, and $f_3\notin(f_2)$ by independence), so $\operatorname{ht}\mathfrak p\ge2$, and $\operatorname{ht}\mathfrak p\le0+2$ by [lem-weil-pbc-noetherian-height-quotient-bound]. Thus $\operatorname{codim}(W,Y)=2$ and $W\not\subseteq H_{v_1}$ as $y\in W$. Hence [lem-zl-bertini-irreducible-member] gives nonempty opens of $\mathbf A(V)$ for $X$ and for $T$. Intersect them with the open of Step 2 (in the irreducible $\mathbf A(V)$) and choose a $k$-point $v$ ($k$ is infinite). Then $H_v\cap X$ and $H_v\cap T=T\times_X(H_v\cap X)$ are smooth and geometrically irreducible, in particular connected.

Old step 4 (uses: lem-zl-bertini-smooth-member, lem-zl-bertini-irreducible-member, def-weil-scheme-morphism-properties):

The resulting closed subscheme $X_1\subset X$ contains $S$, is affine because it is closed in the affine scheme $X$, is smooth and connected, and has dimension $d-1$; its inverse image $T_1=T\times_X X_1$ is connected, finite, and etale over $X_1$. Repeat the same construction with $X_1,T_1$ and the same finite set $S$ until dimension one. At every stage the dimension is at least two when Bertini is applied, so the codimension-two base-locus hypothesis remains valid; the final $X_r$ is the required curve $C$, and connectedness of $T_r$ is the connectedness of $T\times_X C$.

Old step 5 (uses: lem-zl-bertini-finite-field-descent):

The final curve $C=X_r$ is a closed subscheme of $X=X_0\times_{k_0}k$ with $X_0$ of finite type over $k_0$ (smooth). By [lem-zl-bertini-finite-field-descent] applied to the closed immersion $i:C\hookrightarrow X$, there are $m\ge1$ and a closed subscheme $C_m\subseteq X_0\times_{k_0}\mathbf F_{q^m}$ with $C=C_m\times_{\mathbf F_{q^m}}k$, and an automorphism $\varphi:C\to C$ with $i\circ\varphi=(\mathrm{id}_{X_0}\times\sigma)^m\circ i$, where $\mathrm{id}_{X_0}\times\sigma=g_X$ is the geometric Frobenius of $X$. This is the displayed Frobenius stability; smoothness, connectedness and affineness of $C$ and connectedness of $T\times_XC$ were proved over $k$ in Step 4.

## Not duplicates

lem-zl-bertini-prescribed-point-smooth-system vs lem-zl-bertini-singular-locus-dimension: the existing statement is "Dimension bound for the singular locus in a Bertini family"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-zl-bertini-singular-first-order-model: the existing statement is "First-order linear kernel containing a Bertini singular fibre"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-zl-bertini-singular-fibre-equations: the existing statement is "First-order equations on the singular fibre"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-zl-bertini-singular-affine-fibre-charts: the existing statement is "Complementary base and fibre dimensions on Bertini charts"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs def-zl-bertini-universal-family: the existing statement is "Universal Bertini family and reduced singular scheme"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-zl-bertini-sections: 0FD5 gives generation and immersion off a closed subscheme; it gives neither first-order surjectivity nor smoothness at prescribed base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-zl-immersion-near-image-locality: the existing statement is "Checking immersion on target opens covering the image"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-zl-bertini-finite-cover-curve: the existing item constructs a final curve with finite-field descent; this helper concerns only a prescribed-point system and one smooth hypersurface, without covers.

lem-zl-bertini-prescribed-point-smooth-system vs lem-zl-bertini-singular-fibre-kernel: the existing statement is "The singular fibre embeds in the linear kernel"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-zl-symmetric-algebra-kernel-factor: the existing statement is "Coordinate quotients factor through the dual kernel"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-zl-immersion-cancellation: the existing statement is "An immersion cancels from a composite"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-zl-bertini-smooth-member: 0FD6 assumes generation everywhere and an immersion; the new system has base points S and must construct jets and smoothness at those base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-zl-irreducible-fibre-dimension-lower-bound: the existing statement is "Lower bound for fibres of an irreducible finite-type scheme"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-zl-hypersurface-nonzero-relative-differential: the existing statement is "Nonzero relative differential gives a smooth hypersurface point"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-zl-bertini-product-system-immersion: the existing statement is "A linear system containing ideal products is immersive"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-pc-q3-affine-open-twist-vanishing-independent: the existing statement is "Affine-open twist vanishing independent of proper coherence"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-pc-c2-closed-immersion-fixed-degree-vanishing: the existing statement is "Fixed-degree vanishing for a closed projective subscheme"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-pc-e4-affine-restricted-twist-fixed-degree: the existing statement is "Fixed-degree affine-local twist cohomology vanishing"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-weil-pbc-closed-immersion-serre-vanishing: the existing statement is "Serre vanishing for restricted projective-space twists over a Noetherian ring"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-weil-pbc-coherent-serre-vanishing: the existing statement is "Serre vanishing for a proper morphism"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-weil-pbc-ample-very-ample-immersion-affine-base: the existing statement is "An ample invertible module over an affine base: a power is the pullback of O(1) along an immersion into projective space"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-prescribed-point-smooth-system vs lem-weil-pbc-formal-systems-graded-vanishing: the existing statement is "Serre vanishing for a finite graded module on a proper scheme"; it does not assert construction of high-degree sections vanishing on a prescribed finite set, simultaneous cotangent surjectivity, and a smooth-member open including the base points.

lem-zl-bertini-finite-cover-irreducible-system vs lem-ag-cartier-reduced: the existing statement is "Cartier: group schemes in characteristic zero are smooth and reduced"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-sbc-regular-codimension-two-etale-extension: the existing statement is "Finite etale extension across a regular codimension-two boundary"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-sbc-strict-hensel-regular-divisor-quotient-noetherian: the existing statement is "Noetherianity of canonical strict henselization"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-sbc-depth-two-punctured-principal-slice-connected: the existing statement is "Connected depth-two puncture with nonempty principal slice"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-sbc-strict-hensel-regular-divisor-quotient: the existing statement is "Noetherian canonical strict henselization and regular divisor quotient"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-sbc-root-normalization-generic-stalk-flat: the existing statement is "Flat normalization stalks at the generic root divisor"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-sbc-strict-hensel-regular-divisor-quotient-regular: the existing statement is "Regular domain divisor quotient of canonical strict henselization"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-sbc-regular-cartier-generic-stalk-dvr: the existing statement is "The generic ambient stalk of a regular integral Cartier divisor is a DVR"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-sbc-strict-hensel-regular-divisor-quotient-domain-part: the existing statement is "Domain property of strict henselization divisor quotient"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs thm-trf-frobenius-fixed-points: the existing statement is "Scheme-theoretic Frobenius fixed points"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-finite-algebraic-closure: the existing statement is "Algebraic closure in a finitely generated field extension is finite"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-finite-intermediate-fields: the existing statement is "Finitely many intermediate fields in a finite separable extension"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-finite-separable-closure: the existing statement is "Finite separable algebraic subextension of a finitely generated field extension"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-bertini-affine-incidence-chart: the existing statement is "The affine polynomial quotient chart of universal incidence"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-bertini-field-extension: the existing statement is "Algebraic Bertini lemma for a generic linear combination"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-geometric-irreducibility-add-transcendental: the existing statement is "Adding a transcendental variable preserves geometric irreducibility"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-spectrum-irreducible-nilradical-prime: the existing statement is "Irreducibility of an affine spectrum is equivalent to primality of the nilradical"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-bertini-affine-ambient: the existing statement is "Affine space commutes with change of coefficient ring"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-geometric-irreducibility-subextension: the existing statement is "Geometric irreducibility passes to subextensions"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-bertini-universal-generic-fibre: the existing statement is "Geometric irreducibility of the universal Bertini generic fibre"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-independence-algebraic-base: the existing statement is "Algebraic independence is unchanged by an algebraic base extension"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-bertini-universal-zero-section: the existing statement is "The zero-coefficient section of universal incidence"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-bertini-finite-cover-curve: the existing item constructs a final curve with finite-field descent; this helper concerns only one fixed linear system and simultaneous irreducibility on a cover, without iteration or descent.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-bertini-affine-function-field: the existing statement is "Geometric irreducibility of the affine Bertini function field"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-sepclosed-algebras-tensor-irreducible: the existing statement is "Tensor products of irreducible algebras over a separably closed field"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-generic-point-geometric-irreducibility: the existing statement is "Geometric irreducibility detected by the generic residue field"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-bertini-polynomial-residue-arrow: the existing statement is "The generic residue-field arrow of the eliminated polynomial projection"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-bertini-independent-functions: the existing statement is "Codimension-two intersection supplies independent generic linear combinations"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-geometric-irreducibility-finite-separable-test: the existing statement is "Geometric irreducibility can be tested on finite separable extensions"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-rational-function-degree: the existing statement is "A finite field extension preserves degree after adjoining one indeterminate"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-bertini-trivialized-zero-ideal: the existing statement is "The local equation of a trivialized incidence zero ideal"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-bertini-incidence-adapted-chart: the existing statement is "A dense adapted polynomial chart of the Bertini incidence scheme"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-bertini-incidence-elimination: the existing statement is "Elimination of a unit incidence coefficient"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-geometric-irreducibility-transcendental: the existing statement is "Geometric irreducibility and purely transcendental extensions"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-geometric-irreducibility-subalgebra-colimit: the existing statement is "Geometric irreducibility is preserved by subalgebras and directed colimits"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-irreducible-dominant-generic-fibre: the existing statement is "Irreducibility of the generic fibre of a dominant map"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-fibre-residue-arrow: the existing statement is "Residue fields of points in scheme fibres"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-bertini-irreducible-member: 0G4F assumes the codimension-two witness and geometric irreducibility; this helper must derive those hypotheses from smooth connectedness and the immersive/etale systems, on X and T simultaneously.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-bertini-incidence-naturality: the existing statement is "Universal incidence commutes with changing the base scheme"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-geometric-irreducibility-affine-local: the existing statement is "Affine-local criterion for geometric irreducibility on an irreducible scheme"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-linear-incidence-irreducible: the existing statement is "Irreducibility of an affine linear incidence hypersurface"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-bertini-basis-coordinates: the existing statement is "A basis change preserves the universal incidence equation"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-bertini-generic-fibre-chart: the existing statement is "Affine function-field presentation of the Bertini incidence scheme"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-geometric-irreducibility-separable: the existing statement is "Separable elements in a geometrically irreducible extension"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-bertini-affine-incidence-irreducible: the existing statement is "Irreducibility of trivialized affine incidence charts"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-zl-finite-type-fibre-component-lower-bound: the existing statement is "Dimension lower bound for each rational closed-fibre component of a finite type algebra map"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-trf-strict-semistable-model-normal: the existing statement is "Normality of a strictly semistable model with smooth generic fibre"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-trf-polynomial-algebra-cm: the existing statement is "Polynomial algebras over Noetherian Cohen–Macaulay rings are Cohen–Macaulay"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-trf-stacks-nodal-closed-subcurve: the existing statement is "Stacks lemma for a reduced closed subcurve of a nodal curve"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-trf-completion-local-complete-intersection: the existing statement is "Complete-intersection neighbourhoods detected by the completed local ring"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-trf-log-regular-saturation-normality: the existing statement is "Normality of complete saturated monoid local models"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-trf-smooth-separable-hypersurface-slice: the existing statement is "One smooth hypersurface slice at a separable closed fibre point"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-trf-etale-component-coordinate-identification: the existing statement is "Étale local identification of regular boundary components with coordinate hyperplanes"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-trf-dnc-principal-generic-smooth-reduction: the existing statement is "Generic smooth coordinate reduction for a principal divisor"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-trf-nc-coordinate-max-stratum: the existing statement is "Coordinate description of the maximal branch stratum"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-trf-snc-divisorial-log-chart: the existing statement is "Divisorial charts of a smooth strict normal crossings pair"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-trf-normalization-principal-height-one-refinement: the existing statement is "A prime over a principal ideal in a local normalization contains a height-one prime over it"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-trf-regular-local-surjection-kernel-comparison: the existing statement is "Regular-sequence kernels along a surjection of regular local rings"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-trf-formal-monoid-ring-dimension: the existing statement is "Dimension of a formal monoid ring and a parameter hypersurface"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-trf-integers-excellent: the existing statement is "The ring of integers is excellent"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-trf-chart-coordinate-nonzerodivisors: the existing statement is "The chart generator remains regular after a coordinate quotient"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-trf-regular-ring-universally-catenary: the existing statement is "Noetherian regular rings are universally catenary"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-trf-regular-local-ufd-boundary-factorization: the existing statement is "Boundary-unit factorization in a regular local ring"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-sc-regular-local-domain: the existing statement is "Regular local rings are domains"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-sc-effective-cartier-affine-dimension-drop: the existing statement is "Dimension drop for a principal Cartier subscheme of an affine variety"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-sc-finite-flat-unramified-tangent-criterion: the existing statement is "Tangent criterion for etaleness of a finite locally free morphism"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-per-complete-local-branch-approximation: the existing statement is "Two compatible trait approximations of a complete local pair"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-per-regular-gysin-calculus: the existing statement is "Gysin purity calculus on regular affine schemes"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-per-marked-finite-diagram-approximation: the existing statement is "Regularity and boundary intersections persist under sufficiently fine marked approximation"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-per-regular-boundary-divisorial-chart: the existing statement is "Divisorial charts of a regular strict normal crossings pair"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-per-complete-local-excellence: the existing statement is "Complete Noetherian local rings are excellent"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-per-parameter-ideal-formal-normalization: the existing statement is "Finite formal normalization for supplied parameter ideals"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-per-primitive-monomial-trait-geometry: the existing statement is "Geometry of a monomial trait model with a generically invertible exponent"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-per-snc-boundary-parameter-criterion: the existing statement is "Local parameter criterion for a strict normal crossings boundary"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-per-noetherian-local-colimit-regular: the existing statement is "Noetherian directed colimits of regular local rings are regular local"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-per-regular-lci-geometric-calculus: the existing statement is "Regular-immersion geometry and intrinsic virtual dimension"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-per-partial-parameters-quotient-dimension: the existing statement is "Quotients by initial parts of a system of parameters have the expected dimension"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-per-noetherian-local-domain-open-infinite: the existing statement is "Nonempty opens in a high-dimensional Noetherian local domain are infinite"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-per-complete-mixed-regular-pair-approximation: the existing statement is "Simultaneous regular-pair approximation over a complete Cohen trait"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-per-strict-local-divisor-low-kummer: the existing statement is "Low-degree Kummer cohomology of a strict-local regular divisor complement"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-per-catenary-completion-hyperplane: the existing statement is "Hyperplane reduction of a non-equidimensional completion"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-per-surface-point-blowup-geometry: the existing statement is "Regularity and projectivity of a point blowup on a regular surface"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-per-snc-root-algebra-structure: the existing statement is "Structure of the simultaneous parameter-root algebra over a strict local ring"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-hypersurface-derivation-regular: the existing statement is "Quotient of a regular ring by an element with a unit derivative is regular"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-cm-local-dimension-drop-regular-sequence: the existing statement is "In a Cohen-Macaulay local ring, elements cutting the dimension by their number form a regular sequence"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-popescu-resolve-separable: the existing statement is "Popescu's local problem is resolvable at a regular prime with separable residue field"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-cohen-rings-exist: the existing statement is "Cohen rings exist"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-polynomial-ring-maximal-chain-height-difference: the existing statement is "Maximal chains of primes in a polynomial ring over a field have length the difference of the heights"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-popescu-find-sequence: the existing statement is "Choosing generators of a regular prime with controlled annihilators (Ogoma)"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-regular-local-generators-regular-sequence: the existing statement is "A regular system of parameters is a regular sequence"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-cm-local-maximal-chain-length: the existing statement is "Maximal chains of primes in a Cohen–Macaulay local ring have length the dimension"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-regular-local-mcm-free: the existing statement is "A maximal Cohen–Macaulay module over a regular local ring is free"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-analytic-unramified-principal-criterion: the existing statement is "A principal-quotient criterion for an analytically unramified local domain"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-global-complete-intersection-local-regular-sequence: the existing statement is "The equations of a global complete intersection form a regular sequence at every prime"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-flat-over-regular-with-regular-fibre: the existing statement is "Flat local maps with regular source and fibre have regular target"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-complete-local-domain-finite-over-regular: the existing statement is "A Noetherian complete local domain is finite over a regular complete power series subring"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-regular-fiber-kernel-parameter-lift: the existing statement is "Lift regular closed-fibre kernel parameters preserving the base regular sequence"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-completion-of-dvr-is-dvr: the existing statement is "The completion of a discrete valuation ring is a discrete valuation ring"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-smooth-over-field-local-complete-intersection: the existing statement is "A smooth algebra over a field is a local complete intersection"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-geometrically-regular-over-field-flat: the existing statement is "Flatness over a localized polynomial ring whose variables give a basis of the differentials of a residue subfield"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-noetherian-height-quotient-bound: the existing statement is "Height drops by at most the number of equations (Krull)"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-complete-local-map-regular-presentation: the existing statement is "Compatible regular presentations of a map of complete local rings"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-regular-local-finite-gl-dim: the existing statement is "A regular local ring has finite global dimension"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-regular-local-hypersurface-criterion: the existing statement is "A non-square element cuts a regular local hypersurface"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-regular-sequence-dimension-at-point: the existing statement is "Dimension at a point cut out by a local regular sequence"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-global-complete-intersection-equidimensional: the existing statement is "A global complete intersection has the expected dimension at every point"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-complete-local-flat-presentation: the existing statement is "A local map of complete Noetherian local rings has a flat Cohen presentation"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-cm-local-quotient-nonzerodivisor-cm: the existing statement is "Quotient of a Cohen–Macaulay local ring by a nonzerodivisor is Cohen–Macaulay"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-polynomial-quotient-dimension-lower-bound: the existing statement is "Dimension lower bound for a polynomial quotient over a field"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-flat-over-regular: the existing statement is "A local map from a regular local ring sending a regular system of parameters to a regular sequence is flat"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-flat-polynomial-append-tensor-fibre: the existing statement is "Flatness of the polynomial-append tensor fibre"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-regular-local-finite-module-resolution: the existing statement is "Finite modules over a regular local ring have bounded projective resolutions"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-smooth-at-maximal-ideal-alg-closed-differentials-bound: the existing statement is "Over an algebraically closed field, few differentials at a closed point imply smoothness there"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-flat-polynomial-append-fibre-regular-sequence: the existing statement is "Appending closed-fibre regular coordinates preserves flatness"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-regular-ring-normal: the existing statement is "A regular ring is normal"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-fs-adic-lift-from-residue-field: the existing statement is "A formally smooth complete local algebra over the residue field lifts to a formally smooth complete local algebra"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-popescu-resolve-char-p: the existing statement is "Popescu's local problem is resolvable in characteristic p for geometrically regular Lambda"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-depth-le-dim-associated-prime: the existing statement is "The depth of a module is at most dim(R/p) for every associated prime p"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-dimension-quotient-nonzerodivisor: the existing statement is "Dimension drops by one modulo a nonzerodivisor of the maximal ideal"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-flat-regular-fibre-parameter-selection: the existing statement is "Select flat polynomial parameters in a regular closed fibre"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-lci-regular-sequence-global-complete-intersection: the existing statement is "If the ideal of a presentation is generated by a regular sequence at a prime, the algebra is a global complete intersection near that prime"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-weil-pbc-miracle-flatness: the existing statement is "Miracle flatness"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-pur-smooth-pair-regular-immersion: the existing statement is "Local regular equations for a closed immersion of smooth schemes"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-pur-smooth-pair-local-coordinates: the existing statement is "Local coordinates for a closed immersion of smooth schemes"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-exc-regular-map-reduced-target: the existing statement is "Reducedness ascends along a regular map of Noetherian rings"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-pur-etale-near-regular-coordinate-fibre: the existing statement is "Etaleness near a regular coordinate fibre"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-exc-fields-excellent: the existing statement is "Fields are excellent"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-exc-regular-local-lift-regular-sequence-quotient: the existing statement is "Regularity lifts from the quotient by a regular sequence"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-exc-regular-locus-open-from-prime-quotients: the existing statement is "Regular locus is open when every prime quotient has a regular open"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

lem-zl-bertini-finite-cover-irreducible-system vs lem-sc-tsen: the existing statement is "Tsen's theorem"; it does not assert simultaneous geometrically irreducible members on a connected finite etale cover from an immersive system with prescribed finite base locus.

