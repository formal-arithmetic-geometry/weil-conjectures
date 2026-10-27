## Worker report

1. Files written: the item `dag/nodes/sec-six-functors-basics/lem-sfb-snc-finite-root-regular-ring.json` (statement unchanged, split, no Mathlib match); `lem-sfb-snc-root-local-presentation.json` (statement-only, unsplit, no Mathlib match); `lem-sfb-transverse-local-root-family-regular.json` (statement-only, unsplit, no Mathlib match), both in the same directory; and sandbox `citations.json`. Two new nodes, zero Mathlib leaves.
2. Attachments: none. The blueprint tag and concept searches in `lean/WeilConjectures/` do not give a completed theorem for this item. `AlgebraicGeometry.isRegularRing_snc_finiteRoot` in `lean/Sheaf/AlgebraicGeometry/SNCFiniteRootRegularRing.lean:84` has `sorry` and is not an attachment. The existing one-root theorem is already represented by `lem-sbc-root-algebra-regular-at-root` and is not the full simultaneous theorem.
3. WANTED: none.
4. This repairs the returned long-proof split. The sandbox initially contained only dispatcher brief markers, without node files, report or searches. I copied the current live item; its seven steps have the exact returned lengths (625, 722, 829, 635, 711, 926, 799). No earlier sandbox proof was discarded. The prior Q08 report is retained below. The item's statement, Lean record, source, inherited metadata and prior Mathlib searches are unchanged. The new local-data node takes old steps 1, 2 and 7 (2146 characters); the algebraic-family node takes old steps 3--6 (3101 characters). These are separate geometric and commutative-algebra arguments, with comparable workloads; neither merely restates a clause of the item. The item now has a 1252-character assembly. Both new nodes have empty proof/proof_deps, null proof_origin, and status unsplit, so other workers can split them independently. Every old argument is preserved verbatim below and allocated explicitly.
5. The one-level repair is complete; proofs of the two new nodes are future work, as required by the return. No Lean source was written and no Lean compiler, Lake, build or local DAG-check script was run. Only the named sandbox was written; server checks and packaging use the authorized delivery tools.

## Sources and searches

For the item and both new nodes I read ILO, Expose IX Proposition 2.1, printed pp.133--134 (PDF pages 139--140), especially the displayed full simultaneous root algebra before invariants. The source leaves this elementary-algebraic regularity calculation implicit; the retained argument is explicitly agent-written. No SGA source or theorem is used. The reference to Abhyankar on the following page is not part of this split.

For the local-data node I read Stacks `etale.tex`, Tag 0BIA (`lemma-strict-normal-crossings`), its regular-intersection criterion and parameter proof, and `algebra.tex`, Tag 00CT (`proposition-localize-quotient`). The affine stalk and finite-type Noetherian steps reuse the actual statements of `lem-weil-pbc-affine-open-stalk-localization`, `pqf-lem-affine-open-locnoeth` and `lem-weil-pbc-finite-type-algebra-noetherian`. The SNC definition already contains the precise dimension equality, so this is not an attempt to infer that equality from bare regularity of intersections.

For the local-family node I read Stacks `algebra.tex`, Tag 00NP (`lemma-regular-domain`), Tag 00NU (`lemma-regular-mod-x`), and `more-algebra.tex`, Tag 07PF (`lemma-quotient-regular`). I opened every existing node cited in the retained induction. The root-at-root statement assumes a Noetherian coefficient ring, injectivity of the branch equation, a regular quotient, and a positive exponent; it does not require the coefficient algebra to be a domain or local. Its complementary locus is handled by the unit derivative, not by an unsupported regularity-descent assertion.

All fresh Mathlib searches ran through the required `msearch.py Q64 lem-sfb-snc-finite-root-regular-ring` command and are copied exactly from its `searches.jsonl` log into the appropriate new node. Each node has two LeanFinder phrasings, Loogle and grep searches, and an attempted LeanSearch. Both LeanSearch attempts were unavailable because of the service rate limit; their verdicts are unavailable. The first local-data Loogle pattern was rejected for unknown `Ideal.Quotient`; it is recorded as unavailable and was replaced with the valid `IsRegularLocalRing, "quotient"` query, which returned zero hits. The returned Krull-dimension lemmas concern regular sequences already given, and the smooth/standard-etale results do not state the geometric local-data result. For the local-family node the grep hits `MvPolynomial.isRegularRing_of_isRegularRing`, `Mathlib/RingTheory/RegularLocalRing/Polynomial.lean:108`, only prove polynomial ambient regularity; I read lines 108--114. The other phrasing returns standard-etale presentations, which omit the ramified primes. Kummer grep hits are number-theoretic. Thus neither new node is a one-line Mathlib specialization. The item's earlier searches and their results remain intact.

I searched the whole DAG for `0BIA`, `07PF`, `00NU`, root/regular words, partial-root and intersection-quotient language, the proposed ids, and related existing statements; I searched the entire imported blueprint with `tools/blueprint_refs.py search` for `root regular`, `normal crossings`, `parameter root`, `regular local` and each of those tags. None states either new result. I also read the neighbouring SNC root-structure, parameter-criterion, face-regularity and divisor-root-model statements. The blueprint ancestor command returns null. I retained the inherited explicit paragraph-(3) open-direct-image place and via chain; the new nodes prepend this item to via and identify the part of the same finite-root argument they carry. The chapter and unit records were read and unchanged.

## Review by Q64

I checked every part of the return: two new independent, statement-only unsplit nodes were added; the item statement is unchanged; the old proof is not discarded or blurred; the old work is assigned 2146/3101 characters to the two workers; the parent assembly is below 3000 characters. The original sources, citations and search results survive in the node and in the retained material below. This is a substantive re-split, not a rebase of unchanged content.

In new step 1, `lem-sfb-snc-root-local-presentation` explicitly supplies both Noetherian conclusions, every local quotient R_J and its exact dimension equation, and both localization isomorphisms. Its assumptions are precisely the affine regular scheme, the distinct reduced branch equations as closed subschemes, a finite boundary and a positive root exponent, all present in the item. The node does not presuppose regularity of C. This avoids taking a conclusion from the proof of another node or using a definition for a theorem it does not state.

In new step 2, `lem-sfb-transverse-local-root-family-regular` actually says every B_{J,K} is regular and Noetherian under the dimension-and-regularity data supplied in step 1. I checked the quantifiers: simultaneous over every J contained in S, then every K disjoint from J, not merely quotients for J empty. This is exactly what allows the original induction to enlarge J after killing a coordinate. The positive n is the same n, and its inverse maps from A into A_p, then into each quotient. The set S computed in A_p is the original set because t/1 lies in pA_p exactly when t lies in p. Specializing J empty and K all indices produces the required local root presentation. The new statement permits unit t_i, arbitrary finite I, and requires no henselian or roots-of-unity hypotheses.

In new step 3, the regular-ring definition supplies regular local prime localizations of the ring from step 2. The local-data node explicitly identifies that prime localization with (C_n)_q. The concluding assembly is elementary with these cited conclusions: arbitrary q plus the already established global Noetherianity is precisely regularity. It does not infer global Noetherianity from stalks. `citations.json` contains a verbatim full-statement quote for each of the four step/node citations.

For the work moved to the local-data node I checked the old step-1 affine hypotheses, all old step-2 intersections and the old step-7 maps. For J contained in S the point p is actually on every branch in J, so the quotient is nonzero regular local and the stated dimension is meaningful. The maps identifying the local root presentation fix all coefficients as fractions and all root coordinates. The further prime-localization maps invert exactly the elements outside q. Both directions were explicitly present and are retained below. No regular-root conclusion is used to establish this geometric node.

For the work moved to the local-family node I checked old steps 3--6 against all their cited statements. Iterated monic freeness gives injective multiplication by each nonzero coefficient on the partial root algebra without asserting that algebra is a domain. At a prime containing the new root, the branch lies in S; two adjacent dimension equalities force it nonzero in R_J. Regular-local-domain then gives injectivity on coefficients. Reduction of the monic presentations gives D/(t_i)=B_{J union {i},K minus {i}} by the displayed generator maps, and the simultaneous induction supplies a regular quotient. Thus all hypotheses of the root-at-root node hold. Off the root, t_i is invertible at the prime, D[1/t_i] is regular, its polynomial ring is regular, and the derivative nT^(n-1) has the written inverse factors. The 07PF criterion applies to this polynomial ring; explicit fraction maps identify the resulting local ring with B_Q. There is no circular appeal to the parent, a face-regularity node, or a strictly henselian SNC theorem.

Small cases: A=0 gives C=0 and no primes in the local-data node; r=0 gives A and the empty-root family base. In the local-family node R is a genuine nonzero regular local ring, and every R_J is nonzero by hypothesis. K empty gives R_J with basis {1}; n=1 eliminates each root variable. If R is a field then S is empty: only unit roots occur and the unit-derivative argument applies, even when the root algebra splits and is not local. The examples R=k[s]_(s), t=s and R=k[s,u]_(s,u), t=(s,u) satisfy the transverse dimension hypotheses. A family with one unit and one parameter exercises both prime cases. Repeated equations t_1=t_2=s fail the dimension condition for J={1,2} and may give a singular x_1^n=x_2^n; the item excludes them. No invertibility assumption is lost at a quotient or localization.

I checked delivery-errors B--E: new statements introduce every object and cite their defining notions, contain no proof sketch, and are not elementary repackagings. There is no claim that a sorry declaration is complete, no new Mathlib leaf on a partial hit, no unstated off-unit tool in the parent, no new cycle and no clause moved verbatim into a renamed node. The geometric result concludes structural local data, not regularity of a root ring; the algebra result assumes that data and handles arbitrary local partial-root families, with a different proof task. They divide, rather than reproduce, the original theorem. All three parent steps are below 2000 characters, and the complete arguments removed from them are preserved below for the two future workers. No statement dispute was found and no route was changed.

## Retained arguments and allocation to new nodes

The following is the previous seven-step proof, verbatim, with its sources and dependency lists. This is report material for the next workers, not proof content inside either statement-only node. Steps 1, 2 and 7 belong to `lem-sfb-snc-root-local-presentation`; steps 3--6 belong to `lem-sfb-transverse-local-root-family-regular`. The old step 7's final use of regularity is the parent assembly; its nontrivial localization argument belongs to the local-data node.

### Former step 1: local-data node

The regular scheme $X$ is locally Noetherian by [def-weil-regular-scheme], so its affine coordinate ring $A$ is Noetherian by [pqf-lem-affine-open-locnoeth]. The displayed finite polynomial presentation of $C_n$ then makes $C_n$ Noetherian by [lem-weil-pbc-finite-type-algebra-noetherian]. If $A=0$, this quotient is zero and has no prime ideals. Otherwise fix an arbitrary prime $q\subset C_n$, let $p=q\cap A$, and put $R=A_p=\mathcal O_{X,p}$ using [lem-weil-pbc-affine-open-stalk-localization]. It suffices to show that the localization of the same root presentation over $R$ at the prime induced by $q$ is regular local.

Uses: def-weil-regular-scheme, pqf-lem-affine-open-locnoeth, lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-affine-open-stalk-localization.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; Expose IX Proposition 2.1 proof, printed p.133: full parameter-root algebra before invariants; the induction below supplies the regularity argument left implicit there.

### Former step 2: local-data node

Write $I=\{1,\ldots,r\}$, $S=\{i\in I:t_i\in p\}$ and $d=\dim R$. For $J\subseteq S$ put $R_J=R/(t_j:j\in J)$. The intersection of the branches indexed by $J$ is the affine closed subscheme $\operatorname{Spec}(A/(t_j:j\in J))$ and contains $p$. By [def-trf-strict-normal-crossings-boundary] its local ring there is regular local, and its dimension plus $|J|$ is $d$. The quotient-localization isomorphism [lem-weil-pbc-localization-at-prime-of-quotient], together with [lem-weil-pbc-affine-open-stalk-localization], identifies this local ring with $R_J$, preserving the images of the $t_i$. Thus each $R_J$ is regular local with $\dim R_J+|J|=d$. If $i\notin S$, $t_i$ is already a unit in $R$, hence also in every $R_J$.

Uses: def-trf-strict-normal-crossings-boundary, lem-weil-pbc-localization-at-prime-of-quotient, lem-weil-pbc-affine-open-stalk-localization.

Source: literature/stacks-project/etale.tex; Tag 0BIA (lemma-strict-normal-crossings), regular-intersection criterion and its proof; the required dimension equality is explicitly included in the boundary definition used here.

### Former step 3: local-family node

For disjoint $J\subseteq S$ and $K\subseteq I\setminus J$, set $B_{J,K}=R_J[x_i:i\in K]/(x_i^n-t_i:i\in K)$. Iterating [lem-weil-pbc-monic-quotient-free] gives a finite free $R_J$-basis $\prod_{i\in K}x_i^{a_i}$, $0\leq a_i<n$. The presentation can be iterated in any order: the maps in both directions fix constants and send each root coordinate to the coordinate with the same index; their composites fix all algebra generators. In particular all these rings are Noetherian by [lem-weil-pbc-finite-type-algebra-noetherian]. We prove simultaneously for all $J$ that $B_{J,K}$ is regular, by induction on $|K|$. For $K=\varnothing$ it is $R_J$, which is a regular ring by [lem-weil-pbc-regular-local-localization]. This formulation allows the induction hypothesis to be applied with $J$ enlarged when a root coordinate is killed.

Uses: lem-weil-pbc-monic-quotient-free, lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-regular-local-localization.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; Expose IX Proposition 2.1 proof, printed p.133: full parameter-root algebra before invariants; the induction below supplies the regularity argument left implicit there.

### Former step 4: local-family node

For the induction step choose $i\in K$, put $K'=K\setminus\{i\}$ and $D=B_{J,K'}$. The induction hypothesis makes $D$ regular. Set $B=D[T]/(T^n-t_i)$ and write $u$ for the class of $T$; this is $B_{J,K}$. Fix a prime $Q\subset B$ containing $u$. The relation $u^n=t_i$ implies that $i\in S$, since otherwise $t_i$, and hence $u$, would be a unit. In $R_J$, $t_i\ne0$: otherwise $R_{J\cup\{i\}}=R_J$, contradicting the two dimension equalities from step 2. Since $R_J$ is a domain by [lem-sc-regular-local-domain], multiplication by $t_i$ is injective on $R_J$ and therefore on $D$, coordinate by coordinate in the free basis of step 3.

Uses: lem-sc-regular-local-domain.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; Expose IX Proposition 2.1 proof, printed p.133: full parameter-root algebra before invariants; the induction below supplies the regularity argument left implicit there.

### Former step 5: local-family node

Reduction of the monic presentations modulo $t_i$ identifies $D/(t_i)$ with $B_{J\cup\{i\},K'}$, using [lem-weil-pbc-monic-quotient-free]. Explicitly the map sends each coefficient in $R_J$ to its class in $R_{J\cup\{i\}}$ and fixes the root coordinates; the inverse sends these classes and roots to their classes in $D/(t_i)$. The relations in both presentations are the same, so both composites fix their generators. This ring is regular by the induction hypothesis with $|K'|<|K|$. Now $D$ is Noetherian, multiplication by $t_i$ on $D$ is injective, $n>0$, and $Q$ contains the root. Thus [lem-sbc-root-algebra-regular-at-root] applies with base $D$ and equation $t_i$, and gives that $B_Q$ is regular local.

Uses: lem-weil-pbc-monic-quotient-free, lem-sbc-root-algebra-regular-at-root.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; Expose IX Proposition 2.1 proof, printed p.133: full parameter-root algebra before invariants; the induction below supplies the regularity argument left implicit there.

### Former step 6: local-family node

It remains to treat a prime $Q\subset B$ not containing $u$. Then $t_i=u^n\notin Q$. Put $E=D[1/t_i]$, a regular ring by [lem-weil-pbc-localization-of-regular-ring]; its polynomial ring $E[T]$ is regular by [lem-trf-polynomial-ring-regular-base]. The derivative of $F=T^n-t_i$ is $nT^{n-1}$. In $E[T]/(F)$ the coordinate $T$ is a unit, with inverse $T^{n-1}/t_i$, and $n$ is a unit as the image of the given unit of $A$. Therefore the derivative has unit image. Apply [lem-weil-pbc-hypersurface-derivation-regular] to the derivation $\partial/\partial T$ to obtain regularity of $E[T]/(F)$. The prime $Q$ extends to this ring, since it misses $t_i$; its prime localization is $B_Q$. Indeed each newly inverted $t_i$ is already a unit in $B_Q$, so the maps in both directions are the maps on fractions fixing $D$ and $u$. Hence $B_Q$ is regular local. Together with step 5 this proves the induction step for every prime of $B$.

Uses: lem-weil-pbc-localization-of-regular-ring, lem-trf-polynomial-ring-regular-base, lem-weil-pbc-hypersurface-derivation-regular.

Source: literature/stacks-project/more-algebra.tex; Tag 07PF (lemma-quotient-regular), applied to the ordinary polynomial derivative after inverting the branch equation.

### Former step 7: local-data node

Apply the completed induction with $J=\varnothing$ and $K=I$. This proves regularity of $R[x_1,\ldots,x_r]/(x_i^n-t_i)$. This ring is $(A\setminus p)^{-1}C_n$: the isomorphism sends $a/s$ to the localized coefficient $a/s$ and each $x_i$ to its localized class; the inverse evaluates polynomials in those fractions, and the defining relations vanish in both directions. As $A\setminus p$ maps outside $q$, localizing further at the prime induced by $q$ gives exactly $(C_n)_q$ (the two maps on fractions fix $C_n$ and invert all its elements outside $q$). Thus every prime localization of the Noetherian ring $C_n$ is regular local, which is regularity as defined in [def-weil-regular-scheme]. For $r=0$ the empty presentation is $A$, and the induction is its base case; $n=1$ is allowed throughout.

Uses: def-weil-regular-scheme.

Source: literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf; Expose IX Proposition 2.1 proof, printed p.133: full parameter-root algebra before invariants; the induction below supplies the regularity argument left implicit there.

## Not duplicates

lem-sfb-snc-root-local-presentation vs lem-trf-nodal-pair-projective-resolution: the existing statement concerns resolution of a nodal curve over a smooth normal-crossings pair; it does not give the affine SNC intersection-quotient data together with coefficient and prime localization identifications for the simultaneous root presentation.

lem-sfb-snc-root-local-presentation vs lem-trf-snc-divisorial-log-chart: the existing statement concerns divisorial charts of a smooth strict normal crossings pair; it does not give the affine SNC intersection-quotient data together with coefficient and prime localization identifications for the simultaneous root presentation.

lem-sfb-snc-root-local-presentation vs lem-sfb-root-coordinate-supported-vanishing: the existing statement concerns one-coordinate supported vanishing on the full tame root tower; it does not give the affine SNC intersection-quotient data together with coefficient and prime localization identifications for the simultaneous root presentation.

lem-sfb-snc-root-local-presentation vs lem-sfb-snc-finite-root-regular-ring: the item concludes global regularity of the full root ring; the local-data node proves only the structural localization/intersection interface.

lem-sfb-snc-root-local-presentation vs lem-sfb-snc-finite-root-face-regular: the existing node concludes regularity of global coordinate faces and uses the item; the new node never assumes it and instead provides a strictly prior localization/intersection interface.

lem-sfb-snc-root-local-presentation vs lem-sfb-snc-boundary-parameter-criterion: the existing equivalence characterizes boundary parameters but does not assert Noetherianity of the full root presentation or identify its localizations with quotients over A_p.

lem-sfb-snc-root-local-presentation vs lem-sfb-snc-root-limit-normal-charts: the existing statement concerns normal charts and regular boundary equation on a full snc root limit; it does not give the affine SNC intersection-quotient data together with coefficient and prime localization identifications for the simultaneous root presentation.

lem-sfb-snc-root-local-presentation vs lem-sfb-snc-universal-residual-charts: the existing statement concerns henselian snc neighborhoods with universal residual cover; it does not give the affine SNC intersection-quotient data together with coefficient and prime localization identifications for the simultaneous root presentation.

lem-sfb-snc-root-local-presentation vs lem-sfb-snc-tame-root-etale-extension: the existing statement concerns a finite tame cover has an etale model after a simultaneous finite root base change; it does not give the affine SNC intersection-quotient data together with coefficient and prime localization identifications for the simultaneous root presentation.

lem-sfb-snc-root-local-presentation vs lem-sfb-equivariant-nodal-smooth-pair-resolution: the existing statement concerns equivariant resolution of one split marked nodal curve over a smooth pair; it does not give the affine SNC intersection-quotient data together with coefficient and prime localization identifications for the simultaneous root presentation.

lem-sfb-snc-root-local-presentation vs lem-per-marked-finite-diagram-approximation: the existing statement concerns regularity and boundary intersections persist under sufficiently fine marked approximation; it does not give the affine SNC intersection-quotient data together with coefficient and prime localization identifications for the simultaneous root presentation.

lem-sfb-snc-root-local-presentation vs lem-per-embedded-surface-curve-resolution: the existing statement concerns embedded snc resolution on a regular surface; it does not give the affine SNC intersection-quotient data together with coefficient and prime localization identifications for the simultaneous root presentation.

lem-sfb-snc-root-local-presentation vs lem-per-snc-boundary-parameter-criterion: the existing equivalence characterizes boundary parameters but does not assert Noetherianity of the full root presentation or identify its localizations with quotients over A_p.

lem-sfb-snc-root-local-presentation vs lem-per-regular-pair-alteration-pullback: the existing statement concerns regular base change preserves regular alteration pairs; it does not give the affine SNC intersection-quotient data together with coefficient and prime localization identifications for the simultaneous root presentation.

lem-sfb-snc-root-local-presentation vs lem-per-ind-etale-regular-coordinate-locus: the existing statement concerns openness and ind-etale invariance of a labelled regular-coordinate locus; it does not give the affine SNC intersection-quotient data together with coefficient and prime localization identifications for the simultaneous root presentation.

lem-sfb-transverse-local-root-family-regular vs lem-sbc-root-algebra-regular-at-root: the existing node concerns one equation at primes containing its root and assumes injective multiplication and a regular quotient; this node proves regularity of all transverse multi-root partial presentations at every prime, deriving those hypotheses and handling the complementary primes.

lem-sfb-transverse-local-root-family-regular vs lem-sbc-regular-divisor-root-model-normal: the existing statement concerns normal stalks of full root algebras along a regular divisor; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-sbc-regular-integral-divisor-boundary: the existing statement concerns regular codimension-two boundary away from an integral divisor generic point; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-trf-permissible-coordinate-chart: the existing statement concerns regularity and coordinate intersections on a permissible blowup chart; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-sfb-snc-finite-root-regular-ring: the item is the geometric global SNC theorem, whereas this node proves its separate local algebra induction with all J,K and no SNC-scheme hypothesis.

lem-sfb-transverse-local-root-family-regular vs lem-sfb-snc-finite-root-face-regular: the existing node concludes regularity of global coordinate faces and uses the item; the new node never assumes it and instead provides a strictly prior local algebra calculation from explicit transverse coefficient-quotient hypotheses.

lem-sfb-transverse-local-root-family-regular vs lem-sfb-local-surface-maximal-blowup-geometry: the existing statement concerns geometry of the maximal-ideal blowup of a regular local surface; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-sfb-snc-universal-residual-charts: the existing statement concerns henselian snc neighborhoods with universal residual cover; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-sfb-snc-tame-root-etale-extension: the existing statement concerns a finite tame cover has an etale model after a simultaneous finite root base change; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-per-primitive-monomial-trait-geometry: the existing statement concerns geometry of a monomial trait model with a generically invertible exponent; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-per-noetherian-local-colimit-regular: the existing statement concerns noetherian directed colimits of regular local rings are regular local; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-per-complete-mixed-regular-pair-approximation: the existing statement concerns simultaneous regular-pair approximation over a complete cohen trait; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-per-surface-point-blowup-geometry: the existing statement concerns regularity and projectivity of a point blowup on a regular surface; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-weil-pbc-hypersurface-derivation-regular: the existing node assumes a derivation with unit value modulo one equation; this node derives its use after localization only on the unit-root locus and separately proves the ramified locus by simultaneous induction.

lem-sfb-transverse-local-root-family-regular vs lem-weil-pbc-complete-local-map-cohen-presentation: the existing statement concerns compatible cohen power-series presentations of a complete local map; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-weil-pbc-another-helper-g-ring: the existing statement concerns formal fibres of a[x] over nonzero primes above (0), a complete local domain of characteristic p; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-weil-pbc-regular-local-hypersurface-criterion: the existing statement concerns a non-square element cuts a regular local hypersurface; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-weil-pbc-another-helper-g-ring-noetherian-component: the existing statement concerns noetherian component of polynomial formal fibre; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-weil-pbc-polynomial-complete-local-formal-fibres: the existing statement concerns formal fibres of a polynomial ring over a complete local ring at a maximal ideal over the closed point; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-weil-pbc-degree-p-extension-regular: the existing node requires a derivation of the coefficient ring taking the branch equation to a unit; no such derivation is assumed here, and the ramified root case instead uses the regular transverse coefficient quotients.

lem-sfb-transverse-local-root-family-regular vs lem-weil-pbc-polynomial-complete-local-nonzero-fibre-char-zero: the existing statement concerns nonzero polynomial formal fibres in characteristic zero; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-weil-pbc-another-helper-g-ring-geometric-component: the existing statement concerns geometric component of polynomial formal fibre; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-exc-regular-local-lift-regular-sequence-quotient: the existing statement concerns regularity lifts from the quotient by a regular sequence; it does not give the regularity and finite free basis of every B_{J,K} over arbitrary regular local coefficient quotients under the explicit dimension conditions.

lem-sfb-transverse-local-root-family-regular vs lem-per-snc-root-algebra-structure: that theorem assumes a strictly henselian local base, parameter equations in its maximal ideal and a primitive root of unity, and also proves Galois structure; this local-family lemma imposes none of those extra hypotheses, includes unit branch equations, and proves the simultaneous J,K induction.

## Retained prior delivery report (historical Q08 report)

The following report describes the previous seven-step delivery before this repair; its statements about zero new nodes and seven proof steps are historical.

## Worker report

1. Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-snc-finite-root-regular-ring.json` (existing statement, now split; no Mathlib match), and the supporting `citations.json`. No new nodes, no new Mathlib leaves. The sandbox also contains the exact search log and a preparation script.
2. Attachments: none. The tag search and concept searches under `lean/WeilConjectures/` find the one-root lemma `AdjoinRoot.isRegularLocalRing_atPrime_of_root_mem`, which is already attached to `lem-sbc-root-algebra-regular-at-root`; it does not state the simultaneous SNC theorem. No project declaration gives every clause of this item.
3. WANTED: none.
4. The item was statement-only. Its statement is correct and unchanged. ILO IX Proposition 2.1, printed p.133 (PDF page 139), writes the full simultaneous parameter-root algebra before invariants but leaves its regularity calculation implicit. I supplied that calculation and marked the proof as agent-written. I retained all inherited source/creation metadata. The inherited blueprint ancestor is null: `tools/blueprint_refs.py ancestor lem-sfb-snc-finite-root-regular-ring` explicitly reports None. Its existing from.place and via chain are preserved. Searches of the whole imported blueprint for normal crossings, strict normal, finite simultaneous, parameter root, regular root, regular ring and root found no equivalent blueprint statement. This fills the original open-direct-image paragraph (3) finite-root regularity subargument, without changing a chapter or unit route.
5. Nothing remains unfinished in the one-level split. No Lean was written, no compiler or Lake was run, and the repository and launcher scripts were read only.

## Sources and searches

I read ILO IX Proposition 2.1 and its proof on printed pp.133–134; the calculation uses the full root algebra, not an invariant subring. I also read Stacks `etale.tex`, Tag 0BIA (`lemma-strict-normal-crossings`), including the regular-intersection/parameter proof; `algebra.tex`, Tag 00FN (`lemma-Noetherian-permanence`), Tag 00NP (`lemma-regular-domain`), Tag 00NQ (`lemma-regular-ring-CM`), and Tag 00NU (`lemma-regular-mod-x`); `properties.tex`, Tag 02IT (`lemma-characterize-regular`); and `more-algebra.tex`, Tag 07PF (`lemma-quotient-regular`). These justify the existing black-box nodes used here. No SGA source is used.

The item's earlier Mathlib searches are retained. Six fresh searches ran through the required msearch command: two LeanFinder phrasings, LeanSearch, Loogle `IsRegularLocalRing, AdjoinRoot`, and two grep expressions. I read the returned standard-etale and regular-polynomial sources. Standard-etale presentations do not establish the ramified case; `MvPolynomial.isRegularRing_of_isRegularRing` only supplies the ambient polynomial ring, and the regular-element declarations are not regular-ring theorems. The Kummer keyword grep also returns unrelated Kummer number theory; it is not evidence of a match. The exact queries and actual hit summaries are copied from `searches.jsonl`, and no unavailable service was labelled no-match.

## Not duplicates

There are no new nodes. Existing generic algebra nodes are reused: in particular `lem-sbc-root-algebra-regular-at-root`, `lem-weil-pbc-monic-quotient-free`, `lem-weil-pbc-hypersurface-derivation-regular`, and `lem-trf-polynomial-ring-regular-base`. The one-root lemma is used only at primes containing the new root, not claimed to prove the entire item.

## Review by Q08

I checked the proof against delivery-errors B–E with the cited statements open. The item states the full cover ring, not an invariant quotient, and all V(t_i) are the reduced distinct branches as closed subschemes, so their scheme-theoretic intersection is exactly the quotient by their equations. The boundary definition already asserts regularity and the precise local dimension equalities for every intersection; I use those clauses directly, rather than citing a definition for an unstated theorem. There are no new statement-only nodes requiring extra sources, searches or duplicate comparisons.

Step 1 uses the regular-scheme definition only for local Noetherianity and regular local stalks; `pqf-lem-affine-open-locnoeth` says the coordinate ring of this affine open is Noetherian, `lem-weil-pbc-finite-type-algebra-noetherian` applies to the displayed finite polynomial quotient, and `lem-weil-pbc-affine-open-stalk-localization` identifies A_p with the stalk. Thus the global Noetherian assertion is proved, not inferred merely from all stalks being Noetherian.

Step 2 uses the exact regular-intersection/dimension clauses of `def-trf-strict-normal-crossings-boundary`, and the quotient-localization and affine-stalk isomorphisms from `lem-weil-pbc-localization-at-prime-of-quotient` and `lem-weil-pbc-affine-open-stalk-localization`. For J contained in the set S of branches through p, p is actually on that intersection. Thus R_J is a nonzero regular local ring, with dim(R_J)+|J|=dim(R). A branch outside S is a unit already before any extension. No parameter-selection theorem or unstated SNC-coordinate comparison is used.

Step 3 uses precisely the basis and reduction clauses of `lem-weil-pbc-monic-quotient-free`, Noetherianity from the finite presentation, and the explicit consequence in `lem-weil-pbc-regular-local-localization` that a regular local ring is a regular ring. The induction is simultaneous over disjoint (J,K), with measure |K|. The base is stated. The reordering identification fixes all constants and root coordinates, so it follows directly from the quotient presentations and is not a separate comparison lemma.

Step 4 checks the hypotheses needed by the later root lemma. If the prime contains u, the equation u^n=t_i rules out i outside S. For i in S but outside J, the dimension equalities show t_i is nonzero in R_J: otherwise the next quotient is the same ring with a different asserted dimension. `lem-sc-regular-local-domain` really says this regular local coefficient ring is a domain. The finite free basis then proves injectivity of t_i on D coefficient by coefficient. I did not assert that the partial root ring D is local or a domain.

Step 5 uses the actual reduction-mod-I clause of the monic-basis node to identify D/(t_i) with the presentation over R_{J union {i}}. Both algebra maps are described on generators. The induction hypothesis has fewer roots, even though J is larger. The existing root-at-divisor node explicitly assumes Noetherianity, injective multiplication by the equation, positive exponent and regular quotient, and concludes regularity at each prime containing the root. All four hypotheses have been proved. It neither needs invertibility of n nor assumes D local.

Step 6 handles the complementary primes with a different existing tool. Since u is outside Q, t_i=u^n is outside Q. The localization-permanence node applies to regular D, the polynomial-regularity leaf applies to regular E=D[1/t_i], and the hypersurface derivative node applies to E[T] with its ordinary derivative. I wrote the inverse T^(n-1)/t_i and computed the unit derivative nT^(n-1). The integer n remains a unit under every coefficient quotient/localization. The local rings are identified by the explicit mutually inverse maps on fractions; no etale-regularity theorem is implicitly substituted for the derivative node's actual statement.

Step 7 specializes the induction and writes the coefficient-localization and subsequent prime-localization maps. This is the routine universal-property calculation on the displayed generators and fractions, hence marked elementary. The last assertion is the definition of a regular ring. I checked zero A (then zero C_n and no primes), r=0 (base of the induction), n=1 (root equation removes the variable, derivative 1), primes off every branch (only the unit-derivative case), and primes on all or some branches. Pairwise distinctness matters: repeated branch equations would not supply the intersection dimension equalities, and for A=k[t], x^n=t=y^n generally gives a singular crossing at x=y=0 when n>1. That failure is excluded by the hypotheses, not silently ignored.

All seven proof steps are below 2000 characters; none hides an independent general lemma. The simultaneous induction is the proof of this item, not a newly named clause or restatement. Every non-elementary tool is an existing cited node and each citation has a full verbatim statement quote in citations.json. The five generic off-unit algebra tools are declared in split_report.tool_uses with their precise roles; they supply local algebra without changing the six-functor route. I checked B1–B10 (no new nodes, real searches, existing attachments only), C1–C8 (claims, citations, no cycle or illicit off-unit route), D1–D5 (actual induction, no relabelling or implicit source proof), and E1–E7 (hypotheses, objects, formula identifications and edge cases).
