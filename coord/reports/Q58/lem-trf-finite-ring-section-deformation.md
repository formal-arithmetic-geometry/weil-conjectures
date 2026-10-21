# Worker report: Q58 / lem-trf-finite-ring-section-deformation

## Files written

- dag/nodes/sec-trace-formula/lem-trf-finite-ring-section-deformation.json: existing statement unchanged; seven-step assembly, 2164 characters in its proof text.
- dag/nodes/sec-trace-formula/lem-trf-smooth-section-centred-coordinates.json: statement, unsplit; no Mathlib match, no proof or proof dependencies.
- dag/nodes/sec-trace-formula/lem-trf-section-rees-noetherian-geometry.json: statement, unsplit; no Mathlib match, no proof or proof dependencies.
- dag/nodes/sec-trace-formula/lem-trf-section-rees-base-change-etale.json: statement, unsplit; no Mathlib match, no proof or proof dependencies.
- dag/nodes/sec-trace-formula/lem-trf-section-local-dualizing-comparisons.json: statement, unsplit; no Mathlib match, no proof or proof dependencies.
- dag/nodes/sec-trace-formula/lem-trf-etale-shifted-line-normalized-descent.json: statement, unsplit; no Mathlib match, no proof or proof dependencies.
- dag/nodes/sec-trace-formula/lem-trf-section-exceptional-fibre-coherence.json: statement, unsplit; no Mathlib match, no proof or proof dependencies.
- dag/nodes/sec-trace-formula/lem-trf-section-coordinate-counit-normalization.json: statement, unsplit; no Mathlib match, no proof or proof dependencies.
- dag/nodes/sec-trace-formula/lem-trf-finite-ring-bundle-section-orientation.json: statement, unsplit; no Mathlib match, no proof or proof dependencies.

Supporting sandbox files: citations.json contains the full verbatim statement of each new node for every parent-step citation. searches.jsonl is the original msearch log; search-plan.json and search-*.txt preserve node-specific queries and full answers. No Lean source was written or compiler invoked.

## Attachments

None. The project-source search under lean/WeilConjectures found no declaration stating the entire finite-ring Noetherian ordinary-etale assertion. The matching stage-2 module lean/Sheaf/Paper/FiniteRingSectionDeformation.lean has sorry in geometry, lines_and_fibres, existsUnique_normalized, baseChange_compatibility, etale_compatibility, coordinate_normalization, bundleOrientation_frames and bundleOrientation_purity. Its assembled theorem therefore cannot be attached as a completed proof.

## WANTED

None. All source material used is present locally.

## What changed and why

This is the explicit human-authorized re-split of 2026-10-21, not a claim that the already reviewed stage-1 proof was absent. Its statement, coefficient category, arbitrary-base-change scope, ancestor chain and normalization are unchanged. Eight tasks expose the distinct geometric, descent, coherence and trace arguments. All eight are statement-only and can be assigned independently. No task assumes another new task or the parent. Each introduces its objects and hypotheses; no “in the setting above” refers back to the parent. The parent proof is a short assembly, with every non-elementary input cited.

The older split called its regular-coordinate algebra step elementary, although it combines flat tensor exactness and a symmetric-to-graded calculation. That argument now belongs to the coordinates/conormal task rather than being hidden under an elementary flag. The separate counit-pasting task carries the coherence identities; exactness of pullback alone is never used to assert those identities. Nothing invokes SGA 4 or SGA 4½. The original proof text and all its lower-level uses are reproduced below, not shortened or replaced by a vague summary.

## Work allocation and retained arguments

| New statement-only task | Old proof steps | Separate mathematical work |
|---|---|---|
| lem-trf-smooth-section-centred-coordinates | 1, 2 | centred charts, removing the other zero-locus components, regular coordinate injections, flat monomial graded algebra |
| lem-trf-section-rees-noetherian-geometry | 3, 4 | Rees charts and degree pieces, both fibres, punctured cover, smoothness, Noetherianity, separatedness and Nagata compactifications |
| lem-trf-section-rees-base-change-etale | 5, 6 | arbitrary nonflat base change via etale polynomial charts; flat etale pullback of Laurent pieces and the precise induced normal linear map |
| lem-trf-section-local-dualizing-comparisons | 7, 8, 9 | shifted rank-one property, actual counit-defined fibre isomorphisms, affine-space locality identifications and correction at one |
| lem-trf-etale-shifted-line-normalized-descent | 10, 11 | scalar ratios on geometric affine lines, connectedness, conservative stalks, sheaf-level gluing of maps and inverses, uniqueness |
| lem-trf-section-exceptional-fibre-coherence | 12, 13, 14 | mate pasting for base changes and etale adjoint locality, the two fibre coherence equations, uniqueness-based naturality and inverse-zero equations |
| lem-trf-section-coordinate-counit-normalization | 15 | transpose the actual base-change identity of coordinate-tower counits; normalization in standard and etale section charts |
| lem-trf-finite-ring-bundle-section-orientation | 16 | linear trace invariance, counit-preserving adjoint orientations, frame gluing and agreement with inverse vector-bundle purity |

The sizes of the eight task statements, including explicit notion citations, are 1899, 2386, 2735, 3184, 1594, 3232, 2886, 2334 characters. Their proof workloads are distinct: no new node asserts the whole finite-ring section-deformation theorem. The geometric outputs feed the local dualizing construction; the general descent theorem and the independent counit-coherence theorem are then combined. The two orientation tasks concern respectively coordinate normalization and frame gluing.

## Sources read

Read sk-thm-dnc.proof.md (Local construction and Gluing) in main-20261015, sk-thm-smooth-purity.proof.md (finite-ring extension of Kummer and diagonal calculations), and sk-prop-sp-orientation-charts.proof.md (Cartesian centres, induced normal isomorphism, locality, linear integration). For the first new task also read the actual local Stacks source statements and proof at 054L = morphisms/lemma-smooth-etale-over-affine-space, 024T = etale/proposition-properties-sections and 067U = divisors/lemma-immersion-smooth-into-smooth-regular-immersion. These tags support coordinates, clopen removal and regularity; they are not asserted to contain all the monomial algebra. The blueprint and the retained old agent proof supply the remaining argument.

Task 1 follows Local construction and the three tags just named. Task 2 follows the Rees-chart/fibre and finite-type paragraphs of the existing agent proof against Local construction; its required lower-level statements are lem-pur-dnc-etale-rees-chart, lem-pur-conormal-graded-algebra, and the Noetherian/permanence/Nagata inputs retained below. Task 3 follows the explicit base-change and etale-of-pairs paragraphs and orientation-charts Steps 1–2. Task 4 follows the opening paragraph and the two local affine-space identifications, using the ordinary-etale statements thm-asd-smooth-tensor, prop-asd-smooth-base-change, cor-amb-affine-space-adjunction and lem-amb-etale-adjoint-locality. Task 5 follows Gluing, with the scalar-Hom and sheaf-Hom statements read explicitly. Task 6 follows the retained mate-pasting argument: I read lem-amb-unbounded-compact-support-comparisons, lem-weil-pbc-mate-pasting, prop-asd-smooth-base-change and the locality statement, which fix the actual maps. Task 7 follows the standard model and orientation-charts Step 3; I read the actual arbitrary-base-change identity for the counit in lem-amb-affine-space-top-trace, not just the existence of an adjunction. Task 8 follows orientation-charts Step 4; I read lem-amb-linear-trace-invariance and thm-amb-vector-bundle-purity, whose latter statement defines its purity map using precisely these traces.

## Mathlib searches and existing-source searches

For every new id, its own statement/concept was searched by two differently phrased LeanFinder queries, LeanSearch, Loogle and logged Mathlib grep; the exact queries, full results and verdicts are in the node. Supplementary targeted AlgebraicGeometry greps eliminate broad-word false hits. Loogle’s unavailable identifiers for the first attempts at IsPullback/IsEtale/VectorBundle are recorded as query-index failures, not as mathematical absence; a further valid Loogle query for “Etale” and “TensorProduct” returned algebraic etale base-change lemmas only. All services responded on this run; no unrun query is claimed.

The semantic hits for Task 1 concern standard smooth presentations and ranks of Kaehler differentials; they do not provide the centred section, conormal monomials and gluing. Tasks 2–3 return smooth/etale base-change infrastructure and tensor-product spectra, not extended Rees deformations. Task 4 returns algebraic coordinates, standard smoothness and sheafification adjunctions, not the compact-support dualizing-object comparison. Task 5 returns ordinary sheaf unique gluing and Zariski module pullback units, not affine-line etale endomorphism rigidity and shifted descent. Task 6 finds the general mate pasting lemmas (Mathlib/CategoryTheory/Adjunction/Mates.lean, lines 169–213, read) but they require the geometric exchanges/locality maps to be constructed and identified; the new statement is not their one-line specialization. Tasks 7–8 return number-field normalized trace, ordered-real orientations and analytic vector-bundle trivializations, not the etale Kummer counit or algebraic-bundle zero-section orientation. Hence zero Mathlib leaves.

Searched the entire DAG and blueprint by deformation, centred coordinates, Cartesian square of centres, shifted line, normal-bundle orientation, fibre comparisons, coordinate-tower, rigidity, adjoint orientations, and the three Stacks tags. The ancestor tool gives lem-trf-local-term-locality; each new from.via prepends the item to its existing chain. Existing lem-pur-dnc-section-geometry, sk-thm-dnc, prop-pur-dnc-family-constancy, det-sp-orientation-charts and det-sp-orientation-vector-bundle use the special finite-field/pro-etale coefficient conventions, so none states these Noetherian ordinary-etale finite-ring tasks. Also read lem-pur-noetherian-etale-section-specialization: it restricts A to Z/ell^n, assumes regularity/compactifiability and does not give the separate local and coherence assertions here.

## Not duplicates

lem-trf-smooth-section-centred-coordinates vs lem-pc-dense-separable-points: density of finite separable closed points on a smooth scheme over a field; no section or conormal graded isomorphism.
lem-trf-smooth-section-centred-coordinates vs lem-pur-smooth-pair-local-coordinates: general local coordinates for two smooth schemes; no affine cover of the entire section over base opens or canonical symmetric-to-graded isomorphism.
lem-trf-smooth-section-centred-coordinates vs lem-pur-smooth-pair-regular-immersion: regular generating sequence only; no centred etale coordinate cover with fixed relative dimension or monomial symmetric-to-graded comparison.
lem-trf-smooth-section-centred-coordinates vs lem-sc-smooth-diagonal-regular-immersion: the diagonal ideal of a smooth morphism, not the section-chart/conormal comparison.
lem-trf-smooth-section-centred-coordinates vs lem-sc-smooth-proper-diagonal-koszul-regular: diagonal Koszul-regularity/perfectness, not centred coordinates and section conormal algebra.
lem-trf-smooth-section-centred-coordinates vs lem-sc-standard-smooth-local-relative-dimension: standard smooth neighbourhoods of points with the right dimension, not a section-centred Cartesian zero fibre or conormal monomial comparison.
lem-trf-smooth-section-centred-coordinates vs lem-sp-smooth-admissible-coordinate-cover: finite-type schemes over a positive-characteristic field with a cover of the ambient scheme, no centred closed section or symmetric-to-graded assertion.
lem-trf-smooth-section-centred-coordinates vs lem-trf-curve-centred-valuation-dvr: a valuation-ring statement for an integral smooth curve over a field, not a general relative smooth section.
lem-trf-smooth-section-centred-coordinates vs lem-weil-pbc-etale-section-clopen-immersion: the clopen property of a section of an etale map; only an input to constructing the coordinates, not the coordinate/conormal conclusion.
lem-trf-smooth-section-centred-coordinates vs sbc-thm-etale-local-normal-form: uncentred pointwise smooth normal form only; no Cartesian section square or conormal algebra.
lem-trf-smooth-section-centred-coordinates vs lem-trf-finite-ring-section-deformation: only the geometric coordinate/conormal task, independent of coefficients, without deformation duality, global comparison, naturality or orientations.
lem-trf-section-rees-noetherian-geometry vs lem-pur-dnc-etale-rees-chart: the existing algebra chart is an input, not the global Noetherian/compactifiable family, fibre and coverage statement.
lem-trf-section-rees-noetherian-geometry vs lem-pur-rees-associated-graded-chart: the existing quotient-ring identity is an input, not smooth section geometry or compactifiability.
lem-trf-section-rees-base-change-etale vs lem-trf-dnc-functorial-geometry: that statement concerns arbitrary ideals over the fixed finite-field trait and includes fixed schemes; it does not assert arbitrary nonflat base-change isomorphisms over a Noetherian base or etale smooth-section normal-bundle compatibility.
lem-trf-etale-shifted-line-normalized-descent vs lem-pur-a1-pullback-endomorphism-rigidity: the existing statement uses small pro-etale sites and only endomorphism rigidity; the new ordinary-etale statement additionally constructs a unique shifted comparison from normalized local data.
lem-trf-etale-shifted-line-normalized-descent vs lem-pur-diagonal-orientation-compatibility: existing ordinary-etale Hom rigidity is for prime-power cyclic coefficient reductions, whereas this task allows every finite commutative ring and establishes normalized descent with supplied local isomorphisms.
lem-trf-section-exceptional-fibre-coherence vs lem-weil-pbc-mate-pasting: generic categorical pasting supplies the method, not identification of the actual exceptional fibre maps with etale locality on a smooth family.
lem-trf-section-coordinate-counit-normalization vs lem-amb-affine-space-top-trace: trace base-change compatibility is an input; the new result transposes it to exceptional right-adjoint and section-chart normalizations.
lem-trf-finite-ring-bundle-section-orientation vs thm-amb-vector-bundle-purity: that theorem allows valuation-ring quotients only; this task glues a zero-section orientation for arbitrary finite A and additionally identifies it with the old purity map in its scope.

## Review by Q58

I read the item statement, its full old proof and the current source proofs before extracting the tasks. I checked the parent statement is byte-for-byte unchanged. Step 1 cites exactly the new coordinates and Rees-geometry statements: the first gives regularity/rank and the canonical graded comparison, and the second gives smoothness, both pairs and compactifications. Its hypotheses are exactly the given Noetherian smooth separated finite-type section. Step 2 cites the Rees functoriality statement, whose algebra formula explicitly allows nonflat R to R-prime and whose etale clause fixes the induced conormal linear map; it does not appeal to flat base-change invariance for an arbitrary ideal.

Step 3 cites the local-dualizing statement and the normalized-descent statement. The former gives both shifted sheaves, the actual theta and eta isomorphisms, and local maps normalized at one; the latter accepts those data with m=2d and gives the unique global kappa. I checked every geometric/compactifiability hypothesis of the former is supplied by Step 1. Delta then has the correct direction: eta composed with the inverse of i0-star kappa. Both morphisms and inverse morphisms descend as sheaf morphisms after a common shift; no unproved derived-category descent is hidden.

Steps 4 and 5 cite fibre coherence and normalized descent. I checked the two theta/eta equations have matching domains, that the b maps are the actual counit-mate or counit-preserving locality maps, and that invertibility is stated. The comparisons over the base-changed Noetherian scheme have the same hypotheses by Step 2. The candidate a-prime-star b_C composed with the pulled-back kappa and b_F inverse restricts to theta-prime; the uniqueness input therefore applies. The zero equation is then exactly delta-prime b_C = b_H v-star delta. For an etale neighbourhood the geometry has already supplied the precise linear normal-bundle identification.

Step 6 cites the coordinate-counit normalization statement and descent uniqueness. I checked it fixes the Kummer-normalized tower counit, not just any orientation isomorphism. Its equality is with theta, so the correction h is actually identity, and the locally induced map is the restriction of the globally normalized kappa. Step 7 cites the bundle orientation and coordinate-counit statements. Their frame maps are inverses of the affine-space adjoint orientations; invertible linear changes preserve the counits, so their sections agree. The valuation-ring quotient comparison uses the integration map specified in vector-bundle purity, with the canonical ordinary Tate identifications.

For every new statement I tested d=0 (empty coordinate sequence, identity affine adjunction), empty S (empty cover and unique maps), and A=0 for the coefficient tasks (all module sheaves zero and unique isomorphisms). For Task 1 I also tested a nonreduced Noetherian base: polynomial variables remain regular even when coefficients have zero divisors. For Tasks 2–3 the standard ring model R[x] and a nonflat quotient R to R/J still give R-prime[t,u], so the base-change formula does not silently assume flatness of the base. Removing other zero-locus components is scheme-theoretic and uses the separated etale section being clopen. For Task 5, Artin–Schreier local systems on an affine line do not contradict the assertion: it assumes the local comparisons are supplied and only proves rigidity of a base pullback; it does not assert all lisse sheaves descend. For Task 8 arbitrary A includes mixed-prime products, while agreement with the published purity theorem is asserted only for its stated valuation-ring quotient coefficients.

Against delivery-errors B–E, I checked self-contained objects and hypotheses, statement-only new files, genuine subdivision rather than a replacement theorem, no false attachment to sorried Lean, all searches actually logged, precise blueprint ancestry, the finite-field/pro-etale near-duplicates distinguished above, the unchanged route, and each parent citation against the full new statement copied into citations.json. No parent step exceeds 2000 characters. All non-elementary parent work is an explicit cited theorem; all substantive old subarguments have their own work assignment below. The old elementary uniqueness/naturality calculations are also stated in the coherence task and written in the parent assembly. No statement dispute was found.

## Unfinished work

The eight new tasks deliberately have status unsplit and no proof steps: this is the human-requested work spreading. Their proofs are not claimed complete. The parent is fully assembled from their statements. No stage-2 or stage-3 work was attempted.

## Original arguments retained verbatim for future workers

These are handoff material, not proof fields of the new statement-only nodes. Each paragraph retains its original sources and cited lower-level nodes.

### Original step 1 → lem-trf-smooth-section-centred-coordinates

Work locally on $S$ with an affine open $S_i$ and an affine neighbourhood $U_i$ of $s(S_i)$ in $V\times_SS_i$. Such neighbourhoods exist: start at $s(b)$, choose an affine neighbourhood in $V$, and shrink the base inside its inverse image under $s$. The smooth normal form gives a separated etale map $e_i:U_i\to\mathbf A^d_{S_i}$, with $d$ the given relative dimension. Subtract the values of its coordinates on the section, so $e_is=0$. The inverse image $P_i=e_i^{-1}(0)$ is separated etale over $S_i$ and its section is open and closed. Its complement to $s(S_i)$ is closed in $P_i$, hence closed in $U_i$. Remove that complement, and choose affine neighbourhoods and shrink the base once more if needed. Thus the centre square is Cartesian. Write $S_i=\operatorname{Spec}R$, $U_i=\operatorname{Spec}B$, $P=R[x_1,\ldots,x_d]$, $J=(x_1,\ldots,x_d)$; then $I=JB$ and $B/I=R$. The etale algebra $B$ is flat over $P$.

Original uses: sbc-thm-etale-local-normal-form, lem-sbc-smooth-relative-dimension-permanence, lem-weil-pbc-affine-source-morphism-separated, lem-weil-pbc-etale-scheme-base-change, lem-weil-pbc-separated-base-change, lem-weil-pbc-etale-section-clopen-immersion, def-weil-etale-morphism, lem-weil-pbc-flat-morphism-affine-criterion, lem-weil-pbc-etale-smooth-zero-dimensional-fibres, sbc-lem-affine-space-smooth.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md — Local construction, first paragraph; Stacks 054L/lemma-smooth-etale-over-affine-space and 024T/proposition-properties-sections.

### Original step 2 → lem-trf-smooth-section-centred-coordinates

The coordinates $x_1,\ldots,x_d$ are a regular sequence in $P$: successive quotients are polynomial rings over $R$ and multiplication by the next variable is injective by comparison of coefficients. Flat tensor exactness for $P\to B$ preserves these successive injections, so their images form a regular sequence defining the section. Tensoring $0\to J^{m+1}\to J^m\to J^m/J^{m+1}\to0$ identifies $I^m/I^{m+1}$ with $B\otimes_P(J^m/J^{m+1})$. The monomials of degree $m$ give an $R$-basis of $J^m/J^{m+1}$, and $B\otimes_PR=B/I=R$. Hence $I/I^2$ is free of rank $d$, and the canonical multiplication map $\operatorname{Sym}_{B/I}(I/I^2)\to\bigoplus_{m\geq0}I^m/I^{m+1}$ is an isomorphism, sending each basis monomial to its class. These canonical maps agree on restrictions. This proves regularity, codimension $d$ in the regular-immersion sense, local freeness of the conormal, and the global symmetric-to-graded identification.

Original uses: lem-weil-pbc-flat-tensor-exact, lem-pur-conormal-graded-algebra.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md — Local construction, regular-coordinate algebra; compare Stacks 067U/lemma-immersion-smooth-into-smooth-regular-immersion.

### Original step 3 → lem-trf-section-rees-noetherian-geometry

The etale Rees chart lemma gives
$$B[t,I/t]\cong B\otimes_P R[t,u_1,\ldots,u_d],\qquad x_j\mapsto tu_j.$$
Thus the induced deformation chart $D_{U_i}\to\mathbf A^d_{\mathbf A^1_{S_i}}$ is etale and its structural morphism is smooth of relative dimension $d$. In the full extended Rees algebra the Laurent coefficient in degree $-m$ is $I^m$, for $m>0$, and in degree $k\geq0$ it is $B$. Quotient by $t$ therefore has pieces $I^m/I^{m+1}$. Step 2 identifies its spectrum with $N_s$ and its augmentation with the zero section. Inverting $t$ gives $\mathcal O_V[t,t^{-1}]$, with section $s\times1$; evaluating at $1$ gives $(V,s)$. The charts $D_{U_i}$ cover the zero fibre because their images cover the centre; together with the punctured deformation they cover $D$. Smooth permanence on the punctured part and on the etale charts proves smoothness of $\widetilde g$ of dimension $d$ everywhere.

Original uses: lem-pur-dnc-etale-rees-chart, lem-pur-conormal-graded-algebra, lem-sbc-smooth-relative-dimension-permanence.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md — Local construction, deformation charts and the two fibres.

### Original step 4 → lem-trf-section-rees-noetherian-geometry

Every affine ideal of the centre is finitely generated since $V$ is Noetherian: $V$ is finite type over the Noetherian $S$. If $I=(f_1,\ldots,f_r)$, its extended Rees algebra is generated by $t,f_1/t,\ldots,f_r/t$. Consequently $D\to V$ is finite type, so $D$ is Noetherian. Its map to $V\times_S\mathbf A^1_S$ is affine and hence separated. Composing with the separated base change of $g$ proves that $\widetilde g$ is separated. The bundle $\pi$ is affine, separated, smooth of dimension $d$ and finite type by its local polynomial descriptions. Every Noetherian scheme here is quasi-compact and quasi-separated: an open subscheme of a Noetherian scheme is quasi-compact, in particular every intersection of two affine opens. Nagata therefore supplies compactifications of $\pi$, $\widetilde g$, and every separated finite-type chart map and composite used below. Their open source schemes are again Noetherian.

Original uses: def-weil-pbc-noetherian-ring, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-separated-base-change, lem-weil-pbc-proper-fp-permanence, def-asd-vector-bundle-zero-section, sbc-lem-affine-space-smooth, lem-weil-pbc-noetherian-open-subscheme-noetherian, thm-nagata-compactification.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md — Local construction, finite type and compactifiability of the Rees family.

### Original step 5 → lem-trf-section-rees-base-change-etale

For arbitrary, possibly nonflat, $S'\to S$, work over an affine $\operatorname{Spec}R'\subset S'\times_SS_i$. Put $P'=R'[x]$, $B'=B\otimes_RR'$, $I'=JB'$. The chart $P'\to B'$ is etale and flat. Applying the Rees chart formula before and after this change gives
$$B[t,I/t]\otimes_RR'\cong B'\otimes_{P'}R'[t,u]\cong B'[t,I'/t].$$
The maps send $t$ to $t$, $b$ to $b\otimes1$, and $x_j/t$ to $x'_j/t$; likewise the conormal basis $[x_j]$ maps to $[x'_j]$. Off $t=0$ the equality is simply Laurent-polynomial base change. These canonical maps agree on restrictions and glue, proving compatibility of the entire deformation, both sections and both fibre identifications with arbitrary base change. Smoothness and relative dimension survive by smooth permanence; the base-changed closed section is still closed. Its separated finite-type structural maps are again compactifiable by Step 4 over the Noetherian $S'$.

Original uses: lem-weil-pbc-etale-scheme-base-change, lem-pur-dnc-etale-rees-chart, lem-weil-pbc-flat-morphism-affine-criterion, def-weil-etale-morphism, lem-weil-pbc-scheme-morphism-gluing, lem-sbc-smooth-relative-dimension-permanence, lem-weil-pbc-closed-immersion-base-change, lem-pod-separated-finite-type-base-change, thm-nagata-compactification.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md — Local construction, explicit base-change maps.

### Original step 6 → lem-trf-section-rees-base-change-etale

For a separated etale map $h:V'\to V$ of neighbourhoods over $S$ with a Cartesian square of centres, on affine charts write $B\to B'$ and $I'=IB'$. Flat tensor exactness identifies $B'\otimes_BI^m$ with $I'^m$ and $B'\otimes_B(I^m/I^{m+1})$ with $I'^m/I'^{m+1}$. Tensoring the Laurent degree pieces yields $B'\otimes_BB[t,I/t]\cong B'[t,I'/t]$, inside $B'[t,t^{-1}]$. Thus the deformation map is a base change of $h$, hence etale. On the zero fibre its degree-one map is the conormal pullback isomorphism $[b]\mapsto[h^\sharp b]$; the induced symmetric-algebra map is exactly the linear isomorphism of normal bundles. The maps fix $t$ and preserve augmentations, so they preserve the sections and the fibre at $1$.

Original uses: def-weil-etale-morphism, lem-weil-pbc-flat-morphism-affine-criterion, lem-weil-pbc-flat-tensor-exact, lem-weil-pbc-etale-scheme-base-change, lem-pur-conormal-graded-algebra, def-asd-vector-bundle-zero-section.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md — Local construction, etale maps of pairs; orientation-charts proof Steps 1–2.

### Original step 7 → lem-trf-section-local-dualizing-comparisons

Apply the ordinary-etale smooth tensor theorem to $g$, $\pi$, and $\widetilde g$. Their sources and bases are Noetherian, the maps are separated, compactifiable, smooth of dimension $d$, and the same finite ring $A$ is killed by $N$, which remains invertible on every scheme involved. Thus $\omega_b[-2d]$ is a locally constant free rank-one sheaf. Exact constant-coefficient inverse image preserves this property, giving the asserted statements for $C[-2d]$ and $F[-2d]$. No change of coefficient category is involved.

Original uses: thm-asd-smooth-tensor, prop-weil-pbc-inverse-image-modules-exact.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md — Opening paragraph: shifted locally constant dualizing lines.

### Original step 8 → lem-trf-section-local-dualizing-comparisons

Apply counit-defined exceptional base change to $\widetilde g$ and $i_r:S\to\mathbf A^1_S$, $r=0,1$, and pull to the section. With Step 3 this gives the specified isomorphisms
$$\theta:i_1^*F\xrightarrow{\sim}C,\qquad \eta:i_0^*F\xrightarrow{\sim}z^*\omega_\pi.$$
The theorem applies to these closed changes of base without a flatness assumption. All pullbacks are the exact inverse images stipulated in the statement.

Original uses: prop-asd-smooth-base-change, prop-weil-pbc-inverse-image-modules-exact.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md — Opening paragraph: fibre identifications.

### Original step 9 → lem-trf-section-local-dualizing-comparisons

Etale locality of the compact-support right adjoint identifies its restriction to $U_i$ with $e_i^*\omega_{p_d}$, and on the deformation chart identifies its restriction with $\widetilde e_i^*\omega_{p_{d,\mathbf A^1_{S_i}}}$. Here the open restrictions and chart composites satisfy the Noetherian and compactifiability hypotheses by Step 4. The affine-space adjunction, compared with the Brown right adjoint by uniqueness respecting counits, identifies these dualizing objects with $A(d)[2d]$. Tate pullback then identifies both section restrictions with the corresponding pullbacks of $A_{S_i}(d)[2d]$. Smooth base change for $S_i\to S$ makes this a local isomorphism $\lambda_i:F|_{\mathbf A^1_{S_i}}\to a_i^*(C|_{S_i})$. Define $h_i=(i_1^*\lambda_i)\theta_i^{-1}$ and replace $\lambda_i$ by $a_i^*h_i^{-1}\lambda_i$. This gives $i_1^*\lambda_i=\theta_i$.

Original uses: lem-amb-etale-adjoint-locality, cor-amb-affine-space-adjunction, det-sp-unique-right-adjoint, lem-asd-etale-finite-twist-pullback, prop-asd-smooth-base-change.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md — Local construction, affine-space adjunction and normalization.

### Original step 10 → lem-trf-etale-shifted-line-normalized-descent

Shift all local comparisons by $[-2d]$. Full faithfulness of degree-zero complexes identifies them with actual sheaf morphisms. On an overlap their ratio is an automorphism of $a^*C[-2d]$. In a basis it is multiplication by a section of the constant unit sheaf $A^\times$; this description is independent of the basis since $A$ is commutative. More explicitly, the constant-module Hom lemma with $P=Q=A$ identifies local endomorphisms with scalar sections; the invertible ones are precisely the units. Pulling to a geometric fibre gives an automorphism of a constant free rank-one sheaf on $\mathbf A^1_\Omega$. The ring $\Omega[t]$ is a domain, so its zero prime is dense and its spectrum is irreducible, hence connected. Sections of a constant sheaf on this connected scheme are constant. The ratio has value $1$ at $t=1$, so it is the identity on the entire fibre. Every geometric point of $\mathbf A^1_S$ lies over such a geometric fibre. Exactness and conservativity of geometric stalks imply the ratio is globally the identity: the image of its difference from identity has zero stalks and hence is zero. The same argument proves uniqueness for any two global normalized comparisons.

Original uses: lem-weil-pbc-derived-single-fully-faithful, lem-pur-site-constant-module-hom, lem-weil-pbc-polynomial-ring-domain, lem-weil-pbc-spec-irreducible-closed-subsets-primes, lem-pc-irreducible-space-connected, lem-weil-pbc-constant-sheaf-set-sections-connected-natural, prop-weil-pbc-geometric-stalks-exact, lemma-weil-pbc-geometric-stalk-conservative.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md — Gluing, connected geometric affine-line fibres.

### Original step 11 → lem-trf-etale-shifted-line-normalized-descent

Sheaf-Hom gluing applies to the normalized maps and their inverses, since Step 10 proves agreement on overlaps. They glue to inverse global maps. Shifting back yields $\kappa:F\xrightarrow{\sim}a^*C$ with $i_1^*\kappa=\theta$, unique by Step 10. At $0$ the actual section comparison is
$$\delta=\eta\circ(i_0^*\kappa)^{-1}:C\xrightarrow{\sim}z^*\omega_\pi.$$
Under the stipulated identification by $\eta$ this is precisely the statement's formula.

Original uses: lem-pur-sheaf-hom-cover-gluing, lem-weil-pbc-derived-single-fully-faithful.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md — Gluing, global normalized comparison and restriction at zero.

### Original step 12 → lem-trf-section-exceptional-fibre-coherence

We first check coherence of the fibre maps. For any smooth compactifiable $b$, let $b_v:v_X^*\omega_b\to\omega_{b'}$ be the mate defined by transposing the pulled-back counit through inverse compact-support exchange. The unbounded compact-support exchanges commute with composite base changes and with composition of structural maps. Mate pasting therefore gives $b_{vw}=b'_w\circ w_X^*b_v$, with the inverse-image compositors understood. For $v:S'\to S$ write $b_C:v^*C\to C'$, $b_F:\bar v^*F\to F'$ and $b_N:v^*z^*\omega_\pi\to z'^*\omega_{\pi'}$ for their section pullbacks. The two decompositions of $\bar v i'_r=i_rv$ and Step 5 give
$$\theta' i_1'^*b_F=b_Cv^*\theta,\qquad \eta'i_0'^*b_F=b_Nv^*\eta.$$
These identities establish coherence with the chosen fibre identifications; exactness of pullback alone would not suffice.

Original uses: prop-asd-smooth-base-change, lem-amb-unbounded-compact-support-comparisons, lem-weil-pbc-mate-pasting.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md — Gluing, naturality of the normalized comparison under base change.

### Original step 13 → lem-trf-section-exceptional-fibre-coherence

All maps $b_C,b_F,b_N$ are isomorphisms by exceptional smooth base change. The candidate comparison over $S'$ is
$$\kappa^v=a'^*b_C\circ\bar v^*\kappa\circ b_F^{-1}.$$
Its restriction at $1$ is $\theta'$ by Step 12, so uniqueness gives $\kappa^v=\kappa'$. At $0$, the second equality in Step 12 and the inverse formula of Step 11 give $\delta'b_C=b_Nv^*\delta$. These are the required compatibilities with arbitrary Noetherian changes of base.

Original uses: prop-asd-smooth-base-change.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md — Gluing, uniqueness and arbitrary-base-change compatibility.

### Original step 14 → lem-trf-section-exceptional-fibre-coherence

For an etale map of pairs as in Step 6, the locality isomorphisms for right adjoints give $b_C:C\to C'$ and $b_F:F\to F'$ on the common bases, and the induced normal-bundle linear isomorphism gives $b_N:z^*\omega_\pi\to z'^*\omega_{\pi'}$. Compatibility of locality with the fibre comparisons follows from the same mate-pasting calculation: locality is the comparison between the composite adjunction for $Rh_!\dashv h^*$ and the compact-support adjunction for the composite structural map. Compact-support composition and base-change coherence commute these two decompositions; pasting mates yields $\theta'i_1^*b_F=b_C\theta$ and $\eta'i_0^*b_F=b_N\eta$. Thus $a^*b_C\circ\kappa\circ b_F^{-1}$ is normalized at $1$ and equals $\kappa'$ by Step 10. Restriction at $0$ gives $\delta'b_C=b_N\delta$. This proves the etale-neighbourhood compatibility with exactly the linear map of Step 6.

Original uses: lem-amb-etale-adjoint-locality, lem-amb-unbounded-compact-support-comparisons, lem-weil-pbc-mate-pasting, det-sp-unique-right-adjoint.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md — Local construction and orientation-charts proof Step 3, etale locality.

### Original step 15 → lem-trf-section-coordinate-counit-normalization

For the standard pair the Rees calculation is $R[t,u]$ with $x_j=tu_j$. Identify $\omega_{p_d}$ and its affine-line base change by the adjoints of the specified Kummer-normalized coordinate-tower counits. The actual trace maps commute with arbitrary Noetherian base change. Transposing their equality and comparing right adjoints by their counits gives that the exceptional fibre comparison at $1$ is the identity in these orientations. For a section chart $e_i$, locality and fibre comparison commute by the pasting calculation of Step 14. Thus the unnormalized chart map $\lambda_i$ of Step 9 already restricts to $\theta_i$ when these orientations are used, so its correction $h_i$ is the identity. Consequently $\kappa$ is precisely the identity between the two pullbacks of the affine-space dualizing line in every such chart, as asserted.

Original uses: lem-amb-affine-space-top-trace, cor-amb-affine-space-adjunction, det-sp-unique-right-adjoint, lem-weil-pbc-mate-pasting, lem-amb-etale-adjoint-locality, lem-asd-etale-finite-twist-pullback.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md — Local construction, standard model; orientation-charts proof Step 3.

### Original step 16 → lem-trf-finite-ring-bundle-section-orientation

On a trivializing open of $N_s$, pull the inverse of the adjoint affine-space orientation to its zero section, obtaining $z^*\omega_\pi\to A_S(d)[2d]$. On overlaps two trivializations differ by an invertible linear change of coordinates. Linear trace invariance says their coordinate-tower counits agree after this change. Uniqueness of right adjoints compatible with counits gives equality of the adjoint orientations. After section restriction they are maps between shifted sheaves, so full faithfulness and sheaf-Hom gluing give the stated normal-bundle orientation for arbitrary finite $A$. Linear isomorphisms preserve it by exactly the same equality. For coefficients in the scope of the vector-bundle-purity theorem, that theorem defines its integration by these same affine traces; its inverse purity map therefore has the same local restrictions and agrees after gluing. When $d=0$ the standard adjunction is the identity and all coordinate calculations have no variables; the claimed identities follow. If $S$ is empty all maps are unique; if $A$ is the zero ring all module sheaves vanish, and the comparisons remain unique isomorphisms.

Original uses: def-asd-vector-bundle-zero-section, lem-amb-linear-trace-invariance, lem-amb-affine-space-top-trace, det-sp-unique-right-adjoint, lem-pur-sheaf-hom-cover-gluing, lem-weil-pbc-derived-single-fully-faithful, thm-amb-vector-bundle-purity.

Original source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md — Local construction and orientation-charts proof Step 4, linear normalization.

## Dry-run repairs

The first server preflight required bracketed notion citations inside each new statement, in addition to the complete stmt_deps fields. Added individually bracketed citations for every listed notion/comparison interface (the parser does not recognize a comma-separated list inside one bracket pair) and regenerated all verbatim quotes. This changes no mathematical assertion or search question. The server recorded existing incoming off-unit route warnings involving the old parent; no unrelated node was edited.
