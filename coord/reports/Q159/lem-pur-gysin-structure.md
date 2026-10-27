# Repair report: lem-pur-gysin-structure

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-gysin-structure.json`: original statement retained exactly; replaced the 9794-character proof with a four-step assembly of 1985 characters.
- `dag/nodes/sec-smooth-purity/lem-pur-zero-support-retraction-triangle.json`: statement, unsplit, no Mathlib match; geometric hypotheses, exact closed direct image and pushed support triangle (old steps 1-2).
- `dag/nodes/sec-smooth-purity/lem-pur-kummer-triangle-concentration.json`: statement, unsplit, no Mathlib match; units, all cohomology degrees, normalized derived isomorphism, constructibility and tensor-unit Tor interval (old steps 3-6).
- `dag/nodes/sec-smooth-purity/lem-pur-supported-class-evaluation-comparison.json`: statement, unsplit, no Mathlib match; conditional closed-support/exceptional comparison, supported Hom, evaluation and classes (old steps 7-9).

`citations.json` contains a verbatim quotation for every citation in every assembly step. `searches.jsonl` is the unaltered search-command log. `returned-node.json` preserves the complete baseline used for the repair. The auxiliary scripts and baseline are sandbox records, not project changes.

## Attachments

No exact attachment. The source search found `AlgebraicGeometry.Etale.gysin_structure_zeroSection` in `lean/WeilConjectures/EtaleCohomology/Purity/Smooth/GmRelativeKummer.lean:388` and its section-identification definition at line 343. I read its variables, conclusion and proof. It works with ordinary small-etale sheaves, the etale exceptional value, and the closed zero locus. This item fixes ordinary small-pro-etale modules and the separately transported exceptional value; the normalized comparison is part of the work rather than a literal specialization of the etale declaration. `lean/Sheaf/Paper/PurityGysinStructure.lean` states the actual item as `WeilConjectures.PurityFiniteSetting.gysin_structure`, but its proof is `sorry`. Neither supplies an exact finished declaration for attachment. No Lean file was written or compiled.

## WANTED

None. The current blueprint statement and proof and the supporting Stacks source passages are present. No new external source is used.

## Return repaired and scope

The return requested three or more independent obligations of comparable size, statement-only and unsplit, with the old argument preserved and the assembly at most 3000 characters. The three packages own respectively 2399, 3877 and 3518 characters of the old argument. None owns the whole proof. The first supplies a support-functor triangle, without an exceptional identification. The second computes any such restriction triangle, without an exceptional functor. The third is a conditional general closed-immersion comparison and evaluation theorem and contains no A1/Gm computation. They can be claimed independently because their full interfaces, including the hypotheses they assume, are stated. All have empty `proof`, empty `proof_deps`, null `proof_origin` and `status: unsplit`. No existing node other than the assigned item is changed. Its statement, Lean attachment and provenance are preserved. The earlier item had already separated the support adjoint from the transported exceptional value; this distinction is preserved throughout.

There were no retained node files or report in this sandbox at session start, only dispatcher markers. The mandated initial dry run exited with “no node files”. I copied the current shared node, which contains exactly the nine returned steps and their lengths, and archived it before editing. No earlier sandbox searches existed. The source node records the prior Q116 review and subsequent Lean statement; these records remain intact.

## Source and route

For the item and each new node I read the current `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-gysin-structure.md` and `.proof.md`, the chapter record and `dag/units/sk-prop-a1-kummer.json`. The first proof paragraph gives the localization/A1/Gm calculation, and the second gives supported Hom and global sections. I also read Stacks `literature/stacks-project/proetale.tex`, Tag 09BM (`lemma-closed-immersion-complement-retrocompact-exact`), whose exactness requires a retrocompact complementary open; and `literature/stacks-project/derived.tex`, Tag 08J5 (`remark-truncation-distinguished-triangle`), for canonical good truncations. These are supporting source passages, not claims that those tags alone prove an extracted node. The new nodes correctly cite the blueprint argument as their source. No forbidden alternative purity route is used. The only proof used above the new obligations is the original unit's relative A1/Gm route.

## Mathlib and duplicate searches

For each new id I ran the prescribed command with two distinct semantic phrasings, Loogle, source grep, and LeanSearch. Every node entry copies the exact tool, query and result from the real log. LeanSearch was rate-limited for the first node and is recorded as unavailable; it answered for the other two. The semantic replies for the first node concern structure-sheaf localization and underived Zariski module pushforward. For the second, the relevant hit is `DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`; I read `TStructure.lean:189` and `HomologySequence.lean:89`. These assume or detect cohomological support, but do not compute the restriction map, the Kummer normalization or the Tor unit. For the third, the generic truncation, cohomology and adjunction hits do not compare the two support/exceptional constructions. Thus no package is a one-line Mathlib specialization. There are zero Mathlib leaves.

Before creating the nodes I searched all DAG statements/titles and the whole imported blueprint with `tools/blueprint_refs.py search`, using “support retraction”, “Kummer triangle”, “supported class evaluation” and related broader words. The exact phrase searches return no blueprint equivalence. I read the relevant existing support, comparison, single-degree, Kummer and bottom-gluing statements. The new ids did not exist. Each new blueprint provenance is the assigned imported node, `via: []`, with the exact paragraph and old-step range; `same_as: []` means no existing full statement is equivalent. The item remains its own imported blueprint node.

## Not duplicates

lem-pur-zero-support-retraction-triangle vs lem-pur-support-localization-triangle: the existing result is the triangle on X and the bounded-below support adjunction; the new assertion verifies the finite affine-line hypotheses and gives its exact normalized image after Rp_* on Y.
lem-pur-zero-support-retraction-triangle vs lem-pur-retracted-support-localization-comparison: the existing result starts with a transported exceptional value and etale-origin input, and gives global-edge compatibility; the new result starts with the ambient kernel support adjoint B0, proves its pushed triangle without an exceptional identification, and is needed before constructibility is known.
lem-pur-zero-support-retraction-triangle vs lem-pur-affine-line-support-geometry: the existing result supplies only geometric Noetherian and quasi-compact hypotheses, not the support adjoint, derived composition or pushed triangle.
lem-pur-kummer-triangle-concentration vs prop-pur-gm-relative-kummer: the existing result computes P and Q; it does not compute the fiber of restriction or its canonically normalized derived isomorphism and Tor interval.
lem-pur-kummer-triangle-concentration vs lem-sf-derived-concentrated-single: the existing generic statement assumes single-degree concentration; the new result proves it from the relative Kummer triangle and fixes the boundary generator and tensor-unit Tor bound.
lem-pur-kummer-triangle-concentration vs thm-pur-affine-line-orientation: orientation identifies the actual Cartier/exceptional class and its invertibility; the new result computes an arbitrary restriction-triangle support fiber before exceptional comparison and asserts no separate Cartier equality.
lem-pur-kummer-triangle-concentration vs lem-pur-gysin-structure: the new statement never identifies its fiber with the transported exceptional object and has no supported-global-section conclusion; the item is the final combination of the three packages.
lem-pur-supported-class-evaluation-comparison vs lem-pur-closed-support-exceptional-comparison: the existing result supplies the representing-object comparison under bounded constructibility; the new conditional theorem also compares supported degree-two classes, shifted Hom and evaluation with explicit canonical formulas.
lem-pur-supported-class-evaluation-comparison vs lem-pur-supported-hom: the existing result stops at Hom_X(i_*A,K[2]); the new result passes to the actual exceptional value on Z and proves the evaluation-to-sections comparison with the counit normalization.
lem-pur-supported-class-evaluation-comparison vs lem-amb-closed-support-hom: that statement is an etale RHom/cone identity, with no pro-etale transported exceptional counit or evaluation formula.
lem-pur-supported-class-evaluation-comparison vs lem-pur-supported-bottom-gluing: that statement is a local-cohomology edge/gluing result for finite twists on X with a lower vanishing bound; the new result treats arbitrary K with a concentrated support value and identifies the relative exceptional adjunction and global evaluation on Z.
lem-pur-supported-class-evaluation-comparison vs lem-pur-retracted-support-localization-comparison: the existing theorem compares triangles and global-edge boundaries for a closed section of p; the new theorem requires no retraction, assumes the support value is already concentrated, and identifies supported Hom and its degree-zero evaluation through the exceptional counit.
lem-pur-supported-class-evaluation-comparison vs lem-weil-pbc-derived-single-fully-faithful: fully faithfulness supplies only derived Hom between singles, not comparison of support and exceptional functors or evaluation on global sections.

## Review by Q159

I checked the item against both paragraphs of the current blueprint and all three new statements against the old arguments they must now carry. In assembly step 1, the first new statement explicitly says A is finite, gives Noetherian Y,X,U and quasi-compact j, and identifies the pushed support-counit triangle with its restriction arrow. The hypotheses are exactly the finite affine-line datum in the unchanged item: Y separated finite type, n positive and divisible by the ramification index. This step does not borrow the separately transported exceptional functor.

In assembly step 2, I checked the second statement actually takes the triangle with that restriction arrow as a hypothesis, so it applies to the B0 just produced. It gives a derived isomorphism A_Y[0] to C0, not merely per-degree numerical ranks, and names its degree-zero map as delta^1 gamma. It separately asserts the tensor-unit Tor calculation and ctf membership. This supplies all of the third node's C0 hypotheses; shift by minus two preserves bounded constructibility of B0. The good truncation is canonical before choosing the generator; the generator then fixes the A_Y trivialization.

In assembly step 3, I read the full third statement: i must be a finite-type closed pair with quasi-compact complement and K bounded below. The zero section meets these hypotheses by step 1, and F is a sheaf in degree zero. The third statement assumes both the derived constant identification and ctf membership of C0, supplied by step 2, so there is no circular use of purity or exceptional constructibility. It states the precise counit equation, and its Hom formula passes through the support adjunction on A_Y[-2], which has its explicit constant etale-origin witness. The map phi[2] is an isomorphism; applying H^m and derived tensor preserves the concentration, cohomology and Tor claims. The statement explicitly gives eta and evaluation, and their inverse composite has exactly the direction of the item's displayed identification. No arbitrary ambient exceptional adjunction is asserted.

In assembly step 4, I reopened `def-pur-affine-line-datum` and checked that the class is the coefficient-extended Kummer class of the coordinate in H^1(U,A(1)), with its etale-to-pro-etale comparison already fixed. I reopened `thm-pur-with-support-exactness`: its last sentence extends the sequence to bounded-below complexes and small-pro-etale finite-torsion coefficients, exactly the case used. The third new statement's boundary clause applies to every alpha and therefore to this kappa(t); eta(beta) is the asserted morphism, and evaluating it and applying the inverse composite gives beta. No stronger equality with an independently constructed Cartier class is smuggled into this assertion. The quotes in citations.json are literal substrings, with complete definition/exactness statements retained where appropriate.

For the new statements I tested the empty base (all sheaves and groups are zero, with the same identities), a geometric-point base (the triangle is the usual H^0 cancellation and Kummer H^1-to-supported-H^2 isomorphism), and a disconnected base (constant rank-one means rank one on each component; evaluation uses all locally constant coefficients on site objects, not only constant scalars). The cochain shift is H^m(B0[2])=H^{m+2}(B0). The exact sequence yields vanishing for negative degrees, degrees zero/one and all degrees at least three separately. The Tor interval is proved via the free coefficient unit, so no false implication from constructibility alone is used. In the conditional comparison node no purity conclusion is asserted when its support-concentration hypothesis fails. All non-elementary assertions in the short assembly are now literal conclusions of cited nodes; the original proofs are retained below for the workers who will split those nodes. There is no proof step over 2000 characters in the item. The new nodes contain statements only, with no hidden proof sketches in the statements.

The corrections are exclusively the requested redistribution: nine steps become three independently claimable unsplit obligations, followed by the four-step assembly. I checked delivery-errors B1-B10 (self-contained statements, definitions, source/provenance, literal TeX, real searches and nonattachment), C1-C8 (coverage, actual cited conclusions and unchanged route), D1-D5 (different intermediate objects and a genuine multi-part split), and E1-E7 (hypotheses, shifts, objects and comparison formulas). The original target statement has no new dispute. Maintainer-only fields are retained from the baseline rather than set as a new review.

## Preserved argument and coverage map

The following are the original nine proof steps, copied verbatim rather than shortened. Their cited nodes and source places are retained too. This is the complete proof material handed to the future workers; the new node files themselves correctly carry statements only.

### Original step 1 -> lem-pur-zero-support-retraction-triangle

Use the finite stage of [def-pur-conventions] and the exceptional functor with the domains of [def-weil-exceptional-inverse-image]. Set $p:X\to Y$, $\pi=pj$ and $F=A_X(1)[0]$, with the pair $(s,j)$ and $\kappa(t)$ of [def-pur-affine-line-datum]. Its $e\mid n$ gives $N=n/e\geq1$, and [lem-pur-finite-kummer-level] identifies $A$ as a module with $(\mathbf Z/\ell^N\mathbf Z)^{ef}$, so $A$ is finite. Apply [lem-pur-affine-line-support-geometry] to the underlying finite-type $k$-scheme $Y$. It says that $Y,X,U$ are Noetherian, that $X,U$ are finite type over $k$, and that $j$ is quasi-compact. These are the support and closed-exactness hypotheses needed below.

Uses: def-pur-conventions, def-weil-exceptional-inverse-image, def-pur-affine-line-datum, lem-pur-finite-kummer-level, lem-pur-affine-line-support-geometry.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-gysin-structure.proof.md; first paragraph: affine-line datum; hypotheses of the closed-support construction made explicit.

### Original step 2 -> lem-pur-zero-support-retraction-triangle

In this step write $R s^!_0$ for the right derived functor of $M\mapsto s^{-1}\ker(M\to j_*j^*M)$ on $D^+$, as specified in [lem-pur-support-localization-triangle], and put $B_0=R s^!_0F$. This notation distinguishes it from the exceptional inverse image defined by etale transport; their comparison will be proved in step 7, after computing $B_0$. The localization lemma applies because $j$ is quasi-compact, $A$ is finite, and $F$ is a sheaf in degree zero. It gives a distinguished triangle $s_*B_0\to F\to Rj_*j^*F\to(s_*B_0)[1]$, with its first arrow the support-adjunction counit. By [lem-exc-proetale-closed-exact], $s_*$ is exact. On a complex this exactness gives $\mathcal H^q(s_*L)=s_*\mathcal H^q(L)$, since kernels and images commute with an exact functor. Hence $s_*$ preserves quasi-isomorphisms, and the comparison from its termwise functor to $Rs_*$ is an isomorphism. The termwise functor is triangulated by [lem-sf-exact-functor-derived-triangulated]. Apply $Rp_*$ to the triangle: [lem-pc-right-derived-functor-triangulated] gives preservation of triangles and shifts. This is the finite-level functor of [def-weil-derived-direct-image], constructed by K-injectives, which exist by [prop-pur-kinjective-resolutions-exist] on the larger-universe small skeletons of [def-weil-pbc-proetale-site]. The finite-level composition isomorphisms of [lem-weil-derived-direct-image-composition], with $ps=\mathrm{id}_Y$ and $pj=\pi$, identify $Rp_*s_*$ with the identity and $Rp_*Rj_*$ with $R\pi_*$. Thus, with $P=Rp_*F$ and $Q=R\pi_*A(1)_U$, we obtain $B_0\to P\xrightarrow{r}Q\xrightarrow{\delta}B_0[1]$. Here $r$ is derived restriction from $F\to Rj_*j^*F$. No exceptional-functor comparison is used to obtain this triangle.

Uses: lem-pur-support-localization-triangle, lem-exc-proetale-closed-exact, lem-sf-exact-functor-derived-triangulated, lem-pc-right-derived-functor-triangulated, def-weil-derived-direct-image, prop-pur-kinjective-resolutions-exist, def-weil-pbc-proetale-site, lem-weil-derived-direct-image-composition.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-gysin-structure.proof.md; first paragraph through the distinguished triangle on Y.

### Original step 3 -> lem-pur-kummer-triangle-concentration

By [prop-pur-gm-relative-kummer](1), the unit $A_Y(1)[0]\to P$ is an isomorphism. By (2), the restriction of this unit along $j$ is the unit $A_Y(1)\to\mathcal H^0(Q)$ and is an isomorphism; this is exactly the equivalence with restriction composed with $p^*$ stated in that clause. Hence $\mathcal H^0(r)$ is an isomorphism. The same proposition gives $\mathcal H^1(Q)\cong A_Y$, with $1$ sent to the edge image of $\kappa(t)$, and $\mathcal H^m(Q)=0$ for $m\geq2$. There is also no negative cohomology of $P$ or $Q$: [lem-weil-pbc-dplus-injective-representative](1),(2) represents either input sheaf by a K-injective resolution zero below degree zero, and direct image applied termwise remains zero there. The module category is Grothendieck by [prop-pur-kinjective-resolutions-exist], and [lem-sp-grothendieck-enough-injectives] supplies enough injectives. Thus $P$ has cohomology only in degree zero and $Q$ only in degrees zero and one.

Uses: prop-pur-gm-relative-kummer, lem-weil-pbc-dplus-injective-representative, prop-pur-kinjective-resolutions-exist, lem-sp-grothendieck-enough-injectives.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-gysin-structure.proof.md; first paragraph: units, Kummer generator, and all vanishing degrees.

### Original step 4 -> lem-pur-kummer-triangle-concentration

Use [lem-sf-derived-homology-long-exact] on the triangle of step 2. For $m<0$, the exact segment $\mathcal H^{m-1}(Q)\to\mathcal H^m(B_0)\to\mathcal H^m(P)$ has zero outer terms, so $\mathcal H^m(B_0)=0$. In degrees zero and one the exact segment is $0\to\mathcal H^0(B_0)\to\mathcal H^0(P)\xrightarrow{\sim}\mathcal H^0(Q)\to\mathcal H^1(B_0)\to0$, giving $\mathcal H^0(B_0)=\mathcal H^1(B_0)=0$. Next, $0=\mathcal H^1(P)\to\mathcal H^1(Q)\xrightarrow{\delta^1}\mathcal H^2(B_0)\to\mathcal H^2(P)=0$ makes $\delta^1$ an isomorphism. For $m\geq3$, again $\mathcal H^{m-1}(Q)=\mathcal H^m(P)=0$, hence $\mathcal H^m(B_0)=0$. Therefore $\mathcal H^2(B_0)\cong A_Y$ via $\delta^1$, and all its other cohomology sheaves vanish. The argument uses kernels and images in the abelian category of module sheaves, not a conclusion from constant numerical ranks.

Uses: lem-sf-derived-homology-long-exact.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-gysin-structure.proof.md; first paragraph: displayed long exact sequence and degree-by-degree computation.

### Original step 5 -> lem-pur-kummer-triangle-concentration

Put $C_0=B_0[2]=R s^!_0A_X(1)[2]$. By [lem-sp-derived-cohomology-shift], $\mathcal H^m(C_0)=\mathcal H^{m+2}(B_0)$, so only $\mathcal H^0(C_0)$ survives, and step 4 identifies it with the constant rank-one module sheaf $A_Y$. Apply [lem-sf-derived-concentrated-single] with $r=0$ to obtain $C_0\cong\mathcal H^0(C_0)[0]\cong A_Y[0]$. The canonical identification with its degree-zero cohomology uses the good-truncation maps: for a representative $C_0^\bullet$, the maps $\tau_{\leq0}C_0^\bullet\to C_0^\bullet$ and $\tau_{\leq0}C_0^\bullet\to\mathcal H^0(C_0)[0]$ induce the identity on degree-zero cohomology and isomorphisms on all other (zero) cohomology groups, hence are quasi-isomorphisms. These are the truncations of [def-sbc-standard-tstructure-derived-category]: the second map is the quotient $\ker d^0\to\ker d^0/\operatorname{im}d^{-1}$ in degree zero and zero in negative degrees. Both maps are natural in chain maps and induce the identity on $\mathcal H^0$; the resulting isomorphism in the derived category is therefore the canonical one and does not use a chosen trivialization $\mathcal H^0(C_0)\cong A_Y$. Thus $C_0$ is concentrated in degree zero, with constant, and in particular lisse, rank-one cohomology.

Uses: lem-sp-derived-cohomology-shift, lem-sf-derived-concentrated-single, def-sbc-standard-tstructure-derived-category.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-gysin-structure.proof.md; end of first paragraph: displayed shift and constant cohomology; canonical good truncation as in Stacks 08J5.

### Original step 6 -> lem-pur-kummer-triangle-concentration

The constant finite module sheaf $A_Y$ is constructible by the single stratum $Y$ in [def-weil-finite-torsion-constructibility]. Moreover $A_Y[0]$ itself is K-flat in the definition of [def-weil-derived-tensor]: tensoring it with any acyclic complex is that same complex, by the mutually inverse degreewise maps $a\otimes x\mapsto ax$ and $x\mapsto1\otimes x$. Consequently for every degree-zero module sheaf $M$, $C_0\otimes_A^L M\cong A_Y[0]\otimes_A M[0]\cong M[0]$. This proves Tor amplitude $[0,0]$ by [def-weil-finite-tor-amplitude]. Together with step 5 it proves $C_0\in D^b_{ctf}(Y,A)$. The Tor conclusion comes from the explicit tensor unit, and is not deduced from bounded constructibility. This proves the constructibility and Tor claims for the support value $C_0$, before any comparison with the separately defined exceptional inverse image.

Uses: def-weil-finite-torsion-constructibility, def-weil-derived-tensor, def-weil-finite-tor-amplitude.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-gysin-structure.proof.md; end of first paragraph: constructibility and finite Tor amplitude, with tensor-unit verification.

### Original step 7 -> lem-pur-supported-class-evaluation-comparison

Compare $B_0$ with $B=Rs^!F$. The zero section is a closed immersion in the affine-line datum, $X,Y$ are finite type over $k$ and $j$ is quasi-compact by step 1, and $F=A_X(1)[0]$ is bounded below. Steps 5-6 give $B_0=C_0[-2]\cong A_Y[-2]$, which is bounded constructible by [def-weil-finite-torsion-constructibility]. Thus [lem-pur-closed-support-exceptional-comparison], applied to $i=s$ and $K=F$, gives a canonical isomorphism $\phi:B_0\xrightarrow{\sim}B$ with $\epsilon\circ s_*\phi=\epsilon_0$, where $\epsilon_0$ is the support counit and $\epsilon$ the relative exceptional counit. Put $C=B[2]$. The isomorphism $\phi[2]:C_0\xrightarrow{\sim}C$ carries the concentration, constant rank-one cohomology and finite-Tor conclusions of steps 5-6 to $C$, proving (1). The comparison lemma uses only the full bounded-below etale-origin class; no ambient adjunction on arbitrary pro-etale objects is invoked.

Uses: def-weil-finite-torsion-constructibility, lem-pur-closed-support-exceptional-comparison.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-gysin-structure.proof.md; first paragraph: comparison of the localization support value with the exceptional inverse image, after the relative A1/Gm calculation; expanded relative-adjunction argument.

### Original step 8 -> lem-pur-supported-class-evaluation-comparison

Apply [lem-pur-supported-hom] to $s$, $F=A_X(1)[0]$, and $a=2$. It gives the natural isomorphism
$$H^2_{s(Y)}(X,F)\cong\operatorname{Hom}_{D(X_{\mathrm{proet}},A)}(s_*A_Y,F[2]).$$
The support adjunction of [lem-pur-support-localization-triangle], applied to the bounded-below test object $A_Y[-2]$ and input $F$, gives
$$\operatorname{Hom}_X(s_*A_Y,F[2])\cong\operatorname{Hom}_X(s_*(A_Y[-2]),F)\cong\operatorname{Hom}_Y(A_Y[-2],B_0)\cong\operatorname{Hom}_Y(A_Y,C_0).$$
The first and last identifications apply the mutually inverse shift functors of [def-weil-abstract-derived-category]; exact termwise $s_*$ commutes with them by [lem-sf-exact-functor-derived-triangulated]. Now compose with postcomposition by $\phi[2]$ from step 7 to obtain $H^2_{s(Y)}(X,F)\cong\operatorname{Hom}_Y(A_Y,C)$ for the actual exceptional value $C=Rs^!F[2]$. The equality $\epsilon\,s_*\phi=\epsilon_0$ proved in step 7 says exactly that this composite uses the relative exceptional adjunction on the test object $A_Y[-2]$. This establishes the claimed comparison without treating the ambient support adjoint as the transported exceptional functor.

Uses: lem-pur-supported-hom, lem-pur-support-localization-triangle, def-weil-abstract-derived-category, lem-sf-exact-functor-derived-triangulated.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-gysin-structure.proof.md; second paragraph: supported cohomology to the Hom of the actual exceptional value, using the proved counit-compatible comparison.

### Original step 9 -> lem-pur-supported-class-evaluation-comparison

Step 7 and the canonical degree-zero truncation of step 5 identify $C$ with $\mathcal H^0(C)[0]$. By [lem-weil-pbc-derived-single-fully-faithful], $\operatorname{Hom}_{D(Y,A)}(A_Y[0],C)$ is therefore $\operatorname{Hom}_{\operatorname{Mod}(A_Y)}(A_Y,\mathcal H^0(C))$. Evaluation at $1$ identifies this last group with $\Gamma(Y,\mathcal H^0(C))$: a global section $v$ defines on each site object $V$ the $A_Y(V)$-linear map $a\mapsto a\,v|_V$, compatible with restrictions. Conversely, an $A_Y$-linear sheaf map sends $1|_V$ to the restriction of its value at the global section $1$, and hence sends every $a\in A_Y(V)$ to $a$ times that restriction. These constructions are inverse, including on disconnected objects of the site. Composing the inverse of step 8 with this identification gives the claimed canonical isomorphism $\Gamma(Y,\mathcal H^0(C))\cong H^2_{s(Y)}(X,A(1))$. The class $\kappa(t)$ of [def-pur-affine-line-datum] is a class in $H^1(U,A(1))$, and the pro-etale finite-torsion clause of [thm-pur-with-support-exactness] supplies its boundary $\beta=\partial\kappa(t)\in H^2_{s(Y)}(X,A(1))$. Apply the isomorphism of step 8 to $\beta$ to obtain a morphism $A_Y\to C$; under evaluation at $1$ it corresponds to the inverse image of $\beta$ in $\Gamma(Y,\mathcal H^0(C))$. This proves precisely the asserted correspondence of the boundary class. The statement asks for this correspondence, not for a further equality with a separately constructed Cartier class.

Uses: lem-weil-pbc-derived-single-fully-faithful, def-pur-affine-line-datum, thm-pur-with-support-exactness.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-gysin-structure.proof.md; second paragraph: global sections, supported boundary, and the resulting morphism.

## Preserved dependency statements for the extracted proof material

These verbatim statements keep the old citations reviewable; they are not new proof dependencies on the unsplit nodes.

### def-pur-conventions

Fix the global finite-field datum $(p,a,q,k_0,k)$ of [def-weil-finite-field-fiber], with $p$ prime, $a\geq1$, $q=p^a$, $k_0=\mathbf F_q$ and $k$ its fixed algebraic closure. Fix a prime $\ell\ne p$, a finite extension $E/\mathbf Q_\ell$ contained in the fixed algebraic closure $\overline{\mathbf Q}_\ell$, its valuation ring $\mathcal O_E$, a uniformizer $\varpi_E$, and $n\geq1$, and put
$$
 A=A_{E,n}=\mathcal O_E/\varpi_E^n
$$
as in [def-weil-l-adic-coefficient-extension].

For a $k$-scheme $Y$, use its small pro-etale site [def-weil-pbc-proetale-site]. The finite coefficient category $D^b_c(Y,A)$ is the bounded constructible category of [def-weil-finite-torsion-constructibility]. At integral coefficients use $D^b_c(Y,\mathcal O_E)$ of [def-weil-derived-complete-integral-detailed], with its derived completeness and a single cohomological interval for all finite reductions; its ambient coefficient ring sheaf is $\widehat{\mathcal O}_{E,Y}=\varprojlim_j(A_{E,j})_Y$ [def-weil-completed-integral-coefficients]. The rational category $D^b_c(Y,E)$ is the scalar localization of [def-weil-rationalization-karoubi], and $D^b_c(Y,\overline{\mathbf Q}_\ell)$ is the common-stage category of [def-weil-algebraically-closed-coefficients]. Use the finite-Tor subcategories $D^b_{ctf}(Y,\Lambda)$ for $\Lambda\in\{A,\mathcal O_E,E,\overline{\mathbf Q}_\ell\}$ exactly as in [def-weil-finite-tor-amplitude]: at the integral stage the Tor interval is uniform in all reductions, and at the two field stages $D^b_{ctf}=D^b_c$.

Use the derived pullback, tensor product and internal Hom of [def-weil-derived-pullback-tensor-hom], on the domains specified there, and the cohomology sheaves $\mathcal H^r$ of [def-weil-derived-cohomology-sheaves]. For a separated finite-type $k$-morphism $f:X\to Y$ between finite-type $k$-schemes [def-weil-proper-morphism, def-weil-finite-type-morphism], use the finite-level compact-support direct image $Rf_!$ of [def-compact-support-direct-image-detailed], its higher-coefficient constructions of [def-weil-integral-rational-qbar-compact-support], and the constructible exceptional inverse image $Rf^!$ of [def-weil-exceptional-inverse-image], with the adjunction $Rf_!\dashv Rf^!$ on the bounded constructible categories specified in that definition. Use the exchange and projection maps of [def-exchange-projection], on its stated domains and with its specified comparison data. These conventions name the functors and maps; preservation and invertibility assertions are the separate statements about them.

Let $\Lambda_Y$ denote the coefficient unit: $(A_{E,n})_Y$ in degree zero at finite level, $\widehat{\mathcal O}_{E,Y}$ at the integral level, and its rationalized or common-stage image at the field levels. Use the coefficient twists of [def-coefficient-twists-detailed] for every $m\in\mathbf Z$:
$$
 K(m)=K\otimes^L_{\Lambda_Y}\Lambda(m)_Y.
$$
Here $\otimes^L_{\Lambda_Y}$ is the derived tensor product of sheaves of $\Lambda_Y$-modules exactly as specified in [def-coefficient-twists-detailed] (over the completed sheaf $\widehat{\mathcal O}_{E,Y}$ at the integral level); for $\Lambda\in\{E,\overline{\mathbf Q}_\ell\}$ it is formed on an integral representative, as there. Smooth of relative dimension $d\geq0$ has the meaning of [def-sbc-smooth-morphisms]. Statements and constructions in the finite-coefficient part of the purity chapter are made for $\Lambda=A$; the $\mathcal O_E,E,\overline{\mathbf Q}_\ell$ versions are the derived-complete, rationalized and common-stage coefficient transports specified in the chapter's transport section.

Use the canonical Weil structures on the twists of [def-weil-frobenius-coefficient-twists]. The geometric-Frobenius normalization on the coefficient line over $\operatorname{Spec}k$ is the scalar action of [lem-pur-twist-frobenius-scalar]: $q^{-1}$ on $\Lambda(1)$, $q^{-m}$ on $\Lambda(m)$, and $q^m$ on $\Lambda(-m)$ for $m\geq0$, compatibly with finite reduction and scalar extension.

For a separated finite-type $k$-scheme $Y$, with structure morphism $a_Y:Y\to\operatorname{Spec}k$, define
$$
 \omega_{Y,\Lambda}:=Ra_Y^!\Lambda_{\operatorname{Spec}k}.
$$
Here $Ra_Y^!$ is the constructible exceptional inverse image just specified; no exceptional-adjoint admissibility datum is added.

Source: {"document": "literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-purity-conv/def-pur-conventions.md", "place": "node def-pur-conventions, order 1889"}.

### def-weil-exceptional-inverse-image

Fix a prime $\ell$, a finite extension $E/\Ql$ with valuation ring $\mathcal
O_E$ and uniformizer $\varpi_E$, and an integer $n\in\mathbf Z_{\geq1}$, with
$A=A_{E,n}=\mathcal O_E/\varpi_E^n$ [def-weil-l-adic-coefficient-extension]. Use the global finite-field datum [def-weil-finite-field-fiber], with
$k$ the fixed algebraic closure of the finite field of characteristic $p$
and $\ell\ne p$, and put $S=\Spec k$. Let $X,Y$ be finite-type
[def-weil-scheme-morphism-properties] $S$-schemes, and let $f:X\to Y$ be a
separated finite-type $S$-morphism. Thus $X,Y$ are Noetherian [lem-weil-pbc-finite-type-over-noetherian]; the
Noetherian assertion is made in this field-base setting, not for an arbitrary
base on which $\ell$ is invertible. *No ambient datum is
assumed.* Let $f^{\times}:D(Y_{\mathrm{et}},A)\to D(X_{\mathrm{et}},A)$ be the
right adjoint of the etale compact-support functor
$Rf^{\mathrm{et}}_!=Rp_{\mathrm{et},*}j^{\mathrm{et}}_!$ attached to a
compactification, which exists unconditionally by Brown representability on
the ordinary etale derived categories of the Noetherian schemes $X,Y$ (the
etale exceptional adjoint [thm-amb-etale-exceptional-adjoint]). Use finite-torsion constructibility
[def-weil-finite-torsion-constructibility] and the compact-support direct image
[def-compact-support-direct-image-detailed]. On the small pro-etale sites
[def-weil-pbc-proetale-site], with $\nu_X,\nu_Y$ the comparison morphisms
[def-weil-pbc-site-comparison-morphism], *define*

$$
 Rf_n^!:=\nu_X^*\,f^{\times}\,R\nu_{Y,*}:
 D^+(Y_{\mathrm{proet}},A_{E,n})\longrightarrow D^+(X_{\mathrm{proet}},A_{E,n}),
$$

the etale right adjoint transported along the etale/pro-etale comparison.
Its bounded-below domain is justified independently of the restriction:
for $L\in D^{\geq a}(Y_{\mathrm{et}},A_n)$, place $L$ at all levels
$m\geq n$ by restriction of scalars $A_m\to A_n$, with identity
transitions, and put zero at levels $m<n$. This is a bounded-below
coefficient system. The uniform lower-bound assertion of
[lem-pur-etale-coefficient-system-adjoint], followed by evaluation at
$n$, puts $f_n^\times L$ in $D^{\geq a-c_f}$. Derived direct image
$R\nu_{Y,*}$ preserves a lower bound and $\nu_X^*$ is exact, so the
finite composite indeed has the displayed $D^+$ typing;
on $D^b_c(Y,A_{E,n})$, every object of which is of etale origin
[lem-sf-proetale-constructible-origin], $L\cong\nu_Y^*G$, the unit
$G\xrightarrow{\sim}R\nu_{Y,*}\nu_Y^*G$
[thm-weil-pbc-site-comparison] identifies this value with
$\nu_X^*f^{\times}G$. The ambient composite is defined first; its constructible preservation is
the separate property explained below, permitting the restriction

$$
 Rf_n^!:D^b_c(Y,A_{E,n})\longrightarrow D^b_c(X,A_{E,n}).
$$

For integral coefficients use $R_T=\widehat{\mathcal O}_{E,T}$
[def-weil-completed-integral-coefficients] and the category
[def-weil-derived-complete-integral-detailed]. The integral construction is
made on derived categories of actual coefficient systems, before asserting
its constructible typing. Write $\mathsf S_A(T_\tau)$, for
$\tau\in\{\mathrm{et},\mathrm{proet}\}$, for the abelian category of strict
systems of $(A_n)_T$-modules of
[lem-pur-coefficient-system-derived-comparison].

There is a derived reduction functor
$$\mathcal R_Y:D(\operatorname{Mod}(R_Y))\longrightarrow
D(\mathsf S_A(Y_{\mathrm{proet}})).$$
Compute it from one K-flat representative $P$ with flat terms [lem-pc-kflat-resolution]
by the strict system $P\otimes_{R_Y}(A_n)_Y$, with transitions
$1\otimes(A_{n+1}\to A_n)$, as in
[def-weil-integral-derived-reduction, def-weil-integral-reduction-tower].
This is a functor to the derived category of systems: termwise tensor
respects shifts, cones and chain homotopies; a quasi-isomorphism between
K-flat representatives becomes a quasi-isomorphism at every level
[lem-pur-derived-change-of-rings], hence of systems since their cohomology
is levelwise. The resolving-class theorem
[lem-pur-left-derived-from-kflat-class] therefore gives this functor and
its action on morphisms independently of the representative. It is
normalized: $P\otimes_{R_Y}(A_m)_Y$ is K-flat with flat
terms over $(A_m)_Y$ by
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback], so ordinary further
tensor computes its derived reduction. At $m\geq n$ the balancing
isomorphism sends $(x\otimes b)\otimes a$ to
$x\otimes q_{m,n}(b)a$, with inverse
$x\otimes a\mapsto(x\otimes1)\otimes a$.
For $r\geq m\geq n$, the two successive balancing maps send
$((x\otimes b)\otimes c)\otimes a$ to
$x\otimes q_{r,n}(b)q_{m,n}(c)a$, which is also the direct
balancing map after tensor reassociation, since
$q_{m,n}q_{r,m}=q_{r,n}$. This proves the quotient cocycle;
applying a chain map to $x$ commutes with both formulas, proving naturality. This is also the construction
of [def-weil-pbc-adic-coefficient-datum], retaining the finite-level
module actions instead of immediately forgetting them.

Let $G_{f,A}$ be the ordinary etale right adjoint on the derived category
of coefficient systems supplied by
[lem-pur-etale-coefficient-system-adjoint], with evaluation
$e_nG_{f,A}\cong f_n^\times e_n$. Apply the derived comparison of systems
[lem-pur-coefficient-system-derived-comparison] and form the functor
$$\mathcal T_f=\nu_{X,A}^*\,G_{f,A}\,R\nu_{Y,A,*}\,\mathcal R_Y.
$$
Let $U_X:\mathsf S_A(X_{\mathrm{proet}})\to
\operatorname{Tow}_{R_X}(X)$ forget to the strict system of $R_X$-modules
by the projections $R_X\to(A_n)_X$
[def-weil-integral-derived-restriction-of-scalars,
def-weil-pbc-adic-coefficient-datum]. This functor is exact, since its
kernels and cokernels have the same underlying sheaves levelwise, so
termwise application induces $DU_X$ on derived categories
[lem-sf-exact-functor-derived-triangulated]. Define the integral functor by
$$ Rf^!_{\mathcal O_E}=R\varprojlim\circ DU_X\circ\mathcal T_f.
$$
Here the inverse limit is the functor on $D(\operatorname{Tow}_{R_X}(X))$
computed by a K-injective tower resolution followed by termwise inverse
limit [lem-weil-pbc-ringed-strict-tower-homotopy-limit]. In particular its
input is an actual derived strict tower and every arrow is the image of an
arrow under the displayed composite of functors. This does not require a
lift of a diagram given only in the ordinary derived category.

Evaluation gives, naturally in $L$,
$$e_n\mathcal T_fL\cong\nu_X^*f_n^\times R\nu_{Y,*}L_n=Rf_n^!L_n,
\qquad L_n=L\otimes^L_{R_Y}(A_n)_Y.$$
Thus the object formula is
$$Rf^!_{\mathcal O_E}L=R\varprojlim_n\operatorname{Res}_n(Rf_n^!L_n).$$
For integral constructible $L$, its reductions are uniformly bounded below
and of etale origin [def-weil-derived-complete-integral-detailed,
lem-sf-proetale-constructible-origin]. The last clause of
[lem-pur-coefficient-system-derived-comparison] shows that
$R\nu_{Y,A,*}\mathcal R_YL$ is a bounded-below normalized system.
[lem-pur-etale-coefficient-system-adjoint] then supplies its normalized
exceptional image; exact inverse image preserves normalization. The
result, including $DU_X\mathcal T_fL$ as its coherent realization, is a
normalized tower in [def-coef-normalized-dvr-tower]. The effectivity
statement [lem-coef-normalized-dvr-effectivity] supplies its integral
reductions and derived completeness. Its finite-level constructibility
and common bounds follow from the locality argument below; consequently
the integral value lies in $D^b_c(X,\mathcal O_E)$. This constructs the
integral functor without using lem-coef-finite-exceptional or
prop-coef-integral-exceptional-adjoint as premises. Those downstream
statements describe its duality, adjunction and coefficient comparisons.
In particular [lem-coef-integral-residue-tor] puts the reductions of an
integral input in the finite-Tor domain of the former comparison.

For $E$-coefficients pass to scalar localization
[def-weil-rationalization-karoubi]: on an integral representative use
$Rf^!_{\mathcal O_E}$, and on a localized morphism $u\otimes a$ use
$Rf^!_{\mathcal O_E}(u)\otimes a$. For $\Qlb$-coefficients use the
common-stage category [def-weil-algebraically-closed-coefficients]: send
$(E,L)$ to $(E,Rf_E^!L)$ and a morphism represented over a common finite
extension $F$ to its image under $Rf_F^!$, using the scalar comparisons of
[lem-pur-etale-coefficient-system-adjoint] on the coefficient systems to
identify the source and target. Indeed $\mathcal O_F/\varpi_E^n\mathcal O_F$
is finite free over $A_{E,n}$; the displayed system comparison is coherent
in successive field extensions. Such finite-free tensor commutes with
finite direct sums, and hence with the derived limit here (as a functor
it is a finite direct sum after choosing a basis); the subsequence of
powers $\varpi_F^{e(F/E)n}$ is cofinal. More explicitly, after forgetting
to fixed completed coefficients the subsequence functor on strict towers
has an exact left adjoint that repeats the n-th object in the finite
block preceding its selected index. It therefore preserves K-injective
complexes: a map into its image from an acyclic complex is adjoint to a
map from the acyclic repeated-block complex, hence is null homotopic.
The ordinary inverse limits of a tower and this subsequence agree by
compatible families, so their K-injective computations of derived limit
agree naturally as well. The natural comparisons therefore
pass to the integral functors and then their scalar localizations. The
common-stage map is consequently independent of its representative.
lem-coef-rational-operations is a downstream identification of these
operations, rather than the construction premise for their map action.
Thus for $\Lambda\in\{\mathcal O_E,E,\Qlb\}$ define

$$
 Rf^!:D^b_c(Y,\Lambda)\longrightarrow D^b_c(X,\Lambda).
$$

For $K\in D^b_c(X,\Lambda)$ and $L\in D^b_c(Y,\Lambda)$, characterize the
resulting functor by the natural adjunction isomorphisms

$$
 \Hom_Y(Rf_!K,L)\cong\Hom_X(K,Rf^!L).
$$

The two defining properties of this functor are theorems, not hypotheses.
The adjunction isomorphism holds for every bounded-below $K$ of etale origin
(in particular every $K\in D^b_c(X,A_{E,n})$) and every bounded-below $L$,
with units and counits compatible with refinements of the compactification:
at the finite coefficient stage this is [thm-sf-ambient-adjoint-class] (the etale adjunction transported by the
compact-support comparison and the full faithfulness of $\nu^*$ on $D^+$).
The constructible typing and finite-Tor preservation
[def-weil-finite-tor-amplitude] are properties of
the ambient finite formula already defined above. We establish these properties directly from ordinary etale closed-support
and smooth-purity statements, before restricting the functor. The downstream
thm-sf-preservation-class is not a prerequisite. For arbitrary $Y$ here,
take a finite affine open cover $v_i:V_i\hookrightarrow Y$ and
put $u_i:X_i=f^{-1}(V_i)\hookrightarrow X$ and $f_i:X_i\to V_i$.
The needed target restriction of the ordinary etale adjoint follows from
the existing statements, not from source locality alone. For a
bounded-below $H$ on $X_i$ and $L$ on $Y$, the successive adjunctions give
$$
\begin{aligned}
\operatorname{Hom}(H,u_i^*f_n^\times L)
&=\operatorname{Hom}(u_{i,!}H,f_n^\times L)\\
&=\operatorname{Hom}(Rf_{!,n}^{\mathrm{et}}u_{i,!}H,L)\\
&=\operatorname{Hom}(v_{i,!}Rf_{i,!,n}^{\mathrm{et}}H,L)\\
&=\operatorname{Hom}(Rf_{i,!,n}^{\mathrm{et}}H,v_i^*L)\\
&=\operatorname{Hom}(H,f_{i,n}^\times v_i^*L).
\end{aligned}
$$
The exact derived open-extension adjunction is stated in
[lem-amb-etale-adjoint-locality], the middle compact-support composition
isomorphism is [lem-amb-etale-compact-comparisons] applied to
$f u_i=v_i f_i$, and the remaining adjunctions are
[thm-amb-etale-exceptional-adjoint]. These are natural bijections, so the
two bounded-below representing objects are canonically isomorphic.
On constructible inputs, use their etale origins and
[lem-sf-proetale-constructible-origin] to read the restrictions on the
pro-etale site: restriction of $\nu_X^*H$ to $X_i$ is
$\nu_{X_i}^*(H|_{X_i})$, since both are sheafification of the same
restricted inverse-image presheaf in
[def-weil-pbc-site-comparison-morphism], and these inverse images are exact.
In particular the value of the already defined ambient
composite restricts to the corresponding finite composite for $f_i$.
Here is the ordinary etale preservation argument on each such target open,
using only prerequisites which do not refer to this definition. Finite type
and [lem-weil-pbc-finite-type-over-noetherian] make $Y$, $X$, and their
open subschemes Noetherian [lem-weil-pbc-noetherian-open-subscheme-noetherian]. By [def-weil-finite-type-morphism], choose a
finite affine cover $V_i=\operatorname{Spec}B_i$ of $Y$ and a finite
cover of $X_i$ by affine $U=\operatorname{Spec}C$. Each $C$ is a finitely
generated $B_i$-algebra by [lem-weil-pbc-lft-affine-pairs]. Choose generators
$c_1,\ldots,c_{d_U}$. The surjection $B_i[t_1,\ldots,t_{d_U}]\to C$,
$t_r\mapsto c_r$, gives a closed immersion
$i_U:U\hookrightarrow P_U=\mathbf A^{d_U}_{V_i}$, by
[def-weil-closed-immersion, def-sbc-affine-space]. Write
$\pi_U:P_U\to V_i$ and $s_U:U\hookrightarrow X_i$, so that
$f_i s_U=\pi_U i_U$. Discard empty $U$ and empty $V_i$.
All these schemes are Noetherian, and the open complements in $P_U$
are quasi-compact. The projections are smooth of pure relative dimension
$d_U$ [sbc-lem-affine-space-smooth]. They are separated and finite type;
Nagata [thm-nagata-compactification] supplies the compactifications needed
for their ordinary etale adjoints.

Set $e_i=\dim V_i$. These are finite nonnegative integers on nonempty
charts [lem-kun-dimension-finite-type]. The Noetherian polynomial-dimension
formula [lem-sf-noetherian-polynomial-dimension] and its identification
with scheme dimension [lem-weil-pbc-spec-topological-krull-dimension-ring]
give $\dim P_U=e_i+d_U$. For the complementary open
$j_U:W_U\hookrightarrow P_U$, open-subspace dimension monotonicity
[lem-weil-pbc-open-subspace-dimension-monotone] gives
$\dim W_U\leq e_i+d_U$. Thus
[lem-sf-etale-direct-image-vanishing] gives
$$R^qj_{U,*}M=0\quad(q>c_U),\qquad c_U=2(e_i+d_U),$$
for every ordinary etale $A_n$-module sheaf $M$.
For a constructible sheaf $F$ on $W_U$, placed in degree zero,
[thm-dg-finite-type-constructibility] says that $Rj_{U,*}F$ has
constructible cohomology, so every $R^qj_{U,*}F$ is constructible.
Here $W_U$ and $P_U$ are finite type over $k$ and $A_n$ is finite and
annihilated by a power of $\ell$ invertible in $k$. These are precisely
the two hypotheses needed for [lem-exc-closed-amplitude] and
[prop-exc-closed-tor]. Consequently the ordinary etale closed adjoint
$i_U^\times$ carries constructible cohomological intervals $[r,t]$
into $[r,t+c_U+1]$, and it carries bounded constructible inputs of Tor
amplitude $[r,t]$ into bounded constructible outputs of Tor amplitude
$[r,t+c_U+1]$. Indeed choose the compactification
$U\xrightarrow{\mathrm{id}}U\xrightarrow{i_U}P_U$ in
[def-amb-etale-compact-support]; its compact-support functor is
$Ri_{U,*}=i_{U,*}$ by [lemma-weil-pbc-finite-direct-image-exact] and
[lem-weil-pbc-closed-immersion-finite]. Thus the adjoint of
[thm-amb-etale-exceptional-adjoint] is exactly the ordinary closed
adjoint used in those two bound statements, by its natural Hom bijections.
The Tor statement is taken from the theorem, not inferred by tensoring
an unproved projection-formula triangle.

By [thm-asd-smooth-tensor], the ordinary etale adjoint of $\pi_U$ is
$$\pi_U^\times L\cong\pi_U^*L\otimes_{A_n}L_U[2d_U],$$
where $L_U$ is an etale locally constant free rank-one $A_n$-sheaf.
Pullback preserves finite locally constant sheaves and their finite
stratifications [lemma-constructible-pullback-stratification,
lemma-constructible-pullback-constant]; it is exact
[prop-weil-pbc-inverse-image-modules-exact]. Tensor by $L_U$ is locally
tensor by $A_n$, hence exact, and preserves finite locally constant
strata after intersecting the finitely many input strata. Thus on
bounded constructible inputs the cohomological interval changes from
$[a,b]$ to $[a-2d_U,b-2d_U]$. For Tor bounds use
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]; on any slice, the
inverse-image functor is exact and tensor by the displayed rank-one
line has exact inverse given by its dual line. The Tor interval is
therefore also shifted by $-2d_U$. Equivalently test after restriction
to opens trivializing $L_U$, where this is the shift of the pullback
of a flat model [lem-sf-flat-model].

For completeness the required adjoint-composition identification is made
before the constructible restriction. For $H\in D^+(U_{\mathrm{et}},A_n)$
and $L\in D^+(V_{i,\mathrm{et}},A_n)$, the open adjunction and compact-support
composition [lem-amb-etale-adjoint-locality,
lem-amb-etale-compact-comparisons] give natural bijections
$$\begin{aligned}
\operatorname{Hom}(H,s_U^*f_i^\times L)
&\cong\operatorname{Hom}(s_{U,!}H,f_i^\times L)\\
&\cong\operatorname{Hom}(Rf_{i,!}s_{U,!}H,L)\\
&\cong\operatorname{Hom}(R\pi_{U,!}i_{U,*}H,L)\\
&\cong\operatorname{Hom}(H,i_U^\times\pi_U^\times L).
\end{aligned}$$
The last line uses the two ordinary etale adjunctions
[thm-amb-etale-exceptional-adjoint, lem-exc-closed-ambient]. Both
representing objects are bounded below: the ordinary finite adjoints
preserve a lower bound up to a finite shift, and for the right hand
object this also follows from smooth purity and the closed-support
bound. Hence Yoneda in $D^+$ identifies them. On a bounded constructible
input the bounds just proved for smooth then closed give
$$s_U^*f_i^\times L\in D_c^{[a-2d_U,\,b-2d_U+c_U+1]}
   =D_c^{[a-2d_U,\,b+2e_i+1]}.$$
For a bounded constructible input with Tor interval $[a,b]$, exactly the
same interval is a Tor bound by [prop-exc-closed-tor]. No previously
restricted exceptional functor is used in this calculation.

For nonempty $X_i$, put $D_i=\max_{U\subset X_i}d_U$. The finitely many
source charts give the common interval $[a-2D_i,b+2e_i+1]$ for $f_i^\times$.
Cohomology vanishing is detected on an open cover. To glue constructibility,
order this finite source cover, intersect each local finite stratification
with $U\setminus\bigcup_{U'\text{ earlier}}U'$, and use the resulting
finite locally closed constructible pieces. Their locally constant finite
module descriptions are inherited from the local stratifications. For
Tor amplitude restrict a tensor with an arbitrary degree-zero module
sheaf to these opens; restriction commutes with derived tensor by
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback], so vanishing is
again detected locally. The site comparison preserves constructibility
[lem-sf-proetale-constructible-origin] and preserves and reflects the
same Tor interval [lem-sf-comparison-tor-amplitude]. It therefore gives
these bounds for the finite composite on $X_i$ as well.

The target-open Hom calculation above now applies for arbitrary $Y$.
For input interval $[a,b]$, take the minimum of the finitely many lower
endpoints $a-2D_i$ and the maximum of the upper endpoints $b+2e_i+1$.
Repeat the source-cover gluing argument for the finite cover $(X_i)$.
This proves bounded constructible typing and finite-Tor preservation
without separatedness of $Y$. Every chart integer, dimension and bound
is independent of $n$. Thus the same intervals apply to all reductions
of an integral input, which is the missing boundedness and
constructibility premise needed for the integral restriction above.
Empty charts are discarded, and for empty $X$ all outputs are zero.
For nonempty $Y$ the dimension bound is finite, and
$e_i\leq\dim Y$ by open-subspace dimension monotonicity. With
$D=\max_iD_i$ the displayed uniform bound can consequently be widened to
$$[a,b]\longmapsto[a-2D,b+2\dim Y+1].$$
For empty $Y$ also $X$ is empty; no dimension of an empty scheme or
maximum over an empty cover is needed.

This is the ordinary etale smooth/closed route in Zheng,
arXiv:1006.3810, Proposition 3.16(2) and Proposition 2.29(2), made
explicit using the existing bound statements. It supplies an acyclic
prerequisite for the restriction. The named thm-sf-preservation-class
is only a downstream summary of these properties; it is not applied.
The conclusions are the analogues of clauses (2) and (3) of
[def-weil-exceptional-adjoint-admissibility]. Normalization and the
coherent realization of the integral output are supplied by the system
construction before its inverse limit, as above.

*Relation to the ambient datum.* The ambient exceptional right adjoint datum
[def-weil-ambient-exceptional-adjoint] is *not* assumed anywhere in this
definition, and it is false in general: for the structure morphism of an
elliptic curve over $\overline{\mathbf F}_p$ with $A=\mathbf F_r$ and $r\ne p$ the functor
$Rf_*=Rf_!$ has no right adjoint on $D(X_{\mathrm{proet}},A)$, nor on $D^+$
(rem:sf-ambient-counterexample in the six-functors chapter). At a finite coefficient stage, the optional ambient datum is attached to a
chosen compactification $c=(j,p)$: its right adjoint $G_c$ is adjoint to
$F_c=Rp_*j_!$ on the ordinary unbounded pro-etale derived categories.
Its comparisons for every refinement, including their unit, counit,
identity and composition equations, are part of that datum; they are not
inferred by extending an etale-origin comparison to all ambient inputs.
Suppose that datum holds and that this same $G_c$ satisfies clauses (2)
and (3) of [def-weil-exceptional-adjoint-admissibility]. Clause (2), with
its signed bounds and zero-interval convention, puts $G_cL$ in $D^b_c(X,A)$
for every $L\in D^b_c(Y,A)$. For such $L$ and every
$K\in D^b_c(X,A)$ compare the natural bijections
$$
 \operatorname{Hom}_X(K,G_cL)
 \cong\operatorname{Hom}_Y(F_cK,L)
 \cong\operatorname{Hom}_X(K,Rf_n^!L).
$$
The first is the assumed adjunction of the ambient datum. For the second,
$F_cK=Rf_{!,n}K$ at the same chosen compactification
[def-compact-support-direct-image-detailed], and the bounded-below
etale-origin adjunction is [thm-sf-ambient-adjoint-class]; bounded
constructible $K$ has that origin by [lem-sf-proetale-constructible-origin].
Both representing objects are in the full category $D^b_c(X,A)$, so
Yoneda identifies them naturally in $L$. Clause (3) restricts this
identification further to $D^b_{ctf}$. This conditional identification at
finite coefficients asserts neither the ambient datum nor its additional
integral or scalar-extension compatibility requirements; none is a premise
of the construction above, and no statement of this blueprint needs the
conditional identification.

Source: {"document": "literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-exceptional-inverse-image.md", "place": "node def-weil-exceptional-inverse-image, order 1489"}.

### def-pur-affine-line-datum

Fix the finite-field and coefficient datum of [def-pur-conventions], with $A=A_{E,n}=\mathcal O_E/\varpi_E^n$, $n\geq1$, and $\ell\neq p$. Let $Y$ be a separated finite-type $k$-scheme [def-weil-scheme-morphism-properties]. Assume $e=e(E/\mathbf Q_\ell)\mid n$ and put $N=n/e=n v_\ell(\varpi_E)\geq1$ and $m=\ell^N$, as in [lem-pur-finite-kummer-level]. In particular $m$ is invertible on every scheme over $Y$.

The affine-line datum consists of the following explicitly constructed objects. Set $X=\mathbf A^1_Y$ with projection $p:X\to Y$ as in [def-sbc-affine-space], and let $t\in\Gamma(X,\mathcal O_X)$ be its coordinate. The zero section $s:Y\to X$ is given over each affine open $\operatorname{Spec}R\subseteq Y$ by $R[t]\to R$, $t\mapsto0$. It is the closed immersion defined by the ideal $(t)$ [def-weil-closed-immersion]. Write $U=\mathbf G_{m,Y}=X\setminus s(Y)$ and $j:U\hookrightarrow X$ for the complementary open immersion [def-weil-open-immersion]; over $\operatorname{Spec}R\subseteq Y$ it is $\operatorname{Spec}R[t,t^{-1}]$. Also write $t$ for its restriction to the global unit $t\in\Gamma(U,\mathcal O_U)^\times$.

For $T=X$ or $U$, on the small pro-etale site [def-weil-pbc-proetale-site] use the roots-of-unity sheaf $\mu_{m,T}$ [def-pur-roots-of-unity-sheaf] and the tensor product of module sheaves [def-pur-sheaf-tensor-product]. Write
$$
\theta_T:A(1)_T\xrightarrow{\sim}\mu_{m,T}\otimes_{\mathbf Z/m\mathbf Z}A
$$
for the canonical identification of the coefficient twist [def-coefficient-twists-detailed] supplied by [lem-pur-finite-kummer-level]. Define the coefficient morphism
$$
\varphi_T:\mu_{m,T}\longrightarrow A(1)_T,\qquad u\longmapsto\theta_T^{-1}(u\otimes1_A).
$$
Here the multiplicatively written group $\mu_{m,T}$ is regarded as a $\mathbf Z/m\mathbf Z$-module.

For the Kummer boundary first work on the small etale site of $U$. On this site $\mu^{\mathrm{et}}_{m,U}$ means the kernel of the $m$-th power map on the units sheaf, and define $A(1)^{\mathrm{et}}_U=\mu^{\mathrm{et}}_{m,U}\otimes_{\mathbf Z/m\mathbf Z}A$ and $\varphi^{\mathrm{et}}_U(u)=u\otimes1_A$. Until the final comparison paragraph, abbreviate these etale sheaves by $\mu_{m,U}$, $A(1)_U$ and $\varphi_U$. The units sheaf $\mathbf G_{m,U}$ is $V\mapsto\Gamma(V,\mathcal O_V)^\times$ [def-sc-gm-torsor]. Use the exact Kummer sequence of [lem-amb-kummer-any-base], with exponent $m$ invertible on $U$,
$$
0\longrightarrow\mu_{m,U}\longrightarrow\mathbf G_{m,U}
\xrightarrow{z\mapsto z^m}\mathbf G_{m,U}\longrightarrow0.
$$
For etale cohomology [def-weil-pbc-etale-cohomology] let
$$
\delta_U:\Gamma(U,\mathcal O_U)^\times
=H^0(U_{\mathrm{et}},\mathbf G_{m,U})\longrightarrow
H^1(U_{\mathrm{et}},\mu_{m,U})
$$
be its connecting map, with the right-derived-global-sections convention of [def-weil-pbc-sites-and-cohomology] and [lem-weil-pbc-right-derived-universal-delta-functor]. Define
$$
\kappa_{\mathrm{et}}(t)=H^1(\varphi_U)(\delta_U(t))
\in H^1(U_{\mathrm{et}},A(1)_U).
$$
Thus coefficient extension is applied to the roots-of-unity sheaf and its cohomology class; no tensor product of the units sheaf over $\mathbf Z/m\mathbf Z$ is used.

Here is the equivalent torsor description, using torsors in [def-sc-gm-torsor] and their canonical classes in [lem-sc-torsor-h1]. Form the relative spectrum [lem-weil-pbc-affine-morphism-relative-spec]
$$
\mathcal T_t=\underline{\operatorname{Spec}}_U
\bigl(\mathcal O_U[T_0]/(T_0^m-t)\bigr).
$$
Its etale sheaf of sections consists of the units $r$ with $r^m=t$, with right action $r\cdot\zeta=r\zeta$ of $\mu_{m,U}$. Since $\mu_{m,U}$ is abelian, regard this as the left action required by [def-sc-gm-torsor]. This is a finite etale cover of degree $m$: on an affine open $\operatorname{Spec}R\subseteq U$, [lem-weil-pbc-monic-quotient-free] supplies the basis $1,T_0,\ldots,T_0^{m-1}$ of $B=R[T_0]/(T_0^m-t)$, and $T_0^{-1}=t^{-1}T_0^{m-1}$ makes $mT_0^{m-1}$ invertible. Consequently the derivative localization in [lem-weil-pbc-standard-etale-monic-derivative] is $B$ itself. Finite and etale have the meanings of [def-weil-finite-integral-morphism] and [def-weil-etale-morphism]. Local roots exist by exactness of the Kummer sequence, and two roots differ by the unique root of unity $r^{-1}r'$, so this action is a torsor action.

Extend its structure group along $\varphi_U$ by forming
$$
\mathcal T_{t,A}=\mathcal T_t\wedge^{\mu_{m,U}}A(1)_U
=\bigl((\mathcal T_t\times A(1)_U)/\mu_{m,U}\bigr)^\#,
$$
where the orbit presheaf is sheafified [def-weil-pbc-sheafification] and the action on pairs is $(r,a)\cdot\zeta=(r\zeta,a-\varphi_U(\zeta))$. This is the contracted product of [def-sc-contracted-product-presentation], an $A(1)_U$-torsor whose class is $\kappa_{\mathrm{et}}(t)$ by the coefficient-functoriality statement [lem-sc-etale-torsor-h1-functoriality]. To identify the root-torsor class with $\delta_U(t)$, use the canonical extension $0\to\mu_{m,U}\to E_{\mathcal T_t}\to\mathbf Z_U\to0$ specified in [lem-sc-torsor-h1]. Its map to the Kummer sequence sends a local generator $[r]$ to $r$ and sends $a\in\mathbf Z_U$ to $t^a$. The relation $[r\zeta]=[r]+\zeta$ and the equality $r^m=t$ make both squares commute, with identity on $\mu_{m,U}$. Naturality of connecting maps in [lem-weil-pbc-right-derived-universal-delta-functor] therefore sends the boundary of $1$ to $\delta_U(t)$. This specifies the equivalence of the two descriptions without interpreting a torsor as a module tensor product.

In the chapter's small pro-etale convention, let $\nu_U:U_{\mathrm{proet}}\to U_{\mathrm{et}}$ be [def-weil-pbc-site-comparison-morphism]. Identify $\nu_U^{-1}\mu^{\mathrm{et}}_{m,U}$ and $\nu_U^{-1}A(1)^{\mathrm{et}}_U$ with the pro-etale roots and twist sheaves above. The identical formulas for roots on etale objects give a morphism $\mu^{\mathrm{et}}_{m,U}\to\nu_{U,*}\mu_{m,U}$ and hence, by the comparison adjunction, a canonical morphism $\rho:\nu_U^{-1}\mu^{\mathrm{et}}_{m,U}\to\mu_{m,U}$. To check it is an isomorphism, choose an etale covering $\{U_i\to U\}$ and pro-etale module trivializations from [lem-pur-twist-sheaf-locally-free](1). Write $\zeta_i$ for the root corresponding to $1\in\mathbf Z/m\mathbf Z$; the trivialization sends a locally constant exponent $a$ to $\zeta_i^a$. For every etale $V\to U_i$, degree-zero comparison in [lem-cbc-abelian-etale-proetale-cohomology-comparison], together with [lem-sf-comparison-pullback-exact](1), identifies the etale and pro-etale sections of the constant sheaf $\mathbf Z/m\mathbf Z$ on $V$. The two roots sheaves have identical sections $\{u\in\Gamma(V,\mathcal O_V)^\times:u^m=1\}$ on such $V$. Thus $a\mapsto\zeta_i^a$ also trivializes the etale roots sheaf. Pulling this trivialization back, using preservation of constant finite coefficients, identifies $\rho$ over $U_i$ with the identity of the constant $\mathbf Z/m\mathbf Z$-module. It is consequently an isomorphism. On overlaps write $\zeta_j=\zeta_i^{a_{ij}}$ for the uniquely determined locally constant $a_{ij}\in(\mathbf Z/m\mathbf Z)^\times$. Coordinates change by $a\mapsto a_{ij}a$ on the roots and by $b\mapsto a_{ij}b$ on their tensor products with $A$. The maps $\zeta_i^a\otimes b\mapsto ab$ identify the etale and pro-etale tensor twists on each $U_i$; on overlaps both have the same transition $a\mapsto a_{ij}a$ on the root coordinate (and hence the same induced transition on the tensor product), so these local identifications glue. Compose the resulting identification of $\nu_U^{-1}A(1)^{\mathrm{et}}_U$ with the pro-etale tensor twist with $\theta_U^{-1}$. Since $u=\zeta_i^a$ maps to $a\cdot1_A$ in each tensor trivialization, this also identifies the two coefficient morphisms. Define $\kappa(t)\in H^1(U_{\mathrm{proet}},A(1)_U)$ as the image of $\kappa_{\mathrm{et}}(t)$ under the canonical comparison isomorphism [lem-cbc-abelian-etale-proetale-cohomology-comparison]. Finally set $R^rs^!(-)=\mathcal H^r(Rs^!(-))$, using [def-weil-exceptional-inverse-image] and [def-weil-derived-cohomology-sheaves], and use the supported cohomology $H^q_{s(Y)}(X,-)$ of [def-pur-support-cohomology].

Source: {"document": "literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-purity-conv/def-pur-affine-line-datum.md", "place": "node def-pur-affine-line-datum, order 1892"}.

### lem-pur-finite-kummer-level

Fix the finite-field datum and $A=A_{E,n}$ of
[def-pur-conventions]; write $e=e(E/\Ql)$ for the ramification
index of $E/\Ql$ and assume that $e\mid n$. With $v_\ell$ normalized
by $v_\ell(\ell)=1$ (so that $v_\ell(\varpi_E)=1/e$), put

$$
N=n\cdot v_\ell(\varpi_E)\in\mathbf Z_{\geq1},
$$

the smallest exponent with $\ell^N\cdot A=0$; here $N=n/e$, and
$\varpi_E^n\mathcal O_E=\ell^N\mathcal O_E$, so that
$A=\mathcal O_E/\varpi_E^n\cong\mathcal O_E/\ell^N\mathcal O_E\cong (\mathbf Z/\ell^N\mathbf Z)^{ef}$
with $e=e(E/\Ql)$ the ramification index and $f=[\mathcal O_E/\varpi_E:\mathbf F_\ell]$ the residue degree,
is free of finite rank as a $\mathbf Z/\ell^N\mathbf Z$-module. Then there is a canonical isomorphism
of finite-torsion module sheaves on the small pro-etale site of any scheme
$T$ on which $\ell$ is invertible,

$$
A(1)_T\xrightarrow{\ \sim\ }\mu_{\ell^N,T}\otimes_{\mathbf Z/\ell^N}A,
$$

where $A(1)_T$ is the finite-level twist of
[def-coefficient-twists-detailed], $\mu_{\ell^N,T}$ is the etale sheaf of
$\ell^N$-th roots of unity, and $\otimes$ is over
$\mathbf Z/\ell^N\mathbf Z$. The isomorphism is compatible with the
derived tensor product and with base
change.

Source: {"document": "literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-purity-conv/lem-pur-finite-kummer-level.md", "place": "node lem-pur-finite-kummer-level, order 1890"}.

### lem-pur-affine-line-support-geometry

Let $k$ be a field [def-weil-field] and let $Y$ be a scheme of finite type over $k$ [def-pc-scheme, def-weil-finite-type-morphism]. Put $X=\mathbf A^1_Y$ with projection $p:X\to Y$ [def-sbc-affine-space]. Let $s:Y\hookrightarrow X$ be the zero section, defined on each affine open $\operatorname{Spec}R\subset Y$ by the quotient $R[t]\to R$, $t\mapsto0$ [def-weil-closed-immersion]. Let $U=X\setminus s(Y)$ with its open subscheme structure and let $j:U\hookrightarrow X$ be the inclusion [def-weil-open-immersion]; over $\operatorname{Spec}R$ this is the principal open $\operatorname{Spec}(R[t]_t)$, also denoted $\operatorname{Spec}R[t,t^{-1}]$. Then $X$ and $U$ are of finite type over $k$, the three schemes $Y,X,U$ are Noetherian, and $j$ is quasi-compact. Here Noetherian means locally Noetherian [pqf-def-locnoeth] and quasi-compact, with quasi-compactness of schemes and morphisms understood as in [def-weil-finite-type-morphism].

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-gysin-structure.proof.md", "place": "First paragraph, the closed-open affine-line pair before applying the support localization triangle. Agent-extracted geometric prerequisite; Stacks Morphisms Tag 01T6 (lemma-finite-type-noetherian) and Properties Tags 01OW (lemma-locally-Noetherian), 01OX (lemma-immersion-into-noetherian) supply the Noetherian and quasi-compact inputs."}.

### lem-pur-support-localization-triangle

Let $s:Z\hookrightarrow X$ be a closed immersion of schemes with complementary open immersion $j:U\hookrightarrow X$, and assume that $j$ is quasi-compact [def-pur-flasque-support, def-weil-finite-type-morphism]. Fix a finite commutative ring $\Lambda$. Work with all module sheaves over the constant coefficient sheaves on the small pro-etale sites and their ordinary derived categories [def-weil-pbc-proetale-site, def-weil-pbc-proetale-operations], without a constructibility condition. Let $K$ be a bounded below complex, or its object in $D^+(X_{\mathrm{proet}},\Lambda)$ [def-weil-pbc-bounded-derived-subcategories]. Write $s^!M=s^{-1}\ker(M\to j_*j^*M)$ as in [def-pur-flasque-support], and let $Rs^!$ be its right derived functor on $D^+$, computed on bounded below complexes of injectives [lem-weil-pbc-right-derived-plus-injective].

The injective-resolution and cone construction of [def-pur-support-triangle] gives a distinguished triangle
$$
 s_*Rs^!K\longrightarrow K\longrightarrow Rj_*j^*K
 \longrightarrow (s_*Rs^!K)[1]
$$
in $D(X_{\mathrm{proet}},\Lambda)$. Here $s_*$ is exact and denotes also its termwise induced derived functor. The functor $Rs^!$ is right adjoint to this $s_*$ on the bounded below derived categories. Consequently any exceptional inverse image defined as a right adjoint to this same $s_*$ on these same categories is naturally identified with $Rs^!$, compatibly with the counit. The triangle is independent of the chosen injective resolution under the derived comparison maps, is functorial in $K$, and is compatible with etale base change in precisely the sense of [def-pur-triangle-meaning, def-weil-etale-morphism].

Source: {"document": "literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/lem-pur-support-localization-triangle.md", "place": "node lem-pur-support-localization-triangle, order 1933"}.

### lem-exc-proetale-closed-exact

Let $i:Z\hookrightarrow X$ be a closed immersion whose complementary open
immersion is quasi-compact. Then $i_*$ is exact on all pro-etale module
sheaves over a finite constant ring.

Source: {"document": "literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-closed-unit/lem-exc-proetale-closed-exact.md", "place": "node lem-exc-proetale-closed-exact, order 1855", "external": [{"document": "Stacks Project", "place": "Tag 09A9"}]}.

### lem-sf-exact-functor-derived-triangulated

Let $F:\mathcal C_1\to\mathcal C_2$ be an exact (additive, preserving finite limits and colimits) functor between abelian categories, with derived categories $D(\mathcal C_1)$, $D(\mathcal C_2)$ [def-weil-abstract-derived-category]. Applying $F$ termwise to complexes induces a functor $F:D(\mathcal C_1)\to D(\mathcal C_2)$ which is triangulated [def-weil-triangulated-category] (it commutes with the shift and carries distinguished triangles to distinguished triangles) and which carries a complex $A[n]$ concentrated in one degree to $F(A)[n]$.

Source: {"document": "literature/stacks-project/derived.tex", "place": "Derived Categories, Lemma Tag 015F (label lemma-right-derived-exact-functor: an exact functor $F$ has $RF$ everywhere defined, computed termwise, and $RF$ is an exact functor of triangulated categories)"}.

### lem-pc-right-derived-functor-triangulated

Let $\mathcal A$ and $\mathcal B$ be abelian categories [def-sp-abelian] with derived categories and K-injective resolutions. For an additive functor $F:\mathcal A\to\mathcal B$ [def-sp-left-exact-additive], its unbounded right derived functor $RF:D(\mathcal A)\to D(\mathcal B)$, constructed from K-injectives, has a natural commutation with integer shifts and carries distinguished triangles to distinguished triangles [def-weil-triangulated-category].

Source: {"document": "WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/Triangulated.lean", "place": "lines 94-99, instances CategoryTheory.Functor.rightDerivedFunctor.CommShift and CategoryTheory.Functor.rightDerivedFunctor.IsTriangulated"}.

### def-weil-derived-direct-image

Fix a prime $\ell$, a finite extension $E/\Ql$, an integer $n\in\mathbf
Z_{\geq1}$, and put $A=A_{E,n}$. Let $X,Y$ be schemes on which $\ell$ is
invertible, and let $f:X\to Y$ be a morphism
[def-weil-scheme-morphism-properties]; write $f_n$ for this morphism at
coefficient level $A_{E,n}$. On the small pro-etale sites
[def-weil-pbc-proetale-site], with derived pullback and internal
Hom notation [def-weil-derived-pullback-tensor-hom] and derived tensor
notation [def-weil-derived-tensor], the functor
$f_*:\Sh(X_{\mathrm{proet}},A)\to\Sh(Y_{\mathrm{proet}},A)$
[def-weil-proetale-module-direct-image] is left exact
[lem-weil-proetale-module-direct-image-left-exact]. At
finite level, choose a K-injective resolution [def-weil-pbc-kinjective-resolutions] and
define its total right-derived functor
[def-weil-pbc-proetale-operations] by

$$
 Rf_{*,n}=R(f_n)_*:D(X_{\mathrm{proet}},A_{E,n})
 \longrightarrow D(Y_{\mathrm{proet}},A_{E,n}).
$$

For a derived-complete integral [def-weil-derived-complete-integral-detailed]
complex $K\in D^b_c(X,\mathcal O_E)$, define

$$
 Rf_*K=
 R\varprojlim_n\operatorname{Res}_n Rf_{*,n}
 \bigl(K\otimes^L_{\mathcal O_E}A_{E,n}\bigr).
$$

Here $D(-,\mathcal O_E)$ and the restriction of scalars
$\operatorname{Res}_n$, applied termwise (it is exact
[lem-weil-restriction-of-scalars-exact]), are those of the completed
coefficient sheaf [def-weil-completed-integral-coefficients], and
$R\varprojlim_n$ is the derived limit [def-weil-derived-limit] in
$D(Y_{\mathrm{proet}},\mathcal O_E)$, which exists because countable products
of pro-etale module sheaves are exact
[lem-weil-proetale-countable-products-exact, lem-weil-derived-limit-existence].
The tower maps are induced by $A_{E,n+1}\twoheadrightarrow A_{E,n}$: the map
$K\otimes^L_{\mathcal O_E}A_{E,n+1}\to K\otimes^L_{\mathcal O_E}A_{E,n}$,
followed by the identification of $R(f_{n+1})_*$ of an
$A_{E,n}$-module complex with $R(f_n)_*$ of it
[lem-weil-proetale-direct-image-restriction-of-scalars]. The
finite-reduction comparison is the natural map

$$
 (Rf_*K)\otimes^L_{\mathcal O_E}A_{E,n}
 \longrightarrow
 Rf_{*,n}\bigl(K\otimes^L_{\mathcal O_E}A_{E,n}\bigr),
$$

adjoint [lem-weil-derived-scalar-extension-restriction-adjunction] to the
projection of $R\varprojlim$ onto its $n$-th term;

its being an isomorphism, and its compatibility with composition and scalar
extension, are separate comparison assertions, not part of this definition of
the derived direct image. Here $A_{E,n}$ and finite-level constructibility
are the finite-torsion coefficient data
[def-weil-finite-torsion-constructibility], and $\mathcal H^r$ is the
cohomology-sheaf functor [def-weil-derived-cohomology-sheaves]. For
$\Lambda=E$ use the rationalized category
[def-weil-rationalization-karoubi]; for $\Lambda=\Qlb$ use the common-stage
category [def-weil-algebraically-closed-coefficients].

Source: {"document": "literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-derived-direct-image.md", "place": "node def-weil-derived-direct-image, order 1468"}.

### prop-pur-kinjective-resolutions-exist

Let $\mathcal C$ be a site whose underlying category is small (its objects form a set) and $\mathcal O$ a sheaf of commutative rings on $\mathcal C$. Then the abelian category $\Mod(\mathcal O)$ of sheaves of $\mathcal O$-modules [def-weil-sheaf-of-modules-category] is a Grothendieck abelian category [def-sp-grothendieck-abelian] (it has all colimits, filtered colimits are exact, and $\bigoplus_{U\in\operatorname{Ob}\mathcal C}j_{U!}\mathcal O_U$ is a generator, where $\mathcal O_U$ is the restriction of $\mathcal O$ to the localized site $\mathcal C/U$ [def-pur-localized-ringed-site] and $j_{U!}\mathcal O_U$ is the sheafification [def-weil-presheaf-modules-sheafification] of the extension-by-zero presheaf of $\mathcal O$-modules $P_{\mathcal O_U}$ [def-weil-extension-by-zero-presheaf]), and every cochain complex $\mathcal M^\bullet$ of $\mathcal O$-modules [def-pc-cochain-complex-modules] admits a K-injective resolution [def-pur-kinjective-complex] $\mathcal M^\bullet\to\mathcal I^\bullet$ which is injective in every degree [def-sp-injective-resolutions], and which can be chosen functorially in $\mathcal M^\bullet$ (a functor $\mathcal M^\bullet\mapsto\mathcal I^\bullet$ on the category of complexes with a natural transformation from the identity whose components are such resolutions).

Source: {"document": "literature/stacks-project/sites-cohomology.tex", "place": "Section 07A5 (sites-cohomology-section-unbounded), first paragraph: Mod(O) is Grothendieck abelian (Modules on Sites, Section sites-modules-section-kernels, Lemmas sites-modules-lemma-j-shriek-flat, sites-modules-lemma-module-quotient-flat) and literature/stacks-project/injectives.tex Theorem 079P (injectives-theorem-K-injective-embedding-grothendieck)"}.

### def-weil-pbc-proetale-site

Fix a scheme $Y$ [def-pc-scheme]. Choose Grothendieck universes $\mathcal U\in\mathcal V$ and
a $\mathcal V$-small skeleton, as required by the size convention
[def-weil-size-convention], and form all categories below inside $\mathcal
V$. The site $Y_{\mathrm{proet}}$ [def-weil-pbc-small-proetale-site] has as objects the $\mathcal U$-bounded
weakly etale maps $U\to Y$, where a weakly etale map
[def-weil-weakly-etale-morphism] is flat with flat diagonal, and as morphisms the $Y$-morphisms. A family
$\{U_i\to U\}_{i\in I}$ is a covering if it is a pro-etale covering [def-weil-pbc-proetale-covering], i.e. an fpqc covering [def-weil-pbc-fpqc-covering]: every arrow is weakly etale and, for
every affine open $V\subset U$, finitely many affine opens $V_j\subset
U_{i_j}$ have images whose union is $V$.

For a commutative ring $A$, let $A_Y$ be the constant sheaf of rings [def-weil-pbc-constant-sheaf], the sheafification [def-weil-pbc-sheafification] of the constant
presheaf $U\mapsto A$ on $Y_{\mathrm{proet}}$. Let
$\Sh(Y_{\mathrm{proet}},A)$ be the abelian category of sheaves of
$A_Y$-modules [def-weil-sheaf-of-modules-category], and set

$$
 D(Y_{\mathrm{proet}},A)=D\bigl(\Sh(Y_{\mathrm{proet}},A)\bigr),
$$

using the derived category of cochain complexes
[def-weil-abstract-derived-category].

Source: {"document": "literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-semicon/def-weil-pbc-proetale-site.md", "place": "node def-weil-pbc-proetale-site, order 662"}.

### lem-weil-derived-direct-image-composition

Fix a prime $\ell$, a finite extension $E/\mathbf Q_\ell$ with valuation ring $\mathcal O_E$, uniformizer $\varpi_E$, and $A_{E,n}=\mathcal O_E/\varpi_E^n$ for $n\geq1$. Let $X\xrightarrow f Y\xrightarrow g Z$ be morphisms of schemes on which $\ell$ is invertible. Use the finite derived direct images of [def-weil-derived-direct-image]. For the integral formula in that definition, specify its functorial realization as follows: form the strict reduction tower on a K-flat representative as in [def-weil-integral-reduction-tower], restrict each term to the completed coefficient sheaf [def-weil-completed-integral-coefficients], apply ordinary total derived direct image on the strict tower category, and then total derived inverse limit [lem-weil-pbc-ringed-strict-tower-homotopy-limit]. This chooses a functorial derived-limit realization; an arbitrary Roos triangle alone is not the meaning of the integral functor here.

There is a canonical natural isomorphism
$$c_{g,f}:R(gf)_*\xrightarrow{\sim}Rg_*Rf_*$$
with the following domains and codomains:
1. At finite level, on all of $D(X_{\mathrm{proet}},A_{E,n})$, valued in $D(Z_{\mathrm{proet}},A_{E,n})$.
2. Integrally, on the full subcategory of $D^b_c(X,\mathcal O_E)$ [def-weil-derived-complete-integral-detailed] consisting of $K$ with $Rf_*K\in D^b_c(Y,\mathcal O_E)$, valued in the ambient $D(Z_{\mathrm{proet}},\mathcal O_E)$.
3. Rationally [def-weil-rationalization-karoubi], on the scalar localization of the full subcategory in (2) whose objects also satisfy $R(gf)_*K\in D^b_c(Z,\mathcal O_E)$, valued in $D^b_c(Z,E)$.
4. In the common-stage category [def-weil-algebraically-closed-coefficients], on pairs $(E,K)$ with $K$ in (3), valued in $D^b_c(Z,\overline{\mathbf Q}_\ell)$. The domain is the full common-stage subcategory; the conditions are preserved on extending the coefficient field.
5. On the small etale site with any commutative ring $A$, on all of the ordinary unbounded $D(X_{\mathrm{et}},A)$, valued in $D(Z_{\mathrm{et}},A)$.

Under the canonical identity identifications the comparison is the identity if either map is an identity. For $h:Z\to W$, the two composites from $R(hgf)_*K$ to $Rh_*Rg_*Rf_*K$ agree whenever all intermediate integral applications are defined (and, at the rational and common stages, all displayed values are bounded constructible). It respects transport along automorphisms of the diagram; direct image along $\sigma$ identifies with inverse image along $\sigma^{-1}$.

Source: {"document": "literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/lem-weil-derived-direct-image-composition.md", "place": "node lem-weil-derived-direct-image-composition, order 1470"}.

### prop-pur-gm-relative-kummer

In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $\Lambda=A=A_{E,n}$, let $Y$ be a separated finite-type $k$-scheme,
and use the affine-line datum of [def-pur-affine-line-datum]: the
projection $p:\mathbf A^1_Y\to Y$, the zero section $s$, the open
complement $j:\mathbf G_{m,Y}\hookrightarrow\mathbf A^1_Y$, the composite
$\pi=pj:\mathbf G_{m,Y}\to Y$, the finite-level twist
$\Lambda(1)=\mu_{\ell^N}\otimes_{\mathbf Z/\ell^N}A$, and the Kummer class
$\kappa(t)\in H^1(\mathbf G_{m,Y},\Lambda(1))$ of the coordinate. Write
$R^m\pi_*=\mathcal H^m R\pi_*$ for the cohomology sheaves of
[def-weil-derived-cohomology-sheaves]. Then:

1. *(Acyclicity of the affine line.)* The units
$\Lambda_Y\to Rp_*\Lambda_{\mathbf A^1_Y}$ and
$\Lambda_Y(1)\to Rp_*\Lambda_{\mathbf A^1_Y}(1)$ are isomorphisms; so
$R^mp_*\Lambda(1)=0$ for $m>0$.
1. *(The Kummer generator.)* The unit
$\Lambda_Y(1)\to R^0\pi_*\Lambda(1)$ — equivalently, restriction along $j$
composed with the pullback $p^*$ — is an isomorphism, and the map
$$
\Lambda_Y\longrightarrow R^1\pi_*\Lambda(1),\qquad 1\longmapsto\kappa(t),
$$
sending $1$ to the image of $\kappa(t)$ under the edge map
$H^1(\mathbf G_{m,Y},\Lambda(1))=H^1(Y,R\pi_*\Lambda(1))\to
\Gamma(Y,R^1\pi_*\Lambda(1))$, is an isomorphism: $R^1\pi_*\Lambda(1)$
is free of rank one on $\kappa(t)$.
1. *(Vanishing above degree one.)* $R^m\pi_*\Lambda(1)=0$ for $m\geq2$.
1. *(Base change.)* For every morphism $g:Y'\to Y$ of separated
finite-type $k$-schemes, with base changes
$p':\mathbf A^1_{Y'}\to Y'$, $\pi':\mathbf G_{m,Y'}\to Y'$ and
$g':\mathbf G_{m,Y'}\to\mathbf G_{m,Y}$, the pullback of the Kummer class
is the Kummer class, $g'^*\kappa(t)=\kappa(t')$, and the base-change
morphisms
$$
g^*Rp_*\Lambda(1)\to Rp'_*\Lambda(1),\qquad
g^*R\pi_*\Lambda(1)\to R\pi'_*\Lambda(1)
$$
are isomorphisms.

The same base-change conclusion also holds for $g:\operatorname{Spec}\Omega\to Y$ a geometric point, without requiring $\operatorname{Spec}\Omega$ to be of finite type over $k$. Thus (1)–(3) can be checked on geometric fibres: over an algebraically closed field $\Omega$ the affine line has only constant $H^0$, while the punctured line has constant $H^0$, $H^1$ freely generated by $\kappa(t)$, and no higher cohomology.

Source: {"document": "literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/prop-pur-gm-relative-kummer.md", "place": "node prop-pur-gm-relative-kummer, order 1935"}.

### lem-weil-pbc-dplus-injective-representative

Let $\mathcal A$ be an abelian category with enough injectives (for example $\Ab(T_{\Et})$ or $\Mod(T_{\Et},R)$ for a scheme $T$ [lem-weil-pbc-module-sheaves-enough-injectives]), $D^+(\mathcal A)$ its bounded below derived category [def-weil-pbc-bounded-derived-subcategories] and $Q$ the localization functor from cochain complexes [def-weil-abstract-derived-category]. (1) If $K\in D^+(\mathcal A)$ and $n\in\mathbf Z$ are such that $\mathcal H^i(K)=0$ for all $i<n$, there are a complex $L$ of injective objects of $\mathcal A$ with $L^i=0$ for $i<n$ and an isomorphism $QL\cong K$ in $D^+(\mathcal A)$. (2) Every bounded below complex of injective objects of $\mathcal A$ is K-injective [def-weil-pbc-kinjective-resolutions]. In particular every object of $D^+(\mathcal A)$ is isomorphic to $QI$ for a bounded below K-injective complex $I$.

Source: {"document": "literature/stacks-project/derived.tex", "place": "Lemma 013K (lemma-injective-resolutions-exist, line 6280), (2)-(3): a complex with bounded below cohomology has an injective resolution by a bounded below complex of injectives; Lemma 070J (lemma-bounded-below-injectives-K-injective, line 9688)"}.

### lem-sp-grothendieck-enough-injectives

Every Grothendieck abelian category [def-sp-grothendieck-abelian] has enough
injectives.
(*Source: the classical input; the sites used in this blueprint are
Grothendieck topoi, cf. Stacks Project, Cohomology on Sites, Section 12.24.*)

Source: {"document": "literature/blueprint/master/blueprint/sec-abelian-varieties/sk-prop-av-pqf-finite/lem-sp-grothendieck-enough-injectives.md", "place": "node lem-sp-grothendieck-enough-injectives, order 499"}.

### lem-sf-derived-homology-long-exact

Let $\mathcal C$ be an abelian category, $D(\mathcal C)$ its derived category [def-weil-abstract-derived-category] and $H^n:D(\mathcal C)\to\mathcal C$ the $n$-th cohomology functor (the cohomology of a representing complex). For every distinguished triangle $X\xrightarrow{u}Y\xrightarrow{v}Z\xrightarrow{w}X[1]$ there are connecting morphisms $\delta^n:H^n(Z)\to H^{n+1}(X)$ such that the sequence\n$$\n\cdots\to H^n(X)\xrightarrow{H^n(u)}H^n(Y)\xrightarrow{H^n(v)}H^n(Z)\xrightarrow{\delta^n}H^{n+1}(X)\to\cdots\n$$\nis exact.

Source: {"document": "literature/stacks-project/derived.tex", "place": "Derived Categories, Lemma Tag 05RS (label lemma-cohomology-homological: $H^0:D(\\mathcal A)\\to\\mathcal A$ is a homological functor) and Definition Tag 0147 (a homological functor gives the long exact sequence of a distinguished triangle)"}.

### lem-sp-derived-cohomology-shift

Let $\mathcal B$ be an abelian category with derived category $D(\mathcal B)$ and cohomology functors $H^n:D(\mathcal B)\to\mathcal B$ [def-weil-abstract-derived-category], and let $D^+(\mathcal B)\subset D(\mathcal B)$ be the bounded below derived category [def-weil-pbc-bounded-derived-subcategories]. For $k,a,a'\in\mathbf Z$ with $k+a=a'$ there is a canonical isomorphism

$$
 \tau^{k,a}_M:\ H^{a}(M[k])\xrightarrow{\ \sim\ }H^{a'}(M),
$$

natural in $M\in D(\mathcal B)$ (and so in $M\in D^+(\mathcal B)$); on a complex $M$ it is the identity of $\ker d/\operatorname{im}d$ under the equality of terms $M[k]^{a}=M^{a+k}$ (the sign $(-1)^k$ of the differential of $M[k]$ changes neither kernel nor image). These isomorphisms are compatible with $[0]=\mathrm{id}$ and with $M[k][l]=M[k+l]$.

Source: {"document": "literature/stacks-project/homology.tex", "place": "Homology, Definition 011G (definition-shift-cochain): $A[k]^n=A^{n+k}$, $d_{A[k]}=(-1)^kd_A$; Definition 011H (definition-cohomology-shift) and the paragraph after it: the identification $H^{i+k}(A^\\bullet)\\to H^i(A[k]^\\bullet)$, functorial and compatible with $[k][l]=[k+l]$; used in the derived category in Derived Categories, Section 05RR (derived.tex line 3610)"}.

### lem-sf-derived-concentrated-single

Let $\mathcal C$ be an abelian category, $D(\mathcal C)$ its derived category [def-weil-abstract-derived-category] with cohomology functors $H^n$, and let $K\in D(\mathcal C)$ and $r\in\mathbf Z$ with $H^n(K)=0$ for every $n\neq r$. Then $K\cong A[-r]$ in $D(\mathcal C)$ for an object $A$ of $\mathcal C$ (the complex with $A$ in degree $r$), and necessarily $A\cong H^r(K)$.

Source: {"document": "literature/stacks-project/derived.tex", "place": "Derived Categories, Remark Tag 08J5 (label remark-truncation-distinguished-triangle) applied twice: if $H^n(K)=0$ for $n\\neq r$, the maps $\\tau_{\\leq r}K\\to K$ and $\\tau_{\\leq r}K\\to\\tau_{\\geq r}\\tau_{\\leq r}K$ are quasi-isomorphisms and the last complex is $H^r(K)$ placed in degree $r$"}.

### def-sbc-standard-tstructure-derived-category

Let $\mathcal A$ be an abelian category and $D(\mathcal A)$ its derived category, with cohomology functors $H^i:D(\mathcal A)\to\mathcal A$ [def-weil-abstract-derived-category]. For $n\in\mathbf Z$ let $D(\mathcal A)^{\le n}$ (resp. $D(\mathcal A)^{\ge n}$) be the strictly full subcategory of objects $K$ with $H^i(K)=0$ for all $i>n$ (resp. for all $i<n$); equivalently, of objects isomorphic in $D(\mathcal A)$ to (the image of) a complex $K^\bullet$ with $K^i=0$ for $i>n$ (resp. $i<n$). The pair $(D(\mathcal A)^{\le0},D(\mathcal A)^{\ge0})$ is a t-structure on the triangulated category $D(\mathcal A)$ [def-weil-t-structure], the *standard* (or *natural*) t-structure, with $D(\mathcal A)^{\le n}=D(\mathcal A)^{\le0}[-n]$ and $D(\mathcal A)^{\ge n}=D(\mathcal A)^{\ge0}[-n]$. For a complex $K$ the truncation triangle of axiom (iii) is the image of the short exact sequence $0\to\tau_{\le0}K\to K\to K/\tau_{\le0}K\to0$, where $\tau_{\le0}K$ is the subcomplex $\cdots\to K^{-1}\to\ker(d^0)\to0\to\cdots$ of $K$, and $K/\tau_{\le0}K$ lies in $D(\mathcal A)^{\ge1}$.

Source: {"document": "literature/bbd-faisceaux-pervers_Asterisque-100-1982.pdf", "place": "Exemples 1.3.2 (i), p. 28 (la t-structure naturelle sur DA); the truncation triangle also in literature/stacks-project/derived.tex Remark 08J5 (remark-truncation-distinguished-triangle)"}.

### def-weil-finite-torsion-constructibility

For the global finite-field datum [def-weil-finite-field-fiber], fix a prime
$\ell\neq p$, a finite extension $E/\Ql$, a uniformizer $\varpi_E$ of its
valuation ring $\mathcal O_E$, an integer $n\in\mathbf Z_{\geq1}$, and a
scheme $Y$. On the small pro-etale site
[def-weil-pbc-proetale-site] $Y_{\mathrm{proet}}$, put

$$
  A_{E,n}=\mathcal O_E/\varpi_E^n.
$$

A sheaf of $A_{E,n}$-modules on $Y_{\mathrm{proet}}$ is *constructible* if
there is a finite disjoint partition $Y=\bigsqcup_{\nu=1}^N Y_\nu$ by locally
closed constructible subschemes [def-weil-scheme-morphism-properties], and
the restriction to each $Y_\nu$ is locally constant with finite
$A_{E,n}$-module stalks. For a derived complex, for every $i\in\mathbf Z$,
write $\mathcal H^i$ for its cohomology sheaves
[def-weil-derived-cohomology-sheaves]. Define

$$
 D^b_c(Y,A_{E,n})\subset D(Y_{\mathrm{proet}},A_{E,n})
$$

to be the full triangulated subcategory of complexes with finitely many
nonzero cohomology sheaves, all constructible.

Source: {"document": "literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-finite-torsion-constructibility.md", "place": "node def-weil-finite-torsion-constructibility, order 1454"}.

### def-weil-derived-tensor

Fix a scheme $Y$ and a commutative ring $A$, and use the small pro-etale site
[def-weil-pbc-proetale-site] $Y_{\mathrm{proet}}$, with its constant sheaf of rings $A_Y$, the abelian category of $A_Y$-modules and $D(Y_{\mathrm{proet}},A)$ as defined there. A complex $P$
of $A_Y$-modules is *K-flat* if tensoring it with every acyclic complex
preserves acyclicity, that is, it is K-flat in the sense of [def-pc-kflat-complex] for the ringed site $(Y_{\mathrm{proet}},A_Y)$. For complexes $K_1,K_2$ of $A_Y$-modules, choose a
quasi-isomorphism $P\to K_1$ with $P$ K-flat (one exists by [lem-pc-kflat-resolution]) and define

$$
 K_1\otimes_A^L K_2=P\otimes_A K_2
$$

(the total tensor complex [def-pc-tensor-complex-sheaves] over $A_Y$) regarded as an object of $D(Y_{\mathrm{proet}},A)$. For a ring map $A\to B$ and a complex $K_1$,
write $K_1\otimes_A^L B$ for derived tensor with the constant $B_Y$-module, regarded as an $A_Y$-module by restriction of scalars [def-pc-sheaf-restrict-scalars] along the induced map $A_Y\to B_Y$.

Source: {"document": "literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-semicon/def-weil-derived-tensor.md", "place": "node def-weil-derived-tensor, order 663"}.

### def-weil-finite-tor-amplitude

Fix a prime $\ell$, a finite extension $E/\Ql$ with valuation ring $\mathcal O_E$ and uniformizer $\varpi_E$, an integer $n\in\mathbf
Z_{\geq1}$, and a scheme $Y$ on which $\ell$ is invertible. Put $A=A_{E,n}=\mathcal O_E/\varpi_E^n$.
For an object $K\in D^b_c(Y,A)$, the bounded complexes with constructible cohomology sheaves of the
finite-torsion constructibility condition
[def-weil-finite-torsion-constructibility], say that $K$ has *finite Tor
amplitude* if it has Tor amplitude in $[a,b]$ [def-weil-proetale-tor-amplitude] for some integers $a\leq b$, that is, for every sheaf $M$ of
$A$-modules placed in degree zero, the cohomology sheaves [def-weil-derived-cohomology-sheaves] of the derived tensor product [def-weil-derived-tensor] satisfy

$$
 \mathcal H^r(K\otimes^L_A M)=0
 \qquad\text{for every }r\in\mathbf Z\setminus[a,b].
$$

Define $D^b_{ctf}(Y,A)$ as the full subcategory of $D^b_c(Y,A)$ of such objects; it is a full triangulated subcategory [def-weil-triangulated-subcategory] of $D(Y_{\mathrm{proet}},A)$ by [lem-weil-finite-ctf-triangulated].
For $K\in D^b_c(Y,\mathcal O_E)$, a derived-complete bounded constructible
complex [def-weil-derived-complete-integral-detailed], say that $K$ has
finite Tor amplitude if there are integers $a\leq b$ such that every derived reduction $K\otimes^L_{\mathcal O_E}A_{E,j}$ [def-weil-integral-derived-reduction],
$j\in\mathbf Z_{\geq1}$, has Tor amplitude in $[a,b]$, one interval
independent of $j$, and define $D^b_{ctf}(Y,\mathcal O_E)$ as the full subcategory of the triangulated category $D^b_c(Y,\mathcal O_E)$ [lem-weil-integral-constructible-triangulated] of such objects; it is a full triangulated subcategory by [lem-weil-integral-ctf-triangulated]. At
field coefficients the finite-Tor subcategories are, by definition, the
bounded constructible rationalized category
[def-weil-rationalization-karoubi] and its common-stage algebraically closed
coefficient category [def-weil-algebraically-closed-coefficients]:

$$
 D^b_{ctf}(Y,E):=D^b_c(Y,E),
 \qquad
 D^b_{ctf}(Y,\Qlb):=D^b_c(Y,\Qlb).
$$

The second equality is interpreted in the finite-stage triangulated
2-colimit. For $A_{E,n}$, finite Tor amplitude is an additional condition and
does not follow from bounded constructibility. At the integral stage it is
imposed by the displayed definition; a separate residue-field argument, which is a statement and not part of this definition,
proves that every object of the derived-complete constructible category
in fact satisfies it. This conclusion uses the compatibility of all
reductions of one integral object.

Source: {"document": "literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-finite-tor-amplitude.md", "place": "node def-weil-finite-tor-amplitude, order 1464"}.

### lem-pur-closed-support-exceptional-comparison

Fix the finite-field and finite-coefficient datum of [def-pur-conventions]: $k$ is the fixed algebraic closure of a finite field of characteristic $p$, $\ell\ne p$, $E/\mathbf Q_\ell$ is finite, $\varpi_E$ is a uniformizer and $n\geq1$, with $A=A_{E,n}=\mathcal O_E/\varpi_E^n$. Let $Z,X$ be finite-type $k$-schemes and $i:Z\hookrightarrow X$ a closed immersion of $k$-schemes [def-weil-finite-type-morphism, def-weil-closed-immersion], with quasi-compact open complement $j:V\hookrightarrow X$ [def-weil-open-immersion]. Work with ordinary constant-$A$ module sheaves on the small pro-etale sites and their derived categories [def-weil-pbc-proetale-site, def-weil-pbc-proetale-operations]. For $K\in D^+(X_{\mathrm{proet}},A)$ [def-weil-pbc-bounded-derived-subcategories], let $B_0=Ri^!_0K$, where $Ri^!_0$ is the right derived functor on $D^+$ of $M\mapsto i^{-1}\ker(M\to j_*j^*M)$ [def-pur-flasque-support], with support-adjunction counit $\epsilon_0:i_*B_0\to K$. Assume that $B_0$ is bounded with intrinsically constructible cohomology, namely $B_0\in D^b_c(Z,A)$ in [def-weil-finite-torsion-constructibility].

Use $c=(\mathrm{id}_Z,i)$ as compactification [def-weil-compactifications-refinements], and let
$$B=Ri^!K=\nu_Z^*i_c^\times R\nu_{X,*}K$$
be the finite exceptional value of [def-weil-exceptional-inverse-image], where $i_c^\times$ is the ordinary etale compact-support right adjoint and $\nu_T$ is the comparison morphism [def-weil-pbc-site-comparison-morphism]. For each bounded-below object $T$ of etale origin [def-weil-pbc-etale-origin-witness], denote by
$$a_T:\operatorname{Hom}(T,B_0)\xrightarrow{\sim}\operatorname{Hom}(i_*T,K),\qquad e_T:\operatorname{Hom}(T,B)\xrightarrow{\sim}\operatorname{Hom}(i_*T,K)$$
the support adjunction of [lem-pur-support-localization-triangle] and the relative exceptional adjunction of [thm-sf-ambient-adjoint-class](2) at $c$, respectively; $i_*$ denotes its exact termwise derived functor. Both $B_0$ and $B$ are bounded below of etale origin. There is a unique isomorphism $\phi_K:B_0\xrightarrow{\sim}B$ such that, for every such $T$ and every $f:T\to B_0$,
$$e_T(\phi_K\circ f)=a_T(f).$$
In particular, writing $\epsilon=e_B(1_B)$, one has
$$\epsilon\circ i_*\phi_K=\epsilon_0.$$
All Hom groups are taken in the ordinary derived categories of the indicated pro-etale module sheaves.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-gysin-structure.proof.md", "place": "First paragraph, identification of the first support-triangle term with the exceptional inverse image. Agent-extracted comparison obligation, after the support value is computed; Stacks Categories Tag 001P (lemma-yoneda) is the representability input, and Pro-etale Tag 09BM (lemma-closed-immersion-complement-retrocompact-exact) is the closed-exactness input. These tags alone do not assert the etale/pro-etale comparison."}.

### lem-pur-supported-hom

Fix the finite coefficient ring $A=A_{E,n}$ of [def-pur-conventions].
Let $X$ be a scheme [def-pc-scheme], let $i:Z\hookrightarrow X$ be a
closed immersion [def-weil-closed-immersion], with complementary
open immersion $j:U\hookrightarrow X$ [def-weil-open-immersion].
Work on the small pro-etale
sites with constant coefficient sheaves $A_T$ and ambient derived categories
$D(T_{\mathrm{proet}},A)$ [def-weil-pbc-proetale-site], and let $i_*$ be
the underived module direct image [def-weil-proetale-module-direct-image].
For any bounded-below complex $F$ of $A_X$-module sheaves and every integer
$a$, there is an isomorphism, natural in $F$,
$$
H^a_Z(X,F)\;\cong\;
\operatorname{Hom}_{D(X_{\mathrm{proet}},A)}(i_*A_Z,F[a]),
$$
where the left side is the cohomology of derived supported sections
[def-pur-support-cohomology] and $i_*A_Z$ is placed in degree zero.
The shift uses the cochain convention $(F[a])^r=F^{r+a}$
[def-weil-abstract-derived-category]. No constructibility or finite-Tor
condition is imposed on $F$.

Source: {"document": "literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/lem-pur-supported-hom.md", "place": "node lem-pur-supported-hom, order 1940"}.

### def-weil-abstract-derived-category

Let $\mathcal A$ be an abelian category [def-sp-abelian]. A cochain complex $K$ of $\mathcal A$ consists of objects $K^r$, $r\in\mathbf Z$, and differentials $d^r:K^r\to K^{r+1}$ satisfying $d^{r+1}d^r=0$; a morphism of complexes is a family of morphisms $f^r:K^r\to L^r$ commuting with the differentials. Its $r$-th cohomology object is $H^r(K)=\ker d^r/\operatorname{im}d^{r-1}$, functorial in $K$. A quasi-isomorphism is a morphism of complexes $f$ such that $H^r(f)$ is an isomorphism for every $r$. The derived category $D(\mathcal A)$ is the localization $Q:\mathrm{CoCh}(\mathcal A)\to D(\mathcal A)$ of the category of cochain complexes at the quasi-isomorphisms (equivalently, of the homotopy category $K(\mathcal A)$ at the images of the quasi-isomorphisms), with morphism sizes taken in the chosen universe [def-weil-size-convention]. Since every $H^r$ inverts quasi-isomorphisms it factors uniquely through $Q$, giving the cohomology functors $H^r:D(\mathcal A)\to\mathcal A$ with $H^r\circ Q\cong H^r$. $D(\mathcal A)$ is additive and carries the triangulated structure [def-weil-triangulated-category] induced from complexes: the shift is $(K[1])^r=K^{r+1}$ with differential $-d_K$, and a triangle of $D(\mathcal A)$ is distinguished if it is isomorphic to the image under $Q$ of the cone triangle $K\xrightarrow{f}L\xrightarrow{i}C(f)\xrightarrow{-p}K[1]$ of a morphism of complexes $f$, where $C(f)^r=L^r\oplus K^{r+1}$ with differential $\begin{pmatrix}d_L&f\\0&-d_K\end{pmatrix}$ and $i$, $p$ the inclusion and the projection. With these, $D(\mathcal A)$ is a triangulated category and $Q$ commutes with the shifts. See [Stacks Project, Section 13.11](https://stacks.math.columbia.edu/tag/05RR), Definition 05RU.

Source: {"document": "literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-coherence/def-weil-abstract-derived-category.md", "place": "node def-weil-abstract-derived-category, order 633", "external": [{"document": "Stacks Project", "place": "Tag 05RR (Section 13.11), Definition 05RU, Lemma 05RT"}, {"document": "literature/stacks-project/derived.tex", "place": "Definition 014Q (distinguished triangles of K(A)), Definition derived-definition-cone (the cone), Section 13.11 (lines after \\section{Derived categories})"}]}.

### lem-weil-pbc-derived-single-fully-faithful

Let $\mathcal A$ be an abelian category [def-sp-abelian] with derived category $D(\mathcal A)$ [def-weil-abstract-derived-category]. Let $S:\mathcal A\to D(\mathcal A)$ send $A$ to the complex $A[0]$ concentrated in degree zero and a morphism $f$ to its degree-zero single-complex map. Then $S$ is fully faithful: for every $A,B\in\mathcal A$, the map $\operatorname{Hom}_{\mathcal A}(A,B)\to\operatorname{Hom}_{D(\mathcal A)}(A[0],B[0])$, $f\mapsto S(f)$, is bijective.

Source: {"document": "literature/stacks-project/derived.tex", "place": "Tag 06XS, lemma-negative-exts, part (2), degree zero; Mathlib FullyFaithful.lean lines 37 and 45."}.

### thm-pur-with-support-exactness

Let $X$ be a scheme, let
$i:Z\hookrightarrow X$ be a closed subscheme with open complement
$j:U\hookrightarrow X$, and let $F$ be a
torsion etale sheaf on the
small etale site of $X$. In the
notation of [def-pur-support-cohomology], there is a long exact
sequence

$$
\cdots\longrightarrow H^q_Z(X,F)\longrightarrow H^q(X,F)
\longrightarrow H^q(U,F)\longrightarrow H^{q+1}_Z(X,F)\longrightarrow\cdots,
$$

functorial in the pair $(X,X\setminus Z)$ and in $F$. The same
statement holds for bounded-below complexes with torsion cohomology in the
derived category of [def-weil-pbc-derived-categories], and on the
pro-etale site [def-weil-pbc-proetale-site] of $X$ for finite-torsion coefficients.
(Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.4;
the bounded-below and pro-etale extensions follow from the site argument below.)

Source: {"document": "literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/thm-pur-with-support-exactness.md", "place": "node thm-pur-with-support-exactness, order 1926", "external": [{"document": "Milne", "place": "(Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.3 and the exactness axiom of the etale site.) Step 1: the derived support object."}]}.

## Incomplete work and validation

The three new obligations are deliberately not split or formalized; their proofs are work for independent stage-1 workers, as the return requires. This delivery closes the re-split task only. Initial dry run: no node files, since this sandbox had only dispatcher markers. Server check and final dry-run/push results are recorded below once complete.
