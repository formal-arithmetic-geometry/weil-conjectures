## Worker report

Repair of the 2026-10-22 batch5 return: the former eight-step proof is divided into three independently claimable, statement-only nodes. The item statement is unchanged, byte for byte. The parent now has six assembly steps, 2200 characters in total (below 3000); none exceeds 2000 characters. No Lean file was written and no compiler, Lake or build command was run.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-gabber-global-snc-alteration.json`: same statement, short assembly, updated exact proof dependencies and split report.
- `dag/nodes/sec-six-functors-basics/lem-sfb-semilinear-sylow-snc-resolution.json`: statement; unsplit; no Mathlib match. A GIVEN equivariant smooth model is resolved through its good Sylow components. It does not assert existence of that model or any compactification or return to an arbitrary separated input scheme.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-constant-projective-graph.json`: statement; unsplit; no Mathlib match. Descends projectivity through finite constants, constructs the closed graph over a separated target, and carries the embedding and both projectivity conventions through arbitrary base change.
- `dag/nodes/sec-six-functors-basics/lem-sfb-open-smooth-snc-restriction.json`: statement; unsplit; no Mathlib match. Restricts an already constructed smooth projective SNC pair, including actual component ideals, intersection codimensions and local parameter equations.
- `citations.json`: a verbatim statement quote for every node cited by every step of the item.
- `report.md`: this report. Sandbox-only `repair.py`, `write_report.py`, `old-proof.json` and `searches.jsonl` are research records, not additional library files.

## Attachments

None. A search of `lean/WeilConjectures/` for the item id, theorem name and global SNC terminology found no exact completed declaration. The library-name declaration `AlgebraicGeometry.exists_gabber_global_snc_alteration` at `lean/Sheaf/AlgebraicGeometry/GabberGlobalSNCAlteration.lean:171` ends in `sorry` at line 197 and therefore cannot attach the item. New-child names were checked in both source roots; there is no declaration of these combined assertions.

## WANTED

None. ILO and the Stacks source used here are present locally.

## What was wrong and what changed

The returned proof put 7313 characters of geometric work on one item. The return specifically requests distribution, rather than shortening without new obligations. There are now three obligations, carrying the old Sylow-and-resolution argument (old Steps 4--5, about 1690 characters), graph/projectivity argument (projectivity portions of old Steps 6--7, about 1900 characters), and open smooth-SNC argument (old Step 8, 1320 characters). These have separate hypotheses and can be worked on independently; the graph lemma needs neither a group action nor a boundary, and open SNC restriction needs neither an alteration nor constants of prime-to-ell degree. The first two preliminary constructions already have their own nodes and remain cited in the parent. The remaining empty-case and field-degree calculations are assembly. All old arguments are retained verbatim below, with an allocation, rather than disappearing into a shorter paraphrase.

I also made a formerly implicit input explicit: finite purely inseparable degrees are products of p's by the EXISTING `lem-weil-pbc-purely-inseparable-pth-root-tower`; characteristic zero gives equality by the definition. Its field-tower statement was read, not confused with the definition of purely inseparability. The auxiliary Mathlib search found `IsPurelyInseparable.finrank_eq_pow` (Basic.lean:322--324), but no new node is needed because the existing tower statement supplies the calculation by multiplication of bases.

No statement dispute or source correction is needed. The lower-layer mathematical facts in the old proof are retained, not replaced by a different purity or trace route. No SGA source is used.

## Blueprint and duplicate searches

I read the chapter `sec-six-functors-basics`, the assigned unit `sk-thm-sf-ctf-stability`, the item and its provenance. `tools/blueprint_refs.py ancestor lem-sfb-gabber-global-snc-alteration` returns None: this is an added input, not an imported blueprint node. Each new node has `from.node = null`, `via` beginning with this item followed by its existing ancestry, and a precise place at the alteration/tame-boundary reduction of `det-thm-sf-ctf-stability-direct-images` proof (3). No chapter or unit was changed.

Whole-blueprint searches were run for `Sylow`, `graph`, `normal crossings`, `semilinear`, `strict normal`, `H-projective`, `quasi-projective`, and `purely inseparable`. The Sylow hits concern finite-module filtrations; graph hits concern Chow/compactification or correspondences; H-projective hits mostly define projectivity or concern curves; none states one of the new assertions. Whole-DAG statement searches (not merely proof-word hits) for Sylow resolution, projective graphs and open SNC restriction found the existing model, good-component and tame-resolution lemmas, general projectivity nodes, and special curve/log arguments. Their statements were compared with the new ones. The old item is not duplicated: every new node assumes a substantial intermediate object and omits other parts of the global construction.

## Mathlib searches

All new-node `mathlib_searches` entries are actual calls to the prescribed `batch2/msearch.py`; query text is unchanged from `searches.jsonl`. Each child has LeanFinder, Loogle and source grep, plus LeanSearch and a second semantic phrasing. The LeanSearch service rate-limited the first semilinear query, recorded as unavailable. Other queries ran. No unavailable search is recorded as no match.

For the Sylow-resolution child, returned arithmetic Frobenius, inertia/residue degree and unramified-residue-field lemmas concern ring or field extensions and do not construct a smooth SNC resolution of a scheme quotient. For graph projectivity, the hits give properness/separatedness of Proj and finite cancellation; none descends a projective-space embedding along constants and constructs its graph over an arbitrary separated target. The broader source grep finds Proj infrastructure rather than this assertion. For open SNC restriction, smooth chart/locality lemmas and `Scheme.Opens.stalkIso` supply parts, but no single theorem supplies component decomposition, intersections, codimension, Cartier/reduced ideals and the projective immersion together. The actual Smooth and Restrict sources were checked. Thus the three children remain unsplit, not Mathlib leaves. Item searches from its existing record are preserved.

## Review by NB

I performed the second reading myself under the direct-delivery brief; no other agent was started. The maintainer supplies the independent review.

Source for the item: ILO X, definition of an ell-prime alteration, Theorem 2.1 and its following definition of relative strict normal crossings (printed pp.148--149), and proof 2.3 Steps 1--3 (pp.150--152). These permit arbitrary separated finite-type X, not just integral X, and require the degree condition at every maximal point. The statement has kept exactly these clauses, the finite constant field extension and the relative smooth-intersection conclusion. The old source and current repository statement agree.

Source for the Sylow child: X 2.3 diagram (2.c) and Step 3. I read the statements of `lem-weil-pbc-sylow-subgroup-prime-index`, `lem-sfb-semilinear-sylow-good-components`, and `lem-sfb-tame-snc-quotient-resolution`. The first supplies a finite ell-group of index prime to ell. The second supplies F, a SEPARABLE K/F, an open-and-closed good-component quotient with ALL its generic degrees prime to ell, and an open-and-closed inverse image. The last permits a nonfaithful semilinear action and a disconnected smooth projective source and returns equality of generic residue fields and precisely the inverse image of q(|D|), not an unrelated larger auxiliary boundary. Restriction to the open-and-closed inverse image preserves the input relative SNC divisor. Since ell differs from the characteristic, the Sylow order is invertible in F. Surjectivity of q and h=dq give q(|D|)=d^{-1}C: for a quotient point x pick a preimage y; h(y) lies in C iff d(x) does, and invariance makes the condition independent of y. This proves the exact support used in the new child. I explicitly specified that v is an F-morphism, so the final map respects the chosen constant extension. Its statement assumes the entire equivariant model, so it is neither the item itself nor the stand-alone tame-quotient theorem.

Source for the graph child: Stacks `morphisms.tex`, `lemma-projective-permanence` (0C4Q), including its actual two-factor closed-graph construction, and the projectivity definitions (01W8). I compared the existing finite-projective-bundle, ample-base-to-H-projective, H-projective composition, projective-space base-change, closed-immersion base-change and properness statements. The finite extension is not assumed separable: its spectrum is finite; O on the affine point is ample (section 1); H-projective composition yields R in finite projective space over k. The graph is the pullback of the CLOSED diagonal of S, and i times id is the pullback of the embedding i. Their composite is closed in P^N_S. Pulling the embedding back along S' gives the identical N; P^N_S' is the bundle of O^(N+1), so the EGA convention and properness follow. No projective-bundle composition over a non-ample intermediate base is assumed. This is the full graph argument from the previous proof, including the convention check and its base change, assigned its own node.

Source for the open-restriction child: X 2.3 Step 1 and end of Step 3, and VIII 4.2.2(i). The relative-SNC definition and regular-boundary definition were opened, as were the smooth-relative-dimension permanence and open-etaleness statements. The open map is etale, hence smooth of relative dimension zero. Compose locally with a constant-relative-dimension chart of R/F and of each component intersection to get smoothness. Stalks at a point do not change under open restriction, so component ideals, parameter equations and codimension equations do not change. Nonempty open restrictions of the integral components remain integral and distinct (two such equal dense opens would force their closures to coincide). Cartier and radical ideals restrict to Cartier and radical ideals. For the embedding, R minus U is closed in projective space since R is closed there, and U is closed in its open complement. This yields the stated locally closed immersion. This combined argument is longer than a one-line assertion that smoothness is open; it is now an independently claimable statement.

Parent step 1 uses the statement of proper-pair radicial preparation: it supplies exactly the compactification, closed C with C intersect X equal Z, radicial constants, and r. The empty case takes degree 1 and the empty scheme. Step 2 uses the equivariant smooth-model statement: proper, normal, geometrically reduced B and its effective Cartier boundary are supplied by preparation, and it returns the simultaneous field/group model and all subgroup quotients required by the Sylow child. Step 3 uses the NEW Sylow child's statement with C replaced by r^{-1}C: all its group, finite-quotient and full-quotient hypotheses are present; its precise support identity gives E. Step 4 uses the EXISTING p-th-root tower in positive characteristic on both types of radicial field extension; each is finite purely inseparable and of the same characteristic as k. Products of field bases prove the numerical degree equalities and coprimality follows since ell is another prime. Surjectivity and maximal domination here compose the maps obtained in steps 1 and 3, without any extra geometric theorem. Step 5 uses the NEW graph child's arbitrary-base-change clause and the EXISTING surjective-base-change statement, applied to the actual inverse image fibre product P, not a set-theoretic factorization. Step 6 uses the NEW open-restriction statement, which explicitly provides all the smoothness, local ideals and boundary clauses, then the set equality C intersect X=Z and the already checked generic degree calculation. A dense open in a Noetherian finite-type scheme contains each generic point; thus all the source generic points lie in P and the local residue maps are the same ones. The citations file quotes exactly these node statements.

Small cases checked: trivial G and L, nonfaithful actions on K and Y, empty C, disconnected Y and B, and mixed generic degrees (discarding bad components is essential). The Sylow child never assumes that a prime-to-ell TOTAL degree makes each component degree prime to ell. In characteristic zero preparation is trivial on constants; in characteristic p its finite purely inseparable degree is a power of p. For the graph child, F=k and R empty work; S need not be quasi-projective and no ample sheaf on S is used. For the open child, U empty, U=R, E empty, intersections empty, a zero-dimensional component, and J empty all retain the prescribed conventions. No perfect-field hypothesis is introduced. I checked B1--B7: children are statement-only, introduce their objects, give definition citations or inline explanations, use single-escaped TeX, and name source places. I checked C1--C6 against every parent citation and E1--E7 against the hypotheses just listed. New-node statements are smaller independent obligations, not proof sketches; no proof steps or hidden definition data are written there.

## Not duplicates

lem-sfb-finite-constant-projective-graph vs lem-wf-curve-normal-smooth-compactification: constructs a compactification of a normal finite-field curve; the new lemma starts with an arbitrary-dimensional projective F-scheme and a separated target.

lem-sfb-finite-constant-projective-graph vs lem-trf-alteration-relative-curve-preparation: constructs a relative curve alteration; the new lemma constructs no alteration or curve pencil and proves finite-constant graph projectivity.

lem-sfb-finite-constant-projective-graph vs lem-trf-relative-marked-nodal-reduction: constructs a nodal-curve alteration square; the new lemma is projectivity for a given morphism and has no curve or nodal hypotheses.

lem-sfb-finite-constant-projective-graph vs lem-trf-projective-bundle-proper: only proves properness after projective-bundle projectivity is given; the new lemma must construct that projectivity and its embedding.

lem-sfb-finite-constant-projective-graph vs lem-trf-stein-smooth-generic-curve: constructs a Stein factorization for a relative curve; the new lemma assumes only a projective source over a finite extension and an arbitrary separated target.

lem-sfb-finite-constant-projective-graph vs lem-trf-projective-bundle-to-h-projective: assumes projective-bundle projectivity over an ample base; the new lemma descends finite constants and constructs a graph over S, which need not have an ample sheaf.

lem-sfb-finite-constant-projective-graph vs lem-trf-projective-bundle-global-generated-h-projective: concerns a globally generated projective bundle, with no descent of constants or morphism to an arbitrary separated target.

lem-sfb-finite-constant-projective-graph vs def-trf-projective-bundle-morphism: is a definition; it does not prove existence of the embedding, finite-constant descent or base-change assertions.

lem-sfb-finite-constant-projective-graph vs lem-trf-h-projective-composition: composes two already H-projective morphisms; neither finite-extension projectivity nor the target graph embedding is its conclusion.

lem-sfb-finite-constant-projective-graph vs lem-trf-finite-projective-bundle: makes a finite map projective-bundle; R itself is not assumed finite, and the new lemma also descends its projectivity and constructs the graph.

lem-sfb-finite-constant-projective-graph vs lem-pc-projective-base-change: preserves a GIVEN H-projective embedding under base change; it does not construct projectivity of c from projectivity over F.

lem-sfb-finite-constant-projective-graph vs lem-sfb-projective-affine-base-blowup: concerns an ordinary blowup over an affine Noetherian base; the new lemma has no blowup or Noetherian-base hypothesis.

lem-sfb-finite-constant-projective-graph vs lem-sfb-finite-graded-proj-projective: embeds a graded Proj over a field after Veronese regrading; it does not address a morphism c to a separated target.

lem-sfb-finite-constant-projective-graph vs def-pc-projective-morphism: only fixes a convention for H-projectivity and quasi-compactness, not a theorem constructing it.

lem-sfb-finite-constant-projective-graph vs lem-per-excellent-quasiprojective-normalized-blowup: concerns excellent normalized blowups with an ample-base condition; the new lemma neither constructs nor assumes a blowup.

lem-sfb-finite-constant-projective-graph vs lem-per-excellent-normalized-blowup-tower: concerns towers of blowups and normalization, with no projectivity descent of a given F-projective source to an arbitrary separated target.

lem-sfb-finite-constant-projective-graph vs lem-per-surface-point-blowup-geometry: concerns the geometry of a surface blowup, while the new lemma permits any dimension and has no exceptional divisor.

lem-sfb-finite-constant-projective-graph vs lem-per-h-projective-permanence: assumes the composite to the original base is already H-projective; the new lemma must first obtain that embedding from an F-projective scheme for a finite F/k, and includes its arbitrary-base-change bundle/properness conclusions.

lem-sfb-finite-constant-projective-graph vs lem-weil-pbc-finite-separable-base-refinement: refines a given smooth projective k-structure to a finite separable intermediate field. The new lemma descends in the opposite direction without separability, and proves projectivity to any separated target.

lem-sfb-finite-constant-projective-graph vs lem-weil-pbc-isomorphism-finite: only says an isomorphism is finite; the new lemma has no isomorphism assumption on c.

lem-sfb-semilinear-sylow-snc-resolution vs lem-sfb-semilinear-sylow-good-components: the existing statement stops at a normal Sylow quotient. The new statement additionally resolves that quotient, and proves the exact inverse-image SNC boundary identity.

lem-sfb-semilinear-sylow-snc-resolution vs lem-sfb-tame-snc-quotient-resolution: the existing statement begins with an already tame group over F and says nothing about the constant degree [F:e] or good prime-to-ell component selection; the new statement starts with an arbitrary finite G-action and the full-quotient hypotheses.

lem-sfb-semilinear-sylow-snc-resolution vs lem-sfb-equivariant-smooth-galois-model: the existing statement constructs a model without prime-to-ell degrees; the new statement assumes that model and carries out only the Sylow-and-resolution stage.

lem-sfb-open-smooth-snc-restriction vs def-trf-smooth-strict-normal-crossings-divisor: this is a definition, not an open-restriction theorem with local ideals and projective immersions.

lem-sfb-open-smooth-snc-restriction vs lem-sfb-nested-open-regular-alteration: the existing lemma constructs alterations and nested-open pairs with a prescribed cover. The new statement constructs no alteration and only restricts a given smooth projective pair.

## Preservation of all eight former proof steps

The following is a verbatim archive of the former proof, not proof fields on the new unsplit nodes. Its first two constructions already have independent nodes; the three newly extracted arguments are recorded statement-only for other workers.

### Former step 1: Parent step 1 (empty case).

If $X=\varnothing$, then $Z=\varnothing$. Take $k'=k$, $P=\varnothing$ and the identity of the empty scheme. Its field degree is $1$, and every boundary, generic-point and intersection condition is vacuous. Hence assume $X$ nonempty.

Original uses: .

### Former step 2: Existing lem-sfb-proper-pair-radicial-preparation, parent steps 1 and 4; the explicit characteristic-degree tower citation is added.

Apply proper-pair radicial preparation to $(X,Z)$. It gives the dense open $X\subseteq\overline X$, the closed extension $C$ of $Z$, a common finite radicial extension $e/k$, and $r:B\to\overline X$. In particular $B$ is proper, normal and geometrically reduced over $e$, with finitely many disjoint integral components, and $C_B=r^{-1}C$ is the support of an effective Cartier divisor. At every generic point the residue extension for $r$ is finite purely inseparable. Its degree and $[e:k]$ are powers of the characteristic, or $1$ in characteristic zero, so they are prime to $\ell$. Every component of $\overline X$ meets $X$, since $X$ is dense.

Original uses: lem-sfb-proper-pair-radicial-preparation.

### Former step 3: Existing lem-sfb-equivariant-smooth-galois-model, parent step 2. Its simultaneous-model and full-quotient clauses are hypotheses of the new Sylow child.

Apply the equivariant smooth Galois-model node to $(B,C_B)$ over $e$. Obtain the finite extension $K/e$, finite group $G$, smooth projective $K$-scheme $Y$ and invariant projective surjection $h:Y\to B$. The reduced divisor $D=(h^{-1}C_B)_{\rm red}$ is relative strict normal crossings over $K$. The fixed field $K^G/e$ is radicial and the full scheme quotient $Y/G\to B$ is a finite universal homeomorphism over a dense open meeting each component. These two full-quotient properties, not just a generically finite cover, are the hypotheses needed for the subsequent Sylow argument. The model is chosen simultaneously for all components of $B$, so there is only one field $K$ and one group $G$.

Original uses: lem-sfb-equivariant-smooth-galois-model.

### Former step 4: New lem-sfb-semilinear-sylow-snc-resolution: all of this Sylow selection, its separability and open-and-closed restriction.

Choose an $\ell$-Sylow subgroup $L\leq G$ by the Sylow prime-index node. Apply the semilinear Sylow good-components node to $h$. Set $F=K^L$ and write $Q^\circ\subseteq Y/L$ for the selected open and closed union. It gives $[F:e]$ prime to $\ell$, a finite separable extension $K/F$, a projective surjection $d:Q^\circ\to B$, and finite prime-to-$\ell$ residue extensions at every generic point of $Q^\circ$. Use exactly these selected components: a total prime-to-$\ell$ degree does not assert that every component has prime-to-$\ell$ degree. Let $Y^\circ$ be their open-and-closed inverse image. The $L$-quotient is $q:Y^\circ\to Q^\circ$; the restriction $D^\circ=D\cap Y^\circ$ is an invariant relative strict normal crossings divisor over $K$, since the same components and their intersections restrict to this union of connected components.

Original uses: lem-weil-pbc-sylow-subgroup-prime-index, lem-sfb-semilinear-sylow-good-components.

### Former step 5: New lem-sfb-semilinear-sylow-snc-resolution: all of the tame-resolution application and the exact quotient-image boundary calculation.

The group $L$ has $\ell$-power order, hence its order is invertible in $F$ because $\ell\ne\operatorname{char}(k)$. The hypotheses of the tame semilinear SNC-quotient resolution node now hold for $(Y^\circ,D^\circ,K/F,L)$. Apply it to obtain $v:R\to Q^\circ$, with $R$ smooth projective over $F$ and $v$ projective surjective, an isomorphism on a dense open meeting every component, and inducing equality of the generic residue fields. It also gives a reduced relative strict normal crossings divisor $E$ with support $v^{-1}q(|D^\circ|)$, together with the local regular-parameter and regular-scheme boundary assertions. Because $h$ factors as $d q$ on $Y^\circ$ and $q$ is surjective, $q(|D^\circ|)=d^{-1}(C_B)$: a point of $Q^\circ$ lies over $C_B$ exactly when every point above it in $Y^\circ$ lies in $h^{-1}C_B$. Thus $|E|=(r d v)^{-1}(C)$.

Original uses: lem-sfb-tame-snc-quotient-resolution.

### Former step 6: Parent step 4 keeps the numerical tower multiplication; new lem-sfb-finite-constant-projective-graph carries all of the finite-constant descent and graph-embedding argument.

Set $c=r d v:R\to\overline X$; it is surjective by composing the three surjections. Each generic point of $R$ maps to a generic point of $\overline X$. For the corresponding tower of residue fields, $v$ has degree $1$, $d$ has degree prime to $\ell$, and $r$ has purely inseparable degree prime to $\ell$. The degree of the composite is their product (multiply field bases), hence prime to $\ell$. Likewise $F/k$ has degree $[F:e][e:k]$ prime to $\ell$. This checks every generic point, including all components retained by the Sylow step. Projectivity of $c$ is obtained through its graph, without composing projective-bundle maps over the non-projective bases $B$ and $\overline X$. The finite morphism $\operatorname{Spec}F\to\operatorname{Spec}k$ is projective in the projective-bundle sense by the finite-morphism node; $\operatorname{Spec}k$ is affine, so $\mathcal O$ is ample (take the section $1$), and the projective-bundle-to-H-projective node makes it H-projective. $R$ is H-projective over $F$ by Step 5, so the H-projective composition node gives a closed immersion $\iota:R\hookrightarrow\mathbf P^M_k$ over $k$. Since $\overline X$ is proper, hence separated, over $k$, the graph $(\mathrm{id},c):R\to R\times_k\overline X$ is the base change of the closed diagonal of $\overline X$ along $c\times\mathrm{id}$, so it is a closed immersion; $\iota\times\mathrm{id}:R\times_k\overline X\to\mathbf P^M_k\times_k\overline X$ is a closed immersion by base change, and $\mathbf P^M_k\times_k\overline X=\mathbf P^M_{\overline X}$ by associativity of the fibre product $\overline X\times_{\mathbf Z}\mathbf P^M_{\mathbf Z}$. The composite closed immersion $R\hookrightarrow\mathbf P^M_{\overline X}$ lies over $c$, so $c$ is H-projective.

Original uses: lem-trf-finite-projective-bundle, def-weil-pbc-ample-invertible-module, lem-trf-projective-bundle-to-h-projective, lem-trf-h-projective-composition, def-weil-proper-morphism, lem-weil-pbc-closed-immersion-base-change, def-nagata-projective-space-base-change, def-kun-projective.

### Former step 7: New lem-sfb-finite-constant-projective-graph carries the projective-space base change, bundle-convention and properness check; parent step 5 cites surjective base change and step 6 keeps generic-point restriction.

Take $k'=F$ and $P=c^{-1}(X)=R\times_{\overline X}X$, with $a:P\to X$. Base change of the closed immersion $R\hookrightarrow\mathbf P^M_{\overline X}$ of Step 6 along the open immersion $X\subseteq\overline X$ gives a closed immersion $P\hookrightarrow\mathbf P^M_{\overline X}\times_{\overline X}X=\mathbf P^M_X$ over $X$, so $a$ is H-projective. By the projective-space definition, $\mathbf P^M_X$ is the same scheme over $X$ as the relative projective space $\operatorname{Proj}_X\operatorname{Sym}(\mathcal O_X^{\oplus(M+1)})$, the projective bundle of the finite-type quasi-coherent module $\mathcal O_X^{\oplus(M+1)}$; hence $a$ is projective in the projective-bundle sense. Surjective base change makes $a$ surjective, and H-projective morphisms are proper. Every generic point of $R$ belongs to $P$, since its image is generic in $\overline X$ and hence lies in the dense open $X$; the generic residue extensions for $a$ are therefore exactly those checked in Step 6.

Original uses: lem-weil-pbc-closed-immersion-base-change, def-nagata-projective-space-base-change, def-nagata-relative-projective-space, def-trf-projective-bundle-morphism, lem-weil-pbc-surjective-base-change, lem-kun-projective-implies-proper.

### Former step 8: New lem-sfb-open-smooth-snc-restriction: this entire smoothness, quasi-projectivity, local-parameter and SNC restriction argument; parent step 6 assembles its support with C intersect X=Z.

The open subscheme $P\subseteq R$ is smooth over $F$: locally on $R$, choose a constant relative dimension $n$ for its smooth structure morphism, as in the smooth-morphism definition. The open inclusion is etale by etale composition/cancellation clause (1), hence smooth of relative dimension $0$; relative-dimension composition makes its composite smooth of relative dimension $n$. The same argument applies to each open intersection of components of $E$. Their codimensions persist because the local rings of an open subscheme agree with the original local rings. If $R\hookrightarrow\mathbf P^n_F$ is its projective embedding, $P$ is closed in the complement of the closed subset $R\setminus P$ of that projective space, hence locally closed in $\mathbf P^n_F$. This proves quasi-projectivity. Finally $C\cap X=Z$ gives $|E|\cap P=a^{-1}Z$. Restrict the finitely many integral components of $E$ to $P$ and omit empty ones; each remaining one is still integral because a nonempty open of an integral scheme is integral. Their local parameter equations and local rings are unchanged. Thus they give the claimed reduced divisor, all the relative smooth-intersection and codimension assertions, and the regular-scheme strict normal crossings boundary. Empty intersections and the empty boundary obey the same conventions.

Original uses: def-sbc-smooth-morphisms, lem-weil-pbc-etale-composition-cancellation, lem-sbc-smooth-relative-dimension-permanence, def-trf-strict-normal-crossings-boundary.

## Unfinished work

Only the proofs of the three new unsplit children remain as intended stage-1 queue items. No requested repair point is left open. The required server delivery dry run returned OK at 40131af4d8a, with preflight passed. A final dry run is required after this validation note, then the authorized push.

## Earlier repository report retained (stage-2 archive, not actions of this repair)

The earlier report below predates this stage-1-only repair. Its compilation and Lean-writing statements are historical; no such commands were run in this repair.

## Worker report

The module `Sheaf.AlgebraicGeometry.GabberGlobalSNCAlteration` states
`AlgebraicGeometry.exists_gabber_global_snc_alteration`, with `sorry` as its only proof.
There are no definitions, additional theorem obligations, new nodes, dependency repairs,
or statement corrections. The node changes only `lean` and adds the already landed
`def-sc-quasi-projective` and `def-trf-strict-normal-crossings-divisor` to `stmt_deps`.
These supply existing notions that the original statement describes in words.

Source read: ILO, Travaux de Gabber, Expose X, printed pp. 148--152: the definition of an
ell-prime alteration, Theorem 2.1, its following relative-SNC definition, and proof 2.3
Steps 1--3. The complete eight-step DAG proof is reproduced in the theorem docstring,
including the good-component selection, graph argument for projectivity, and return
to the original open subscheme. The source's geometric conditions agree with the node.

### Each hypothesis and conclusion clause

| Node clause | Lean rendering |
| --- | --- |
| Arbitrary field k | `(k : Type u) [Field k]` |
| Prime ell different from char(k) | `(ℓ : ℕ) (hℓ : Nat.Prime ℓ) (hchar : ℓ ≠ ringChar k)` |
| k-scheme X | `(X : Scheme.{u}) (f : X ⟶ Spec (.of k))` |
| Separated | `[IsSeparated f]` |
| Finite type | `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the recorded finite-type convention |
| Nowhere dense closed subset Z | `(Z : Set X) (hZ : IsClosed Z) (hZnd : interior Z = ∅)`; closedness makes this equivalent to empty interior of the closure |
| Finite field extension k'/k | `∃ (K : Type u) (_ : Field K) (i : k →+* K), i.Finite ∧ ...`; a field homomorphism is injective, and `i.Finite` is finiteness for its canonical scalar action |
| Extension degree prime to ell | `Nat.Coprime (@Module.finrank k K _ _ i.toAlgebra.toModule) ℓ` |
| Scheme P over k' | `∃ (P : Scheme.{u}) (p : P ⟶ Spec (.of K)) ...` |
| Smooth | `Smooth p` |
| Quasi-projective, locally closed immersion in finite projective space | `IsQuasiProjective p`; the upstream definition quantifies over a finite coordinate type and an `IsImmersion` over `Spec K` |
| Proper, projective, surjective alteration a | `(a : P ⟶ X)` and `IsProper a ∧ IsProjectiveBundle a ∧ Surjective a`; projectivity uses the node's projective-bundle convention |
| Compatibility with Spec(k') to Spec(k) | `a ≫ f = p ≫ Spec.map (CommRingCat.ofHom i)` |
| Every component generic point maps to a component generic point | `∀ (C : Set P), C ∈ irreducibleComponents P → ∀ η : P, IsGenericPoint η C → (∃ B ∈ irreducibleComponents X, IsGenericPoint (a η) B) ∧ ...` |
| Finite induced residue extension at each such generic point | `(a.residueFieldMap η).hom.Finite` |
| Every such degree is prime to ell | `Nat.Coprime (@Module.finrank (X.residueField (a η)) (P.residueField η) _ _ (a.residueFieldMap η).hom.toAlgebra.toModule) ℓ` |
| Reduced inverse image of Z | `∃ D : P.IdealSheafData, D = ((Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩).comap a).radical ∧ ...`; D is determined by this equality |
| Relative strict normal crossings | `D.IsStrictNormalCrossingsDivisor p` |
| Finitely many distinct irreducible components | That predicate supplies `n : ℕ`, `C : Fin n → P.IdealSheafData`, injective component supports, integral component schemes, and union of supports equal to D's support |
| Each component smooth of codimension one | The same predicate for singleton finite subsets: `Smooth ((⨆ i ∈ s, C i).subschemeι ≫ p)` and ambient stalk dimension equals intersection stalk dimension plus `s.card = 1` |
| Every intersection smooth of codimension its number of components | The predicate quantifies over every `s : Finset (Fin n)` and all points of the scheme cut out by the sum of the component ideals, with the same dimension formula |
| Local equations are distinct regular parameters | At every `x : P`, an affine neighborhood `U`, stalk Noetherianity `hR`, regular system `t`, and a `s.Sublist t` with `s.Nodup`, whose product generates the stalk ideal of D |
| Local equation is the actual boundary ideal | `(D.ideal U).map (P.presheaf.germ U.1 x hx).hom = Ideal.span {s.prod}` |
| Regular-scheme SNC boundary | `IsStrictNormalCrossingsBoundary D ∧ IsRegularScheme P` |
| Empty schemes, boundaries and intersections allowed | No nonempty or connectedness hypothesis. Finite component families and the parameter sublist may be empty. The relative SNC predicate includes the empty subset and vacuous pointwise codimension conditions for empty intersections. |

The local product equation is precisely the component equation assertion, without a new
local-chart definition: the entries of a regular system are prime parameters, and the
nodup sublist gives distinct local prime factors. The relative SNC components are integral
and smooth, hence their stalks through x are domains. Their local prime ideals are exactly
these parameter ideals. Conversely component parameter equations give this product ideal
because D is the reduced Cartier union. Thus no etale neighborhood, arbitrary replacement
map, or weaker set-theoretic boundary equation is substituted for the stated local condition.

### Dependency declarations read and used

All original statement-dependency nodes, their Lean/mathlib records, and the recorded
signatures and docstrings were read. The modules are read from the live read-only checkout.

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs` (line 180).
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (line 43), and
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
  (line 43). Both classes express the finite-type hypothesis.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`,
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` (line 42), with the recorded
  `IsSeparated` and `UniversallyClosed` signatures in their owning Mathlib modules.
- `def-pc-field-extension`: the ring map `i`, equivalently its `RingHom.toAlgebra`,
  using Mathlib `Algebra` in `Mathlib.Algebra.Algebra.Defs` (line 95).
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth` (line 62).
- `def-trf-projective-bundle-morphism`: `AlgebraicGeometry.IsProjectiveBundle`,
  `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`, read in full. It uses an actual
  quasi-coherent finite-type module and closed immersion into its canonical projective bundle.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective`,
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap` (line 59).
- `def-weil-irreducible-components`: the recorded Mathlib match `irreducibleComponents`,
  `Mathlib.Topology.Irreducible` (line 107), maximal irreducible subsets.
- `def-sc-generic-point`: `IsGenericPoint`, `Mathlib.Topology.Sober` (line 39),
  equality of singleton closure with the given component.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`,
  `Mathlib.AlgebraicGeometry.ResidueField` (lines 48 and 123).
- `def-weil-pbc-regular-system-of-parameters`:
  `IsLocalRing.IsRegularSystemOfParameters`,
  `WeilConjectures.RingTheory.IsRegularSystemOfParameters`, read in full.
- `def-trf-strict-normal-crossings-boundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`,
  `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`, read in full.
- `def-weil-regular-scheme`: `AlgebraicGeometry.IsRegularScheme`,
  `Sheaf.AlgebraicGeometry.IsRegularScheme`, read in full: local Noetherianity AND
  stalkwise regularity, not just regularity of individual rings.
- Added landed `def-sc-quasi-projective`: `AlgebraicGeometry.IsQuasiProjective`,
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective` (line 48).
- Added landed `def-trf-strict-normal-crossings-divisor`:
  `AlgebraicGeometry.Scheme.IdealSheafData.IsStrictNormalCrossingsDivisor`,
  `Sheaf.AlgebraicGeometry.StrictNormalCrossingsDivisor`, read in full.

Proof-only imports include the recorded projectivity, relative projective space,
ample-module, finite-projective-bundle, H-projective composition and conversion modules,
as well as Mathlib closed-immersion base change, etale composition, surjective base change
and Sylow. The four new geometric proof nodes (proper-pair preparation, equivariant model,
Sylow good components and tame quotient resolution) have no Lean declarations yet and
therefore no import. Their absence does not affect this statement's objects; their full
intended uses are in the proof docstring. No consumer module is changed in the read-only clone.

### Edge cases

- Empty X: take K=k of degree one and P empty. Generic-point and stalk conditions are
  vacuous; the empty Cartier divisor is represented by the unit ideal.
- Empty Z with nonempty X: D is the unit ideal. The relative predicate permits `n=0`.
  At any stalk choose `s=[]`, with product one, and any regular parameter system t.
- Dimension-zero components of P: t and s may both be empty; a nowhere dense Z has
  no such component generically in its preimage.
- Empty intersections: smoothness of the empty scheme is allowed and the codimension
  equation has no points at which to be tested.
- Empty index subset of the components: the ideal sum is bottom and its subscheme is P;
  the smoothness assertion is `Smooth p` and the dimension equation has increment zero.
- Characteristic zero: `ringChar k=0` and every prime is allowed. No positive-characteristic
  or perfectness assumption is added. In positive characteristic only the given prime is excluded.
- Disconnected or nonreduced X: no integrality or reducedness hypothesis is imposed. Every
  component of P is tested separately, rather than taking a total generic degree.
- Finiteness is explicit for i and every generic residue map: the convention that `finrank`
  is zero for an infinite extension cannot accidentally make the degree assertion vacuous.
- All ambient fields and schemes are in the explicit universe u, consistent with the recorded
  geometry APIs. A finite field extension of k has a representative in this same universe.
  `set_option autoImplicit false` prevents any silently introduced variable or universe.

### Searches made

- `msearch.py ... leanfinder` query: "Gabber prime to ell projective alteration with smooth
  quasi-projective source and relative strict normal crossings boundary". Eight results:
  smooth and standard-smooth morphism definitions/chart results and Proj valuative existence;
  none states the alteration theorem.
- `msearch.py ... loogle` query: `"IsSmooth", "IsProper"`. Zero hits.
- `msearch.py ... grep` query: `Gabber|alteration|normalCrossing|normal_crossing`.
  Three Mathlib hits, all bibliographic mentions of Beilinson--Bernstein--Deligne--Gabber
  in triangulated t-structure files. No alteration theorem or SNC predicate.
- `msearch.py ... leansearch` query: "Prime to ell alterations resolving a variety with relative
  strict normal crossings boundary". Eight hits on etale loci, normalization, ramification,
  and base-change stability; none states the theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `Relative.*[Nn]ormal|[Nn]ormalCrossings|[Qq]uasiProjective|[Qq]uasi[Pp]rojective|[Gg]abber`
  found existing relative SNC and quasi-projectivity interfaces, reused here. Narrow searches
  for the item id and theorem name found only proof-plan citations in NestedOpenRegularAlteration,
  with no existing statement of this item. No new definition is needed.
- DAG search for `def-trf-strict-normal-crossings-divisor` and quasi-projective locally closed
  immersions located the two landed definition nodes added to statement dependencies.

Validation: prescribed `scompile.py NB lem-sfb-gabber-global-snc-alteration <file>` compiled
both sandbox and library-name modes cleanly, most recently in 3.0 s and 4.3 s. An initial
style warning about an extra newline before the docstring terminator was repaired; the final
file has no warnings. The only theorem proof is `sorry`, as required for stage 2.

## Second reading by NB

This is a dispatcher-started single-worker delivery; no additional agent was started, as the
brief forbids it. This section records a second pass by the same worker; the maintainer supplies
the independent review.

With the final node and Lean file open, I checked every row above against the exact signature.
The result retains arbitrary separated finite-type X (not only integral X), uses the
projective-bundle predicate requested by the node, and quantifies at EACH component generic
point with the actual induced scalar action. The relative-SNC predicate already gives the
finite component/intersection clauses; its empty finite subset supplies smoothness of P.
The additional regular-scheme predicate includes local Noetherianity. The local formula uses
actual stalk ideals and no etale substitution. On this pass I made distinctness of the local
parameter factors explicit with `s.Nodup`; that is already forced for a sublist of a regular
parameter system, and directly renders the node's word "distinct". I also ensured every
available proof-dependency module, including Mathlib leaves, has a proof-only import.
No mismatch, disputed statement, or dependency-interface defect remains.
