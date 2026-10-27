# Worker report

1. Files written:

- lem-fd-frobenius-fixed-pair-comparison: repaired split; statement and statement dependencies unchanged.
- lem-fd-geometric-fibre-comparison-hypotheses: statement, unsplit; no exact Mathlib match after LeanSearch, LeanFinder/Loogle and source grep.
- lem-fd-fixed-pair-equivalence-transport: statement, unsplit; no exact Mathlib match after LeanSearch, LeanFinder/Loogle and source grep.
- lem-fd-fixed-pair-mixed-square-lift: statement, unsplit; no exact Mathlib match after LeanSearch, LeanFinder/Loogle and source grep.

2. Attachments: none. The project theorem WeilConjectures.frobeniusFixedPairComparison, lean/Sheaf/Paper/FrobeniusFixedPairComparison.lean:154–162, ends in sorry. Project helpers mapOfNatIso, fullyFaithfulMapOfNatIso, mapOfNatIsoIsoOfIso and mapOfNatIsoCompIsoOfIso supply parts of the transport work; none alone states one of the three complete tasks. No Mathlib declaration states all of a task in one-line specialization.

3. WANTED: none. The inherited proof is explicitly agent-written, and remains so; the blueprint motivates it but does not prove it.

4. Fault repaired: the released 2026-10-22 stage-1 order requires distributing the 5677-character proof, not shortening it. The new assembly has three steps, and the three statement-only nodes assign every old argument to an independent task. No target or item statement has been changed.

5. Unfinished: the proofs of the three new nodes are intentionally left for other workers, as required. No Lean file was written and no compiler was invoked.

## Argument allocation and preservation

- Old steps 1–3 belong to lem-fd-geometric-fibre-comparison-hypotheses: arbitrary base change and affine generators; Noetherianity and global finite dimension including the empty fibre; units in stalks and the semilinear inverse.
- Old steps 4–7 belong to lem-fd-fixed-pair-equivalence-transport: define transported structures, identify intertwiners by naturality and faithfulness, restrict the Hom bijection, conjugate an arbitrary target structure and lift it and its inverse, then apply the fully-faithful/essentially-surjective criterion.
- Old steps 8–10 belong to lem-fd-fixed-pair-mixed-square-lift: the supplied mixed square, the explicit naturality calculation, substitution of finite-to-common inclusions, and preservation of identities/cocycles by the faithful forgetful functor.

The following is the full inherited argument, retained as the work instructions for those tasks. It is not proof text inside any unsplit node.

### Old step 1

Apply separated finite-type base change to $X_0\to\operatorname{Spec}k_0$ and the field extension $k/k_0$. This gives $X$ separated and of finite type over $k$. Concretely, its finite affine cover has coordinate rings $A_i\otimes_{k_0}k$; the images $a_{ij}\otimes1$ of generators of $A_i/k_0$ still generate over $k$. Thus the finite-type hypothesis needed below is for $X\to\operatorname{Spec}k$, without requiring $k/k_0$ finite.

Uses: lem-pod-separated-finite-type-base-change

### Old step 2

The only ideals of the field $k$ are $0$ and $k$, so every ideal is finitely generated; its one affine chart makes $\operatorname{Spec}k$ Noetherian. Apply finite-type-over-Noetherian to the structure morphism from step 1: $X$ is Noetherian. Apply the finite-type-over-a-field dimension lemma with $K=k$ to the same morphism: $\dim X<\infty$. The empty scheme is allowed, with dimension $-\infty$; hence this also supplies a finite nonnegative dimension bound in that case.

Uses: lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type

### Old step 3

Since $\operatorname{char}k=p$ and $\ell\ne p$, the image of $\ell$ in $k$ has inverse $\ell^{-1}$. Their images under $k\to\mathcal O_{X,x}$ still multiply to $1$, for every $x$. Thus $\ell$ is invertible on $X$. The Frobenius definition gives $g_X$ and its inverse $\operatorname{id}_{X_0}\times\operatorname{Spec}(\varphi_q)$. Their composites are identities because $\gamma\varphi_q=\varphi_q\gamma=1$. Consequently $g_X$ is an allowed scheme isomorphism for $S$; no $k$-linearity is used.

Uses: def-weil-finite-field-fiber, def-weil-frobenius-detailed

### Old step 4

At either a finite stage or the common stage, take from the given datum its equivalence $J:\mathcal C_s\simeq\mathcal C_p$ and comparison $b:JF_s\simeq F_pJ$ for $g_X$. Use the inverse comparison if necessary. Write $\psi_K=J(\theta_K)b_K^{-1}$. This is an isomorphism $F_pJK\to JK$, since both factors are isomorphisms. The framework pairs are exactly the fixed pairs of $F_s$ in the Weil-complex definition; the target pairs are the fixed pairs of $F_p$.

Uses: def-fd-pullback-comparison-datum, def-fd-coefficient-comparison-datum, def-weil-weil-sheaf-complex

### Old step 5

For $u:K\to K'$, naturality gives $F_p(Ju)b_K=b_{K'}J(F_su)$. Therefore
$$Ju\,\psi_K=\psi_{K'}F_p(Ju)\quad\Longleftrightarrow\quad J(u\theta_K)=J(\theta_{K'}F_su)\quad\Longleftrightarrow\quad u\theta_K=\theta_{K'}F_su.$$
The first equivalence substitutes $\psi$ and cancels $b_K$; the second uses injectivity of the Hom map of the supplied equivalence $J$. Thus $u\mapsto Ju$ defines a functor on pairs, preserves identities and composition, and its map on each Hom is exactly the restriction of the given bijection for $J$. The reverse implication shows that its inverse Hom bijection also lands in intertwining arrows, so the pair functor is fully faithful.

Uses: def-fd-coefficient-comparison-datum, def-fd-pullback-comparison-datum, def-weil-weil-sheaf-complex

### Old step 6

Given a target pair $(H,\psi)$, choose $K$ and an isomorphism $v:JK\simeq H$ using the essential surjectivity of the equivalence in the datum. Put $\psi_0=v^{-1}\psi F_p(v):F_pJK\simeq JK$. Lift $\psi_0b_K:JF_sK\simeq JK$ by the Hom bijection of $J$ to $\theta:F_sK\to K$, and lift its inverse to $t:K\to F_sK$. Applying $J$ to the two composites and using injectivity gives $t\theta=1$ and $\theta t=1$. Thus $\theta$ is a Weil isomorphism, its transported structure is $\psi_0$, and $v\psi_0=\psi F_p(v)$ makes $v$ an isomorphism of pairs. This proves essential surjectivity without assuming $H$ is literally $JK$.

Uses: def-fd-coefficient-comparison-datum, def-fd-pullback-comparison-datum, def-weil-weil-sheaf-complex

### Old step 7

Apply the fully-faithful/essentially-surjective criterion to the pair functor from steps 4–6. Its hypotheses are precisely the restricted Hom bijections of step 5 and the isomorphisms $v$ of step 6. All categories and functors involved may be placed in a common larger universe, so the criterion applies. It produces an equivalence with this very functor, and therefore with the required arrow map and Hom bijection.

Uses: lem-trf-fully-faithful-ess-surj-equivalence

### Old step 8

For a finite extension $E\subset L$, denote the two scalar functors by $T_s,T_p$, their supplied Frobenius comparisons by $r_s:T_sF_{s,E}\simeq F_{s,L}T_s$ and $r_p:T_pF_{p,E}\simeq F_{p,L}T_p$, and the coefficient comparison by $j:J_LT_s\simeq T_pJ_E$. These are the actual scalar functors and comparisons in $S$. Its mixed square, with $b$ oriented as in the statement, reads
$$r_{p,J_EK}\,T_p(b_{E,K})\,j_{F_{s,E}K}=F_{p,L}(j_K)\,b_{L,T_sK}\,J_L(r_{s,K}).$$
This is an assumption of the given compatible transformation, not an additional coherence assertion about scheme composition.

Uses: def-fd-pullback-comparison-datum, def-fd-coefficient-comparison-datum

### Old step 9

The structure on the scalar extension of $(K,\theta)$ is $T_s(\theta)r_{s,K}^{-1}$. Naturality of $j$ at $\theta$, followed by rearrangement of the equation in step 8, gives
$$\begin{aligned}
j_KJ_L(T_s(\theta)r_{s,K}^{-1})b_{L,T_sK}^{-1}
&=T_p(J_E\theta)j_{F_{s,E}K}J_L(r_{s,K}^{-1})b_{L,T_sK}^{-1}\\
&=T_p(J_E\theta b_{E,K}^{-1})r_{p,J_EK}^{-1}F_{p,L}(j_K).
\end{aligned}$$
This is exactly the intertwining condition for $j_K$ between the two scalar-extended transported pairs. On arrows its naturality is that of $j$. Hence $j$ lifts to the required natural isomorphism of pair functors; its inverse also intertwines by cancelling this equation.

Uses: def-fd-pullback-comparison-datum, def-fd-coefficient-comparison-datum, def-weil-weil-sheaf-complex

### Old step 10

The same displayed calculation applies to a finite-stage inclusion $I_s:\mathcal C_{s,E}\to\mathcal C_s$ and $I_p:\mathcal C_{p,E}\to\mathcal C_p$: replace $T_s,T_p,J_L$ by $I_s,I_p,J_X$. Here $r_s,r_p$ are their specified pullback comparisons. The datum says the common-stage coefficient functor preserves the field label and that the component of its pullback comparison at a literal pair is the inclusion of the finite component. Thus the equation in step 8 for these substitutions is the specified finite-to-common comparison equation. Step 9 proves that the coefficient inclusion comparison is an isomorphism of Weil pairs, natural in arrows. This proves commutation with every finite-stage inclusion. The scalar cocycle and identity equations remain true after lifting: their underlying maps are the supplied ones, and arrows of pairs are equal exactly when their underlying arrows are equal.

Uses: def-fd-pullback-comparison-datum, def-fd-coefficient-comparison-datum, def-weil-weil-sheaf-complex

## Not duplicates

lem-fd-geometric-fibre-comparison-hypotheses vs lem-pod-separated-finite-type-base-change: the latter gives separated finite type base change only; the new task includes global dimension, Noetherianity, stalk units and the semilinear inverse together.
lem-fd-geometric-fibre-comparison-hypotheses vs lem-weil-pbc-finite-type-over-noetherian: the latter gives Noetherianity only, not dimension, units or Frobenius.
lem-fd-geometric-fibre-comparison-hypotheses vs lem-kun-dimension-finite-type: the latter gives finite dimension only.
lem-fd-geometric-fibre-comparison-hypotheses vs def-weil-frobenius-detailed: the definition specifies the inverse but not the geometric-fibre admissibility hypotheses.
lem-fd-fixed-pair-equivalence-transport vs lem-sf-fixed-pair-adjunction-lift: an adjunction with an invertible mate is distinct from equivalence transport, the restricted Hom bijection and the explicit arbitrary-target preimage.
lem-fd-fixed-pair-equivalence-transport vs lem-pur-natural-comparison-strict-intertwiners: the latter changes an endofunctor in one category while retaining carriers; the new task compares two categories through an equivalence and proves essential surjectivity.
lem-fd-fixed-pair-mixed-square-lift vs lem-pur-natural-comparison-functor-transport: the latter compares two endofunctors over one functor; the new task lifts a square of four functors/categories with components j and coherence.
lem-fd-fixed-pair-mixed-square-lift vs lem-fd-common-stage-comparison-descent: the latter constructs underlying coefficient comparisons on common-stage categories, not their lifting to Frobenius fixed pairs.

## Review by Q35

I read the current item, its released keep_plan repair order, the Fourier chapter and trace unit, and main-20261015 sk-def-trace/def-fd-trace-function.md. The final sentence assigns local Frobenius to the PBC coefficient category; it contains no proof of the comparison, so all three extracted statements retain the agent-written auxiliary attribution. The statement and stmt_deps of the item are byte-for-byte the current live values. No chapter or unit route was changed.

For the geometric node I read Stacks morphisms.tex, lemma-base-change-finite-type (01T4), lemma-finite-type-noetherian (01T6), and schemes.tex, lemma-separated-permanence (01KU), as well as the existing dimension node and its blueprint source. I checked the existing nodes' statements: arbitrary base change includes an infinite algebraic closure; finite type includes quasi-compactness so Noetherianity is global; finite dimension is a global bound, not merely finiteness of each local ring's dimension. The fixed field has characteristic p, and the distinct prime ell therefore has a nonzero image whose inverse maps to each stalk. Frobenius is a scheme automorphism over k0; no k-linearity is imposed. Empty X gives a vacuous unit assertion and dimension minus infinity, bounded by zero. This task packages old steps 1–3 rather than creating tiny nodes for elementary unit calculations.

For the general transport node I read the fixed-pair definition and the upstream mapOfNatIso formulas (Algebra.lean:280–296), fullyFaithfulMapOfNatIso (IsoAlgebraFullyFaithful.lean:36–55), and the existing equivalence-criterion statement. The node records a genuine equivalence, not just a functor: naturality identifies both intertwining conditions, and faithfulness reflects equality. For H only isomorphic to JK, conjugation is v inverse, then psi, then G(v) in ordinary composition notation. The lift and its inverse have the correct domains J(FK) to JK and back; faithfulness proves both inverse identities. It needs no invertibility of the endofunctors. Identity endofunctors and empty categories cause no extra hypothesis. Full faithfulness alone, which the upstream helper proves, is insufficient for the full task and was not called an exact attachment.

For the mixed-square node I read both comparison datum statements, the upstream mapOfNatIsoHom (Algebra.lean:315–324), mapOfNatIsoIsoOfIso and compCommIso (IsoAlgebraComp.lean:47–95), and mapOfNatIsoCompIsoOfIso (IsoAlgebraCompIso.lean:32–59). I checked the displayed mixed equation has source J1 Ts F0 K and target G1 Tp J0 K. Naturality at theta gives the displayed intertwining equality on source G1 J1 Ts K; no unnamed composition coherence of scheme comparisons is asserted. The same assumptions permit inclusion functors and scalar functors, neither required to be equivalences. Faithfulness of forgetting pairs lifts identities and cocycles only with matched source/target pair functors, which is stated explicitly. For identity scalar extensions the calculation reduces to the supplied unit equation; for inclusions it uses the actual common comparison's literal-pair component condition.

Assembly step 1 cites the new geometric statement for exactly its Noetherian, dimension, unit and inverse conclusions, and the pullback datum for its domain. Step 2 cites the new transport statement for the exact object/arrow formulas and restricted Hom bijection; the two datum definitions supply J and b, and the Weil-complex definition identifies the source pair category. Step 3 cites the new mixed-square statement for its lift and coherence conclusions; the coefficient datum supplies scalar comparisons and cocycles, and the pullback datum supplies the mixed square and finite components at literal pairs. I opened all these statements and copied literal excerpts into citations.json for every use. There is no use of a cited node's internal proof.

I searched the whole DAG by fixed-pair, equivalence, mixed-square, semilinear and geometric-fibre keywords, searched its Stacks tags and upstream helper names, and ran blueprint_refs.py searches for fixed pair, geometric fibre, intertwining, mixed scalar, scalar comparison, noetherian finite dimensional, endofunctor and semilinear. The existing nearby statements differ as detailed above. The ancestry is def-fd-trace-function via this item and lem-fd-rational-coefficient-category-comparison; every new node records it. Mathlib searches were run only with msearch.py and read, including a second semantic phrasing for each task. Hits for functor-category equivalences, monoid action comparisons, noninvertible algebras and local Noetherianity do not give these statements. Search results are preserved in searches.jsonl and copied faithfully into the nodes.

I checked delivery-errors B–E: new statements introduce all objects, have definition dependencies, normal TeX and no proofs; no new node simply restates the entire item; the three tasks divide its geometry, equivalence and compatibility arguments. Each has comparable independent work, and the original ten steps are retained above without elision. Their proof and proof_deps fields are empty. The assembly stays below 3000 characters, and no individual step hides the old work. No new source invokes SGA. The current repair is a substantive re-split, not a rebase or unchanged push.
