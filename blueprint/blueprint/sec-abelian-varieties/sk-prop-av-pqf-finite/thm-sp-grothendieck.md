+++
id = "thm-sp-grothendieck"
kind = "theorem"
title = "Grothendieck spectral sequence"
order = 524
uses = ["def-sp-composite-acyclicity", "def-sp-convergence", "def-sp-double-complex-total", "def-sp-exact-couple", "def-sp-image-filtration", "def-sp-injective-resolutions", "def-sp-left-exact-additive", "lem-sp-edge-collapse", "thm-sp-double-complex-spectral-sequences", "thm-sp-if-e1"]
+++
Let $(F,G)$ be a composable pair [def-sp-composite-acyclicity] with $F$
sending injectives to $G$-acyclics. For every $X\in\mathcal A$ there is a
functorial first-quadrant spectral sequence whose $E_2$-page is

$$
 E_2^{p,q}=R^pG\bigl(R^qF(X)\bigr)
$$

and which converges to $R^{p+q}(G\circ F)(X)$; its edge maps in degree $n$
have directions $R^nG(F(X))\to R^n(G\circ F)(X)\to G(R^nF(X))$, and the
spectral sequence depends functorially on $X$.

## Proof

Choose an injective resolution $X\to I^\bullet$
([def-sp-injective-resolutions]) and put $C^\bullet=F(I^\bullet)$ in
$\mathcal B$, so that $R^qF(X)=\mathcal H^q(C^\bullet)$. Let
$C^{\bullet,\bullet}$ be a Cartan--Eilenberg resolution of $C^\bullet$
([thm-sp-if-e1]) and put $D^{p,q}=G(C^{p,q})$; since $G$ is left exact,
$R^qG(C^p)=\mathcal H^q(G(C^{p,\bullet}))$. Filtering the total complex of
$D$ ([def-sp-double-complex-total]) by the second degree, the $E_1$-page is

$$
 E_1^{p,q}=R^qG\bigl(F(I^p)\bigr),
$$

which vanishes for $q>0$ precisely because every $F(I^p)$ is $G$-acyclic
([def-sp-composite-acyclicity]). By the bottom-edge collapse, i.e.
[lem-sp-edge-collapse] applied to the bidegree transposition
$(p,q)\mapsto(q,p)$ (which preserves the [def-sp-exact-couple]-structure and
the first-quadrant convergence of [def-sp-convergence]), this sequence
degenerates at $E_2$: $E_2^{p,q}=0$ for $q>0$, no differential begins at
$E_2$, and

$$
 E_2^{n,0}\cong R^n(G\circ F)(X),
$$

via the edge isomorphisms and $E_2^{n,0}=H^n\bigl(GF(I^\bullet)\bigr)$
([def-sp-left-exact-additive]); this is the convergence computation. The
stated $E_2$-page $R^pG(R^qF(X))$ is the page of the first-degree filtration
of the same double complex, whose identification with the horizontal
cohomology of the $C^{\bullet,q}$-columns is the Cartan--Eilenberg
computation of [thm-sp-if-e1]; the two spectral sequences of the double
complex ([thm-sp-double-complex-spectral-sequences]) converge to the same abutment, so the stated sequence converges to
$R^{p+q}(G\circ F)(X)$ as claimed. The induced filtration on the abutment is
the image filtration of [def-sp-image-filtration], convergence is the
half-plane case of [def-sp-convergence], and everything is functorial in
$X$.

(*References: Weibel, An Introduction to Homological Algebra, Theorem 5.8.3;
Stacks Project, Lemma 13.22.1 (Tag
[015M](https://stacks.math.columbia.edu/tag/015M)) identifies the acyclicity
condition with the canonical map $R(G\circ F)\to RG\circ RF$ being an
isomorphism, and Lemma 13.22.2 (Tag
[015N](https://stacks.math.columbia.edu/tag/015N)) is the bounded, converging
spectral sequence with finite induced filtration. The relative Leray form
$E_2^{p,q}=R^pg_*(R^qf_*\mathcal F)\Rightarrow R^{p+q}(g\circ f)_*\mathcal
F$, functorial in $\mathcal F$ and available for bounded-below complexes, is
Lemma 20.13.8 (Tag [01F6](https://stacks.math.columbia.edu/tag/01F6)); the
topoi (site) form is Lemma 21.14.6, see the dictionary
[def-sp-etale-dictionary] for the specialization.*)
