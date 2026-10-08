+++
id = "sk-def-groth-ss"
kind = "section"
title = "Composable pair with acyclicity; the couple of a double complex"
order = 597
lean = ["CategoryTheory.Functor.IsAcyclicComposablePair", "CategoryTheory.SpectralSequence.Abutment"]
+++
*Definition (sketch).*

Let $\mathcal A\xrightarrow{\,F\,}\mathcal B\xrightarrow{\,G\,}\mathcal C$
be additive left exact functors between Grothendieck abelian categories,
so that all three have enough injectives and the right derived functors
$R^nF$, $R^nG$, $R^n(G\circ F)$ are computed on injective resolutions.
An object $B\in\mathcal B$ is *$G$-acyclic* if $R^qG(B)=0$ for
$q>0$, and $(F,G)$ is a *composable pair with acyclicity* if $F(I)$
is $G$-acyclic for every injective $I\in\mathcal A$.

For a first-quadrant double complex $D^{\bullet,\bullet}$ in
$\mathcal C$, let $\operatorname{Tot}(D)$ be its total complex.
Filtering $\operatorname{Tot}(D)$ by either degree gives a bigraded exact
couple, and its derived couples give the two spectral sequences of $D$;
both abut to $H^\bullet(\operatorname{Tot}D)$ with the image filtration

$$
F^pH^n=\operatorname{im}\bigl(H^n(F^p\operatorname{Tot}D)
\longrightarrow H^n(\operatorname{Tot}D)\bigr),
$$

which in the first quadrant is finite in each degree, so that convergence
is automatic. (Blueprint 05,
`def-sp-composite-acyclicity`, `def-sp-exact-couple`,
`def-sp-image-filtration`, `def-sp-convergence`; the
étale substitution $\mathcal A=\mathrm{Ab}(X_{\Et})$, $F=f_*$, $G=h_*$
is `def-sp-etale-dictionary`.)
