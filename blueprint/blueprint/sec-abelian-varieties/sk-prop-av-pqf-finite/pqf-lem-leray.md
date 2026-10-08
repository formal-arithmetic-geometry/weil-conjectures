+++
id = "pqf-lem-leray"
kind = "lemma"
title = "Leray spectral sequence"
order = 536
uses = ["pqf-def-cohomology", "thm-sp-grothendieck"]
+++
Let $f:X\to Y$ be a morphism of schemes and $\mathcal F$ a
quasi-coherent $\mathcal O_X$-module. There is a spectral sequence

$$
E_2^{p,q}=\mathrm H^p\bigl(Y,R^qf_*\mathcal F\bigr)
\quad\Longrightarrow\quad \mathrm H^{p+q}(X,\mathcal F).
$$

(*Stacks Project, Cohomology of Sheaves, Lemma 20.13.4, Tag
[01F2](https://stacks.math.columbia.edu/tag/01F2).*)

## Proof

Apply the Grothendieck spectral sequence
[thm-sp-grothendieck] of the spectral-sequence chapter to the composable pair of
left exact functors $F=f_*:\mathcal O_X$-mod$\to\mathcal O_Y$-mod
(which is left exact: the functor of sections over the open
subschemes, exactness of $f_*$ on the left being the sheaf property)
and $G=\Gamma(Y,-):\mathcal O_Y$-mod$\to\mathbf{Ab}$.
The acyclicity condition holds: every injective
$\mathcal O_X$-module $\mathcal I$ is flasque (classical: for
$j:U\hookrightarrow X$ open, injectivity applied to the canonical
map $j_{!}\mathcal I|_U\to\mathcal I$ extends sections of
$\mathcal I$ over $U$ to all of $X$; equivalently, every
$\mathcal O_X$-module is a submodule of an injective module and
injective modules are the extension-closed objects), and a flasque
$\mathcal O_X$-module $\mathcal J$ is $f_*$-acyclic: its stalk
$(R^qf_*\mathcal J)_y=\varinjlim_{y\in V}\mathrm H^q(f^{-1}(V),\mathcal J)$ vanishes for $q>0$ since flasque
$\mathcal O_X$-modules are acyclic for $\Gamma$ on every open
subscheme (the standard flasque resolutions). By
[thm-sp-grothendieck] there is a functorial first-quadrant
spectral sequence with

$$
E_2^{p,q}=R^pG\bigl(R^qF(\mathcal F)\bigr)
=\mathrm H^p\bigl(Y,R^qf_*\mathcal F\bigr)
\;\Longrightarrow\;
R^{p+q}(G\circ F)(\mathcal F)=\mathrm H^{p+q}(X,\mathcal F),
$$

$G\circ F=\Gamma(Y,-)\circ f_*=\Gamma(X,-)$ being the global
sections of the source, and $R^qF(\mathcal F)=R^qf_*\mathcal F$,
$R^pG(-)=\mathrm H^p(Y,-)$ as the right derived functors fixed in
[pqf-def-cohomology]. This is the displayed spectral
sequence.
