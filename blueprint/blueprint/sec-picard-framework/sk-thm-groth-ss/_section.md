+++
id = "sk-thm-groth-ss"
kind = "section"
title = "Grothendieck spectral sequence and its Leray specialization"
order = 601
uses = ["sk-def-groth-ss"]
lean = ["CategoryTheory.Functor.exists_grothendieckSpectralSequence"]
+++
*Theorem (sketch).*

Let $X\xrightarrow{f}Y\xrightarrow{h}Z$ be morphisms of sites (or
schemes with their étale or small Zariski sites). For an abelian
sheaf $F$ on $X$, since $f_*$ carries injectives
to $h_*$-acyclics ($f_*$ is right adjoint to the exact $f^{-1}$, so
it preserves injectives), there is a functorial spectral sequence

$$
E_2^{p,q}=R^ph_*R^qf_*F\ \Longrightarrow\ R^{p+q}(hf)_*F,
$$

compatible with base change.

For $Z$ the punctual site, so that $h_*=\Gamma(Y,-)$, this is the
*Leray* spectral sequence

$$
E_2^{p,q}=H^p(Y,R^qf_*F)\ \Longrightarrow\ H^{p+q}(X,F),
$$

with the same functoriality and base-change compatibility. In
particular this includes $Y_{\mathrm{zar}}$ and $X_{\mathrm{zar}}$
for a morphism of schemes. For proper $f$ and coherent $F$ the
Zariski sequence is the spectral sequence of
$\Gamma(Y,-)\circ f_*$ on $\cO$-modules. The reduction of proper
base change uses the general composite form.

## Proof

*Step 1 (the acyclicity hypothesis).* The functor $f^{-1}$ is exact
and left adjoint to $f_*$, so $f_*$ carries injectives to injectives, and
an injective sheaf is $h_*$-acyclic. Hence $(f_*,h_*)$ is a composable
pair with acyclicity in the sense of [sk-def-groth-ss].

*Step 2 (the double complex).* Choose an injective resolution
$F\to I^\bullet$ and put $C^\bullet=f_*I^\bullet$, so that
$R^qf_*F=\mathcal H^q(C^\bullet)$. Let $C^{\bullet,\bullet}$ be a
Cartan–Eilenberg resolution of $C^\bullet$ and set $D^{p,q}=h_*C^{p,q}$,
a first-quadrant double complex.

*Step 3 (filtration by the second degree).* This filtration has
$E_1^{p,q}=R^qh_*\bigl(f_*I^p\bigr)$, which vanishes for $q>0$ by
Step 1. The sequence therefore collapses on the bottom edge, and since
$(hf)_*=h_*f_*$,

$$
H^n(\operatorname{Tot}D)\cong
\mathcal H^n\bigl(h_*f_*I^\bullet\bigr)=R^n(hf)_*F .
$$

*Step 4 (filtration by the first degree).* By the defining property
of a Cartan–Eilenberg resolution, the other filtration of the same
double complex has

$$
E_2^{p,q}=R^ph_*\bigl(R^qf_*F\bigr).
$$

Both filtrations abut to $H^\bullet(\operatorname{Tot}D)$, which Step 3
identifies with $R^{p+q}(hf)_*F$; this is the displayed spectral
sequence, with the image filtration of [sk-def-groth-ss] on the
abutment, finite in each degree.

*Step 5 (functoriality and base change).* The construction depends
only on the chosen resolutions, hence is functorial in $F$. A cartesian
square induces compatible maps of the two double complexes, hence a
morphism of exact couples and so of spectral sequences; taking
$\alpha=g'^{-1}$ and $\gamma=g^{-1}$ gives the asserted compatibility
with base change.

*Step 6 (the Zariski coherent case).* On $\cO$-modules the
composite is $\Gamma(Y,-)\circ f_*=\Gamma(X,-)$, but $f^*$ is no
longer exact, so acyclicity is supplied differently: an injective
$\cO_X$-module $\cI$ is flasque (apply injectivity to
$j_!\cI|_U\to\cI$ for $j:U\hookrightarrow X$ open to extend a section
over $U$), $f_*$ preserves flasqueness, and a flasque module is
$\Gamma$-acyclic on every open, hence $f_*$-acyclic. So
$(f_*,\Gamma(Y,-))$ is again a composable pair with acyclicity in the
sense of [sk-def-groth-ss], and the construction applies verbatim.
For proper $f$ and coherent $F$, this gives the coherent sequence
named in the statement.

This is Blueprint 05, `thm-sp-grothendieck` together with
`thm-sp-grothendieck-base-change`, read through the étale
dictionary `def-sp-etale-dictionary`; the Cartan–Eilenberg input
of Step 2 is `thm-sp-if-e1` and the collapse of Step 3 is
`lem-sp-edge-collapse`.

The topos form of the sequence and of the acyclicity criterion are
Stacks, Cohomology on Sites, Lemmas 21.14.5/21.14.6
([`0732`](https://stacks.math.columbia.edu/tag/0732),
[`0733`](https://stacks.math.columbia.edu/tag/0733)), and
for ringed spaces Lemmas 20.13.4/20.13.8
([`01F2`](https://stacks.math.columbia.edu/tag/01F2),
[`01F6`](https://stacks.math.columbia.edu/tag/01F6)); the
detailed form is Blueprint 17, `pqf-lem-leray`.

Uses: [sk-def-groth-ss]
