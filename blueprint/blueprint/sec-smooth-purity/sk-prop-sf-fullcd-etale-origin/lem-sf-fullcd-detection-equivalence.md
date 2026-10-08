+++
id = "lem-sf-fullcd-detection-equivalence"
kind = "lemma"
title = "The full cohomological-dimension condition is a bound on the pro-étale cohomology of the base-changed source"
order = 1794
uses = ["cor-sf-fullcd-weakly-contractible-test", "def-weil-derived-cohomology-sheaves", "def-weil-full-cohomological-dimension", "def-weil-pbc-direct-image", "def-weil-pbc-proetale-site", "lem-sf-proetale-vanishing-detection", "thm-sp-grothendieck"]
+++
In the setting of [def-weil-full-cohomological-dimension] the condition
$\operatorname{FullCD}(p,A;c)$ is equivalent to the following statement: for
every object $V\to Y$ of $Y_{\Proet}$
([def-weil-pbc-proetale-site]) and every sheaf $\mathcal F$ of
$A$-modules on $\overline X_{\Proet}$, with $p_V$ and $(p_V)_*$ as in
the derived direct image of [def-weil-pbc-direct-image], one has

$$
H^r\bigl((\overline X\times_YV)_{\Proet},\mathcal F|_{\overline X\times_YV}\bigr)=0
\qquad(r\in\mathbf Z,\ r>c),
$$

the cohomology being that of the small pro-étale site of the base-changed
source.

## Proof

*Auxiliary fact.* Let $T$ be a scheme, let $W\to T$ be an object of
$T_{\Proet}$ every pro-étale covering family of which contains a member
admitting a section – a weakly contractible object, the objects whose
existence in abundance is Stacks Project, Pro-étale Cohomology, Lemma
61.13.4, [Tag 0990](https://stacks.math.columbia.edu/tag/0990), and
which are the ones used in [lem-sf-proetale-vanishing-detection]. Then
$H^q(W,\mathcal G)=0$ for every $q>0$ and every sheaf $\mathcal G$ of
$A$-modules on $T_{\Proet}$: the functor
$\mathcal G\mapsto\mathcal G(W)$ is left exact, and it is right exact
because for a surjection $\mathcal G\to\mathcal G'$ and a section of
$\mathcal G'$ over $W$ there is a covering family of $W$ on which the
section lifts, and one of its members admits a section $W\to W_i$ along
which the lift pulls back. Hence the global-sections functor of the site
over $W$ is exact and its higher derived functors vanish. In particular
the Leray spectral sequence of the composite
$\Gamma\bigl((\overline X\times_YV)_{\Proet},-\bigr)= \Gamma\bigl(V_{\Proet},-\bigr)\circ R(p_V)_*$, which exists by
[thm-sp-grothendieck], has
$E_2^{p,q}=H^p\bigl(V_{\Proet},R^q(p_V)_*(\mathcal F|_{\overline X\times_YV})\bigr)$ and therefore collapses at $q=0$ for such a $V$:

$$
H^r\bigl((\overline X\times_YV)_{\Proet},\mathcal F|_{\overline X\times_YV}\bigr)
\cong H^r\bigl(V_{\Proet},R(p_V)_*(\mathcal F|_{\overline X\times_YV})\bigr)
=\bigl(\mathcal H^r(R(p_V)_*(\mathcal F|_{\overline X\times_YV}))\bigr)(V).
$$

*The condition implies the vanishing.* Assume
$\operatorname{FullCD}(p,A;c)$. By its relative clause the sheaves
$\mathcal H^q(R(p_V)_*(\mathcal F|_{\overline X\times_YV}))$
([def-weil-derived-cohomology-sheaves]) vanish for $q>c$; the Leray
spectral sequence of the composite then has $E_2^{p,q}=0$ for $q>c$,
whence $H^r=0$ for $r>c$, for *every* base change $V\to Y$.
*The vanishing implies the condition.* Assume the vanishing of the
statement. Fix a base change $V\to Y$ and a sheaf $\mathcal F$ of
$A$-modules on $\overline X_{\Proet}$; put
$\mathcal Q^r=\mathcal H^r(R(p_V)_*(\mathcal F|_{\overline X\times_YV}))$. For an affine weakly contractible object $W\to V$ of
$V_{\Proet}$ the object $W\to Y$ is a weakly contractible object of
$Y_{\Proet}$: a pro-étale covering family of $W$ over $Y$ is one
over $V$, and such a family contains a member admitting a section, so
$W\to V$ may be replaced by $W$ in the auxiliary fact and the
identification above applies to the base change $\overline X\times_YW\to W$.
Hence $\mathcal Q^r(W)=H^r\bigl((\overline X\times_YW)_{\Proet},\mathcal F|_{\overline X\times_YW}\bigr)=0$ for $r>c$. The affine weakly
contractible objects of $V_{\Proet}$ detect the vanishing of a sheaf by
[lem-sf-proetale-vanishing-detection](i), so $\mathcal Q^r=0$ for
$r>c$; as $V$ was arbitrary this is
$\operatorname{FullCD}(p,A;c)$, which is also the form of the test recorded
in [cor-sf-fullcd-weakly-contractible-test].
