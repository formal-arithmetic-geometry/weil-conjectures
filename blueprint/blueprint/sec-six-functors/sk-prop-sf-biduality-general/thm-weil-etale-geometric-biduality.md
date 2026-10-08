+++
id = "thm-weil-etale-geometric-biduality"
kind = "theorem"
title = "Finite-stage etale Verdier biduality"
order = 2128
uses = ["lem-fin-coordinate-generic-dimension", "lem-sf-etale-direct-image-vanishing", "lem-weil-coefficient-frobenius", "lem-weil-delta-proper-pushforward", "lem-weil-delta-restriction", "lem-weil-duality-pairing", "lem-weil-geometric-generic-duality", "lem-weil-verdier-preservation-strata", "thm-nagata-compactification", "thm-sf-direct-image-tor-amplitude", "thm-sp-truncation-e2"]
+++
For every separated finite-type $X/k$, the natural map

$$
\delta_K:K\longrightarrow D_XD_XK
\qquad(K\in D^b_{ctf}(X_{\Et},A))
$$

is an isomorphism. Consequently $D_X$ is an exact contravariant
anti-equivalence of $D^b_{ctf}(X_{\Et},A)$.

## Proof

Induct on $d=\dim X$, simultaneously for all algebraically closed
fields of characteristic different from $\ell$. Dimension zero
reduces to finitely many geometric points, since nilpotent thickenings
do not change the etale site. There the assertion is perfect derived
coefficient biduality, [lem-weil-coefficient-frobenius].

By [lem-weil-delta-restriction] the assertion is local on $X$.
We may first choose an affine open and then a proper compactification
$j:X\hookrightarrow\overline X$, using
[thm-nagata-compactification], and replace $\overline X$ by the
scheme-theoretic closure of $X$. Its dimension is $d$. Extension by zero
$j_!K$ is bounded constructible with the same Tor interval, as is
checked on stalks. Restriction of its double-dual map is the original
map. It therefore suffices to prove the assertion for proper $X$
of dimension $d$.

Set $\Delta=\operatorname{Cone}(\delta_K)$. Preservation from
[lem-weil-verdier-preservation-strata] makes $\Delta$ bounded
constructible. We show that every cohomology sheaf of $\Delta$
vanishes at every nonclosed point $x$. Choose an affine open
$V\ni x$. Since $x$ is nonclosed, $\kappa(x)/k$ has positive
transcendence degree. Among a finite set of algebra generators of
$\Gamma(V,\mathcal O_V)$, some $t$ has transcendental image in
$\kappa(x)$. The resulting map $V\to\mathbf A^1_k$ sends
$x$ to the generic point. Its generic fibre has dimension at most
$d-1$, by the dimension argument of
[lem-fin-coordinate-generic-dimension]: components with constant
$t$ disappear, and a dominant component loses one dimension.
Algebraic field extension preserves this dimension bound.

The induction hypothesis over $\overline{k(t)}$, together with
[lem-weil-geometric-generic-duality], says that the restriction of
$\delta_{K|_V}$ to the geometric generic fibre is an isomorphism.
Every geometric point above $x$ factors through such a fibre after
choosing an algebraic closure of $k(t)$ in its algebraically closed
residue field. Hence $\Delta$ has zero stalk at $x$.
Each of its finitely many cohomology sheaves has constructible support,
and a constructible subset of a Noetherian finite-type $k$-scheme
containing only closed points is finite: in a finite locally closed
decomposition, a positive-dimensional piece would contain a nonclosed
generic point. Thus all the cohomology of $\Delta$ is supported
on one finite set of closed points.

Write $a:X\to\operatorname{Spec}k$. The direct-image preservation
in [thm-sf-direct-image-tor-amplitude], with
[lem-sf-etale-direct-image-vanishing], makes $Ra_*K$ a perfect
coefficient complex. Its double-dual map is an isomorphism by
[lem-weil-coefficient-frobenius]. Proper compatibility of
evaluation, [lem-weil-delta-proper-pushforward], therefore gives
$Ra_*\Delta=0$. For a sheaf supported on finitely many closed
points over the algebraically closed field $k$, global sections are
the finite direct sum of its stalks and higher cohomology vanishes.
The truncation spectral sequence of [thm-sp-truncation-e2] thus
identifies

$$
H^qRa_*\Delta=\Gamma(X,\mathcal H^q\Delta)
=\bigoplus_x(\mathcal H^q\Delta)_{\bar x}.
$$

Every summand vanishes, so $\Delta=0$. This completes the induction.
Preservation was proved before the induction; together with the natural
evaluation of [lem-weil-duality-pairing], $D_X^2\cong\mathrm{id}$
therefore gives the claimed anti-equivalence.
