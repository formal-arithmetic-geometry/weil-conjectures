+++
id = "lem-wf-curve-normal-smooth-compactification"
kind = "lemma"
title = "Smooth proper compactification of a normal finite-field curve"
order = 2613
uses = ["def-sc-normalization", "def-weil-pbc-scheme-conventions", "lem-sc-dim0-finite", "lem-sc-normal-dim1-dvr", "lem-sc-normalization-properties", "lem-wf-finite-field-curve-quasi-projective"]
+++
Let $k_0=\mathbf F_q$, and let $U_0$ be a normal, geometrically
connected separated scheme of
finite type over $k_0$, pure of dimension one. Then $U_0$ is smooth
over $k_0$, and there are a smooth projective geometrically connected
curve $C_0/k_0$ and a dense open immersion

$$
j_0:U_0\hookrightarrow C_0
$$

whose reduced complement $D_0=(C_0-U_0)_{\mathrm{red}}$ is finite over
$k_0$. The scheme-theoretic terminology is that of
[def-weil-pbc-scheme-conventions].

## Proof

Because $U_0$ is normal, its irreducible components are disjoint open
and closed subsets: two different components cannot meet at a point whose
local ring is a domain. Geometric connectedness implies connectedness, so
there is only one component and $U_0$ is integral. At a closed point its
local ring is a one-dimensional noetherian normal local domain, hence a
discrete valuation ring by [lem-sc-normal-dim1-dvr], and therefore a
regular local ring because a DVR has principal maximal ideal and Krull
dimension one; the local ring at the
generic point is a field. Thus $U_0$ is regular. Since the finite field
$k_0$ is perfect, a regular finite-type $k_0$-scheme is smooth
over $k_0$: the standard regular–smooth criterion over a perfect field
applies
(*reference: Stacks Project, Commutative Algebra, Lemma 10.140.5,
[Tag 00TV](https://stacks.math.columbia.edu/tag/00TV)*).

By [lem-wf-finite-field-curve-quasi-projective], choose a locally
closed immersion $U_0\hookrightarrow\mathbf P^N_{k_0}$ and let $X_0$ be
the scheme-theoretic closure of its image. It is an integral projective
curve and $U_0$ is open in $X_0$.
Let

$$
\nu:C_0:=X_0^\nu\longrightarrow X_0
$$

be the normalization in the common function field, in the sense of
[def-sc-normalization]. By
[lem-sc-normalization-properties](a)–(b), the map $\nu$ is
finite, $C_0$ is proper, and $\nu$ is an isomorphism over the normal
open $U_0$. Hence $U_0\hookrightarrow C_0$ is a dense open immersion.
The finite map $\nu$ is projective (Stacks Project, Morphisms,
Lemma 29.45.16, [Tag 0B3I](https://stacks.math.columbia.edu/tag/0B3I)),
and the composite $C_0\to X_0\to\operatorname{Spec}(k_0)$ is therefore
projective. Thus $C_0$ is projective, not merely proper.
The same local argument as in the first paragraph shows that the normal
curve $C_0$ is regular, hence smooth over the perfect field $k_0$.

The complement has dimension zero, and is therefore a finite set of closed
points by [lem-sc-dim0-finite]; its reduced induced subscheme $D_0$
is consequently finite over $k_0$. Because $k_0$ is perfect and $D_0$
is reduced, $D_0\to\operatorname{Spec}(k_0)$ is finite etale. Thus the
compactification, boundary, and all maps used below are defined over $k_0$
and are Frobenius-equivariant. Finally put
$C=C_0\times_{k_0}\overline{k}_0$ and
$U=U_0\times_{k_0}\overline{k}_0$. The open $U$ is connected by
geometric connectedness and is dense in $C$. The closure of a connected
subset is connected, so $C$ is connected. This says exactly that $C_0$
is geometrically connected.
