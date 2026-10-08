+++
id = "lem-pc-euler-additive"
kind = "lemma"
title = "Additivity of the Euler characteristic"
order = 739
uses = ["def-pc-derived-direct-image", "def-pc-morphism-conventions", "lem-pc-coherent-hi"]
+++
Let $k$ be a field, $X$ a proper scheme over $k$, and let

$$
0\to\mathcal{F}_1\to\mathcal{F}_2\to\mathcal{F}_3\to0
$$

be a short exact sequence of coherent $\mathcal{O}_X$-modules. Then

$$
\chi(X,\mathcal{F}_2)=\chi(X,\mathcal{F}_1)+\chi(X,\mathcal{F}_3).
$$

Moreover, for a morphism $f:Y\to X$ of proper $k$-schemes and a
coherent $\mathcal{O}_Y$-module $\mathcal{G}$:

$$
\chi(Y,\mathcal{G})=\sum_{i\ge0}(-1)^i\chi(X,R^if_*\mathcal{G}).
$$

## Proof

The long exact cohomology sequence of the short exact sequence is

$$
0\to H^0(\mathcal{F}_1)\to H^0(\mathcal{F}_2)\to H^0(\mathcal{F}_3)\to H^1(\mathcal{F}_1)\to H^1(\mathcal{F}_2)
\to H^1(\mathcal{F}_3)\to\cdots,
$$

exact, terminates at both ends (finite support,
[lem-pc-coherent-hi] via the properness of $f$, and finite
dimensionality of the terms, [lem-pc-coherent-hi]), and the
alternating sum of the dimensions in an exact sequence of finite
dimensional vector spaces vanishes (rank–nullity, applied inductively
to the decompositions $0\to\operatorname{im}\to V\to\operatorname{im}'\to0$). Summing the
alternative signs over the long exact sequence gives

$$
0=\sum_i(-1)^i\bigl(\dim H^i(\mathcal{F}_1)-\dim H^i(\mathcal{F}_2)+\dim H^i(\mathcal{F}_3)\bigr),
$$

which is exactly $\chi(\mathcal{F}_1)-\chi(\mathcal{F}_2)+\chi(\mathcal{F}_3)=0$; this is the
first statement (Varieties, Lemma 33.33.2, Tag
[08AA](https://stacks.math.columbia.edu/tag/08AA)).

For the second statement, consider the Leray spectral sequence of $f$
(Cohomology, Lemma 20.13.4)

$$
E_2^{p,q}=H^p(X,R^qf_*\mathcal{G})\Longrightarrow H^{p+q}(Y,\mathcal{G}).
$$

All $R^qf_*\mathcal{G}$ are coherent ([lem-pc-coherent-hi]) and only
finitely many are nonzero, so each $E_2^{p,q}$ is finite dimensional
over $k$ and $E_2$ has finite support; the spectral sequence converges
to finite dimensional $H^n(Y,\mathcal{G})$ and the alternating sum over the
total degree equals the alternating sum of the $E_2$-terms (each
$E_r$-page's alternating total sum is invariant under the differentials
of the spectral sequence, as the pages are finite dimensional and the
differentials are the quotients with the same alternating total sum:
the standard invariance of the Euler characteristic in a spectral
sequence; Varieties, Lemma 33.33.5, Tag
[0BEK](https://stacks.math.columbia.edu/tag/0BEK)):

$$
\chi(Y,\mathcal{G})=\sum_{p,q}(-1)^{p+q}\dim_kE_2^{p,q}
=\sum_{q\ge0}(-1)^q\Bigl(\sum_p(-1)^p\dim_kH^p(X,R^qf_*\mathcal{G})\Bigr)
=\sum_{q\ge0}(-1)^q\chi(X,R^qf_*\mathcal{G}),
$$

as claimed.
