+++
id = "lem-pur-concentrated-complex-shift"
kind = "lemma"
title = "Complexes with cohomology in a single degree"
order = 2000
uses = ["def-pur-conventions", "def-sbc-smooth-morphisms", "def-weil-derived-cohomology-sheaves", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-cbc-proetale-stalk-conservative"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $T$ be a separated
finite-type $k$-scheme, let $K\in D^b_{ctf}(T,\Lambda)$ and let
$r\in\mathbf Z$.

1. *concentration in one degree.* If the
[def-weil-derived-cohomology-sheaves] cohomology sheaves
$\mathcal H^i(K)$ vanish for every $i\neq r$, then the
truncation triangles induce a canonical isomorphism
$$
K\;\xrightarrow{\ \sim\ }\;\mathcal H^r(K)[-r].
$$
1. *local constancy detected on an etale cover.* Let
$u:U\to T$ be a surjective
etale morphism and suppose
that $Lu^*K\cong\underline L[-r]$ for a
locally constant
$\Lambda$-sheaf $\underline L$ with finite stalks on $U$.
Then $\mathcal H^i(K)=0$ for every $i\neq r$, and
$\mathcal H^r(K)$ is locally constant with finite stalks on
$T$.

## Proof

Step 1: the truncation triangles. By
[def-weil-derived-cohomology-sheaves] the sheaves
$\mathcal H^i(K)$ are the cohomology sheaves for the standard
t-structure, and for every $a\in\mathbf Z$ there are exact triangles
$\tau_{\leq a-1}K\to\tau_{\leq a}K\to\mathcal H^a(K)[-a]\to$ and
$\tau_{\leq a}K\to K\to\tau_{\geq a+1}K\to$. A complex all of whose
cohomology sheaves vanish is zero in the derived category of
[def-weil-pbc-proetale-site], that category being the
localization at the quasi-isomorphisms. If therefore
$\mathcal H^i(K)=0$ for every $i\neq r$, then
$\tau_{\geq r+1}K\simeq0$ and $\tau_{\leq r-1}K\simeq0$, and the two
triangles exhibit $K$ and $\mathcal H^r(K)[-r]$ as models of one
and the same object; this is (1).
Step 2: an etale cover. Pullback of sheaves is exact, so the derived
pullback $Lu^*$ commutes with cohomology sheaves, and etale
morphisms are weakly etale, hence covering families in the sense of
[def-weil-pbc-proetale-site] (an etale morphism is flat with
flat diagonal, which is the description of weakly etale in
[def-weil-scheme-morphism-properties]); the description of etale
morphisms is that of [def-sbc-smooth-morphisms]. Since $u$ is a
member of a pro-etale covering family, inverse image along $u$
reflects vanishing of a sheaf, by clause (1) of
[lem-cbc-proetale-stalk-conservative]; as $Lu^*K\cong \underline L[-r]$ has cohomology only in degree $r$, the sheaves
$u^*\mathcal H^i(K)\cong\mathcal H^i(Lu^*K)$ vanish for $i\neq r$,
and therefore so do the sheaves $\mathcal H^i(K)$. For the remaining
degree, $u^*\mathcal H^r(K)\cong\underline L$ is constant along the
covering $u$, so $\mathcal H^r(K)$ is locally constant in the sense
recalled in [def-weil-scheme-morphism-properties]; the stalks of a
constructible object may be computed at geometric points, by part (3) of
[lem-cbc-proetale-stalk-conservative], and they are the stalks of
$\underline L$ there, hence finite. This is (2).
