+++
id = "lem-sc-torsor-h1"
kind = "lemma"
title = "First cohomology classifies torsors"
order = 880
uses = ["def-sc-gm-torsor", "lem-sc-ext-torsor"]
+++
Let $X$ be a scheme (for instance a curve $C$ as in
[def-sc-curves]) and $G$ a sheaf of
abelian groups on $X_{\Et}$. There is a canonical bijection

$$
H^1(X_{\Et},G)\cong\{\text{isomorphism classes of }G\text{-torsors}\}
$$

(torsors as in [def-sc-gm-torsor]), under which the group law of
$H^1$ corresponds to the contracted product
$(T,T')\mapsto T\wedge T':=(T\times T')/G$ (antidiagonal action) and
$0$ to the trivial torsor $G$. The same holds, with the same proof,
for an abelian sheaf on the Zariski site $X_{\mathrm{Zar}}$.

## Proof

By homological algebra,

$$
H^1(X_{\Et},G)=\operatorname{Ext}^1_{\mathrm{Ab}(X_{\Et})}(\mathbf Z_X,G):
$$

the functor $\operatorname{Hom}_{\mathrm{Ab}(X_{\Et})}(\mathbf Z_X,-)$ is canonically isomorphic to the global sections functor
$\Gamma(X_{\Et},-)$ (a homomorphism $\mathbf Z_X\to F$ is
determined by the image of $1$), so the first right derived
functor of this functor is $H^1(X_{\Et},-)$ on the one hand and
$\operatorname{Ext}^1(\mathbf Z_X,-)$ on the other. By
[lem-sc-ext-torsor], $\operatorname{Ext}^1(\mathbf Z_X,G)$ is
canonically the set of isomorphism classes of $G$-torsors, and the
group structures match: the Baer sum of two extensions $E,E'$ is
the subquotient $\{(e,e'):\pi(e)=\pi'(e')\}/\{(g,-g)\}$ of
$E\times E'$, and its preimage of $1$ is
$(\pi^{-1}(1)\times\pi'^{-1}(1))/G$, the contracted product of the
two torsors; the split extension $G\oplus\mathbf Z_X$ gives the
trivial torsor. Nothing in this argument (nor in
[lem-sc-ext-torsor]) uses more than that $\mathrm{Ab}(X_{\Et})$ is the
category of abelian sheaves on a site, so it applies verbatim to
$X_{\mathrm{Zar}}$.
