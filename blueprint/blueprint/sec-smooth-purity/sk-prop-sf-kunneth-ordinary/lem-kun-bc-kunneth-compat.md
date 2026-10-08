+++
id = "lem-kun-bc-kunneth-compat"
kind = "lemma"
title = "Cohomology of the base change map through the Kunneth identification"
order = 1770
uses = ["def-kun-kunneth-map", "def-kun-projective", "def-kun-unbounded-exchange", "lem-kun-0f14b", "lem-kun-leray-bdd", "lem-kun-open-immersion-restriction", "lem-kun-tensor-unit"]
+++
Let $K$ be a separably closed field, let $j:U\to X$ be an open
immersion of schemes of finite type over $K$, let $Y$ be a
projective scheme over $K$, and let
$F$ be a sheaf of $\kunZn$-modules on $U_{\Et}$ with $n$
invertible in $K$. Consider the diagram

$$
\begin{array}{ccc}
Y\times_KX&\xleftarrow{\;h\;}&Y\times_KU\\
\Big\downarrow{\scriptstyle q}&&\Big\downarrow{\scriptstyle p}\\
X&\xleftarrow{\;j\;}&U .
\end{array}
$$

Then $\RGamma$ of the base change map
$q^{-1}Rj_*F\to Rh_*p^{-1}F$ of
[def-kun-unbounded-exchange], under the Kunneth isomorphisms of
[lem-kun-0f14b] (applied to the pairs $(Y,X)$ and $(Y,U)$
with the constant coefficient $\underline{\kunZn}$) and the Leray
identification of [lem-kun-leray-bdd], is identified with the
identity of
$\RGamma(Y_{\Et},\underline{\kunZn})\kunotimes{\kunZn}\RGamma(U_{\Et},F)$.

## Proof

By [def-kun-unbounded-exchange] the base change map is adjoint to
the counit composite
$p^{-1}j^{-1}Rj_*F\to p^{-1}F$ under
$h^{-1}\dashv Rh_*$ (using the cartesian identification
$h^{-1}q^{-1}\cong p^{-1}j^{-1}$). By [lem-kun-tensor-unit] we
have $q^{-1}Rj_*F\cong \pr_1^{-1}\underline{\kunZn}\kunotimes{\kunZn}\pr_2^{-1}Rj_*F$, and
applying $\RGamma$ to the base change map gives, through the
Kunneth maps of [def-kun-kunneth-map] (which are isomorphisms here by [lem-kun-0f14b]), the map

$$
\RGamma(Y_{\Et},\underline{\kunZn})\kunotimes{\kunZn}
\RGamma(X_{\Et},Rj_*F)
\longrightarrow
\RGamma(Y_{\Et},\underline{\kunZn})\kunotimes{\kunZn}
\RGamma(U_{\Et},F)
$$

induced by the counit $j^{-1}Rj_*F\to F$. Since
$\RGamma(X_{\Et},Rj_*F)=\RGamma(U_{\Et},F)$ through the Leray
identification of [lem-kun-leray-bdd] (the direct image
$j_*$ is the identity on $U$-sections, see
[lem-kun-open-immersion-restriction]; on the derived level the
induced map is the Leray identification by functoriality of the
adjunction and of [lem-kun-leray-bdd]), this induced map is the
identity, as asserted.
