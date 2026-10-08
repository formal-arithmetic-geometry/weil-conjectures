+++
id = "lem-amb-etale-adjoint-locality"
kind = "lemma"
title = "Etale localization of the ambient adjoint"
order = 1566
uses = ["def-amb-etale-compact-support", "def-asd-compactifiable", "def-weil-pbc-derived-categories", "def-weil-scheme-morphism-properties", "lem-amb-etale-compact-comparisons", "thm-amb-etale-exceptional-adjoint"]
+++
For a separated etale morphism $u:U\to X$ of finite type,
$u_!$ is exact and is left adjoint to $u^*$ on the whole
ordinary derived categories. If $f$ and $fu$ are
compactifiable, there is a canonical isomorphism

$$
u^*f^\times K\cong(fu)^\times K.
$$

The notation refers to ordinary etale compact supports.

## Proof

An etale morphism is a local homeomorphism of etale topoi.
For an etale test object $V\to X$, the sheaf $u_!F$
consists of sections on $U\times_XV$ with support proper
over $V$; after an etale covering which separates any finite
set of support points, this is the direct sum of the sections on
the corresponding sheets. This description is independent of
the covering by sheaf descent. It gives
$(u_!F)_{\bar x}=\bigoplus_{\bar z\in U_{\bar x}}F_{\bar z}$,
so $u_!$ is exact. Maps from these sums to $G$ are
precisely maps $F\to u^*G$, first on separated sheets and
then by sheaf descent. Thus $u_!\dashv u^*$ already on
sheaves. Both functors are exact, so the adjunction descends
termwise to ordinary derived categories.

For any complex $M$ on $U$, use the ambient adjunction
of [thm-amb-etale-exceptional-adjoint] and the composition
of compact supports in [lem-amb-etale-compact-comparisons]:

$$
\begin{split}
\operatorname{Hom}_U(M,u^*f^\times K)
&\cong\operatorname{Hom}_X(u_!M,f^\times K)\\
&\cong\operatorname{Hom}_S(Rf_!u_!M,K)\\
&\cong\operatorname{Hom}_S(R(fu)_!M,K).
\end{split}
$$

Yoneda gives the displayed isomorphism and its compatibility
with units, counits, and further etale localization.
