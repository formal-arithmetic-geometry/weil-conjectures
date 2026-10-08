+++
id = "sk-prop-sf-open-closed-triangle"
kind = "section"
title = "The open–closed triangle"
order = 1833
uses = ["sk-def-sf-operations", "sk-def-sf-setting"]
lean = ["AlgebraicGeometry.Etale.openClosedShortComplex", "AlgebraicGeometry.Etale.shortExact_openClosedShortComplex"]
+++
*Proposition (sketch).*

Let $j:U\hookrightarrow X$ and $i:Z\hookrightarrow X$ be complementary open and
closed immersions of finite-type $k$-schemes. For every
$M\in\Dctf(X,\Lambda)$ at a coefficient stage of [sk-def-sf-setting], the
extension and restriction maps of [sk-def-sf-operations] give a
distinguished triangle, natural in $M$,

$$
j_!j^*M\longrightarrow M\longrightarrow Ri_*i^*M\xrightarrow{+1}.
$$

For $M=\Lambda_X$ it reads
$j_!\Lambda_U\to\Lambda_X\to Ri_*\Lambda_Z\xrightarrow{+1}$.

## Proof

A closed immersion has exact direct image, so $Ri_*i^*M=i_*i^*M$ computed
termwise, and $j_!$ and $i^*$ are exact as well. It therefore suffices to
produce, for a single abelian sheaf $F$ of $\Lambda$-modules on $X_{\Et}$, the
short exact sequence

$$
0\longrightarrow j_!j^*F\longrightarrow F\longrightarrow i_*i^*F
\longrightarrow0,
$$

whose outer maps are the counit of $j_!\dashv j^*$ and the unit of
$i^*\dashv i_*$. Exactness is checked on geometric stalks, which are
conservative: at $\bar x$ over $U$ one has $(j_!j^*F)_{\bar x}=F_{\bar x}$ and
$(i_*i^*F)_{\bar x}=0$, since extension by zero restores the stalk on the open
and $i_*$ has support in $Z$; at $\bar x$ over $Z$ one has
$(j_!j^*F)_{\bar x}=0$ and $F_{\bar x}\to(i_*i^*F)_{\bar x}$ is the identity.
Applying this termwise to a bounded complex representing $M$ gives a short
exact sequence of complexes, hence the triangle; naturality is that of the
unit and the counit. The constant case is $F=\Lambda_X$, with
$j^*\Lambda_X=\Lambda_U$ and $i^*\Lambda_X=\Lambda_Z$.
This is the elementary sheaf sequence used in SGA 5, III, proof of 1.7.4.

Uses: `\Cref{sk-def-sf-operations}`, `\Cref{def-sf-setting}`
