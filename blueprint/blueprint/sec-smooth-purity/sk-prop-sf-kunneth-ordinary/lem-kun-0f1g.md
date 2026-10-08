+++
id = "lem-kun-0f1g"
kind = "lemma"
title = "Detection of objects supported at closed points"
order = 1768
uses = ["def-kun-global-generated", "def-kun-rgamma-unbounded", "def-kun-separably-closed", "def-kun-support", "lem-kun-0bkz", "lem-kun-0f1f-gen", "lem-kun-0f1f-vanish", "lem-kun-d-zero-cohomology", "lem-kun-etale-lfp", "lem-kun-minimal-cohomology", "lem-kun-stalks-of-cohomology"]
+++
Let $K$ be a separably closed
field and $X$ a scheme of finite type over $K$. Let
$Q\in D(X_{\Et})$ and assume that $Q_{\bar x}\ne0$ only if $x$
is a closed point of $X$. Then

$$
Q=0\quad\Longleftrightarrow\quad H^i(X_{\Et},Q)=0\text{ for all }
i .
$$

(*Source:* Stacks Project, Tag
[0F1G](https://stacks.math.columbia.edu/tag/0F1G).)

## Proof

The implication from left to right is clear by functoriality of the
derived global sections of [def-kun-rgamma-unbounded].
Conversely, assume first that $Q$ is bounded below; this case
suffices for almost all applications. If $Q\ne0$, let $i$ be the
smallest integer with $\mathcal H^i(Q)\ne0$. Then
$H^i(X_{\Et},Q)=H^0(X_{\Et},\mathcal H^i(Q))$ by
[lem-kun-minimal-cohomology]. By
[lem-kun-stalks-of-cohomology] the support of
$\mathcal H^i(Q)$ is contained in the closed points of $X$, and
$\mathcal H^i(Q)\ne0$; by [lem-kun-0f1f-gen] this sheaf is
globally generated, hence admits a nonzero global section: the
evaluation map of [def-kun-global-generated] is an epimorphism
onto the nonzero sheaf, so it has a nonzero section of $F$ in its
image. Thus
$H^0(X_{\Et},\mathcal H^i(Q))\ne0$, contradicting the vanishing of
$H^i(X_{\Et},Q)$. Hence $Q=0$.

For the general case, let $\mathcal B\subset\Ob(X_{\Et})$ be the
quasi-compact objects. Every object of $X_{\Et}$ has a covering by
affine (hence quasi-compact) objects, so $\mathcal B$ is a basis
satisfying clause (1) of [lem-kun-0bkz]. An object
$U\in\mathcal B$ is quasi-compact and etale over $X$; since an
etale morphism is locally of finite presentation
([lem-kun-etale-lfp]), quasi-compactness implies that $U$ is of
finite type over $K$. If $u\in U$ lies in the support of
$\mathcal H^q(Q)|_U$, its image $x\in X$ lies in the support of
$\mathcal H^q(Q)$ and is closed. The residue extension
$\kappa(u)/\kappa(x)$ is finite separable because $U\to X$ is
etale; hence $\kappa(u)$ is finite over $K$, so $u$ is a closed
point of the finite type $K$-scheme $U$. Thus
[lem-kun-0f1f-vanish] applied to
$\mathcal H^q(Q)|_U$ gives $H^p(U_{\Et},\mathcal H^q(Q))=0$ for
all $p>0$ and all $q$. Hence the hypotheses of
[lem-kun-0bkz] are satisfied, and we conclude that
$H^q(U_{\Et},Q)=H^0(U_{\Et},\mathcal H^q(Q))$ for all
$U\in\mathcal B$, in particular for $U=X$. If
$H^i(X_{\Et},Q)=0$ for all $i$, then
$H^0(X_{\Et},\mathcal H^q(Q))=0$ for all $q$, so
$\mathcal H^q(Q)=0$ for all $q$ by the global-generation argument
of the previous paragraph ([lem-kun-0f1f-gen], noting that the
support of $\mathcal H^q(Q)$ is contained in the closed points);
by [lem-kun-d-zero-cohomology] this means $Q=0$.
