+++
id = "lem-sc-primitive-root"
kind = "lemma"
title = "Primitive roots of unity"
order = 928
uses = ["def-sc-curves", "def-sc-mu-trivialization"]
+++
Let $k$ be algebraically closed and let $n\geq1$ be prime to
$\operatorname{char}k$. Then $x^n-1$ has exactly $n$ distinct
roots in $k$, there is a primitive $n$-th root of unity
$\zeta\in\mu_n(k)$, and $\mu_n(k)\cong\mathbf Z/n\mathbf Z$ via
$\theta_\zeta$ ([def-sc-mu-trivialization]). If
$k\subseteq k'$ is an extension of algebraically closed fields, the
image of $\zeta$ in $k'$ is a primitive $n$-th root of unity,
so $\theta_\zeta$ is compatible with pullback along
$k\subseteq k'$.

## Proof

Since $n$ is prime to $\operatorname{char}k$, the polynomial
$x^n-1$ is separable (its derivative $nx^{n-1}$ is nonzero, and
$x^n-1$ and $nx^{n-1}$ are coprime); as $k$ is algebraically
closed it splits into $n$ distinct linear factors, giving a
primitive root $\zeta$ and $\mu_n(k)\cong\mathbf Z/n\mathbf Z$
via $\theta_\zeta$ ([def-sc-mu-trivialization]). The image of
a primitive root in a field extension is primitive (it has order
exactly $n$), which gives the compatibility with pullback.
