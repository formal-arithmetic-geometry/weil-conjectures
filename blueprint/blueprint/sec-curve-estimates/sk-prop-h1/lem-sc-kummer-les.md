+++
id = "lem-sc-kummer-les"
kind = "lemma"
title = "Consequences of the Kummer sequence"
order = 929
uses = ["def-sc-curves", "def-sc-kummer-sequence", "lem-sc-brauer-zero", "lem-sc-h1-gm-pic", "lem-sc-kummer-exact", "lem-sc-primitive-root"]
+++
Let $C$ be a curve over algebraically
closed $k$ (not necessarily connected, reduced or smooth) and let $n$ be prime to $\operatorname{char}k$.
Assume $H^2(C_{\Et},\mathbf G_m)=0$
(for smooth connected $C$ this is [lem-sc-brauer-zero]). Then, under the canonical
identification of [lem-sc-h1-gm-pic], there is a canonical short
exact sequence

$$
0\to\mathcal O_C(C)^\times/\mathcal O_C(C)^\times{}^{\,n}
\to H^1(C_{\Et},\mu_n)\to\operatorname{Pic}(C)[n]\to0,
$$

and

$$
H^2(C_{\Et},\mu_n)=\operatorname{coker}\bigl(n:
\operatorname{Pic}(C)\to\operatorname{Pic}(C)\bigr),
$$

and, if $C$ is connected,
$H^0(C,\mu_n)=\mu_n(k)=\mathbf Z/n\mathbf Z$
([lem-sc-primitive-root]). In particular
$H^1(C_{\Et},\mu_n)=\operatorname{Pic}(C)[n]$ when
$\mathcal O_C(C)^\times$ is $n$-divisible (e.g. when
$C$ is proper and connected, so $\mathcal O_C(C)^\times=k^\times$ if $C$
is moreover reduced).

## Proof

Take the long exact sequence in cohomology of the exact
[def-sc-kummer-sequence] ([lem-sc-kummer-exact]):

$$
\begin{array}{l}
0\to H^0(C,\mu_n)\to H^0(C,\mathbf G_m)\xrightarrow{n}
H^0(C,\mathbf G_m)\to
H^1(C,\mu_n)\to H^1(C,\mathbf G_m)\xrightarrow{n}\\
\hphantom{0\to{}}
H^1(C,\mathbf G_m)\to H^2(C,\mu_n)\to H^2(C,\mathbf G_m)\to\cdots.
\end{array}
$$

Here $H^0(C,\mathbf G_m)=\mathcal O_C(C)^\times$ and $k$ is
algebraically closed, so $x\mapsto x^n$ is surjective on the
constant part $k^\times\subseteq\mathcal O_C(C)^\times$;
$H^1(C,\mathbf G_m)=\operatorname{Pic}(C)$ by
[lem-sc-h1-gm-pic]; and the term $H^2(C,\mathbf G_m)$ is zero
by assumption. Exactness of the sequence at
$H^1(C,\mu_n)$ and at $H^1(C,\mathbf G_m)$ therefore gives the
displayed short exact sequence and the displayed formula for
$H^2(C,\mu_n)$; for connected $C$ the $H^0$-term is
$\mu_n(k)=\mathbf Z/n\mathbf Z$ by
[lem-sc-primitive-root]. The last assertion follows because for
$C$ proper, connected and reduced the only units are the constants
$k^\times$, which are $n$-divisible since $k$ is algebraically
closed.
