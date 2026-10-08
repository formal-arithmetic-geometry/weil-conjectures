+++
id = "thm-sc-proper-cohomology"
kind = "theorem"
title = "Kummer computation on a proper curve"
order = 1024
uses = ["def-sc-curves", "def-sc-kummer-sequence", "def-sc-mu-trivialization", "lem-sc-cohomological-dimension", "lem-sc-kummer-les", "lem-sc-pic-proper-ntorsion", "lem-sc-primitive-root"]
+++
Let $k$ be algebraically closed, let $C$ be a
smooth proper connected curve of genus $g$ over
$k$, and let $n\geq1$ be prime to $\operatorname{char}k$.
Then, under the canonical trivialization
$\theta_\zeta$ for a primitive root $\zeta$
([def-sc-mu-trivialization], existence by
[lem-sc-primitive-root]), the constant sheaf
$\mathbf F_n$ satisfies

$$
H^0(C_{\Et},\mathbf F_n)\cong\mathbf Z/n\mathbf Z,\qquad
H^1(C_{\Et},\mathbf F_n)\cong(\mathbf Z/n\mathbf Z)^{2g},\qquad
H^2(C_{\Et},\mathbf F_n)\cong\mathbf Z/n\mathbf Z,
$$

and $H^q(C_{\Et},\mathbf F_n)=0$ for $q>2$.

## Proof

Use $\theta_\zeta$ ([def-sc-mu-trivialization], with the
primitive root of [lem-sc-primitive-root]) to replace
$\mathbf F_n$ by $\mu_n$. By [lem-sc-kummer-les]
(applied to the exact Kummer sequence
[def-sc-kummer-sequence]; the unit group of the proper connected
curve is $k^\times$, $n$-divisible since $k$ is algebraically
closed, so the exact sequence of the lemma degenerates),

$$
H^1(C,\mu_n)=\operatorname{Pic}(C)[n],\quad
H^2(C,\mu_n)=\operatorname{coker}(n:\operatorname{Pic}(C)\to
\operatorname{Pic}(C)),
$$

which by [lem-sc-pic-proper-ntorsion] are
$(\mathbf Z/n\mathbf Z)^{2g}$ and
$\mathbf Z/n\mathbf Z$; $H^0(C,\mu_n)=\mu_n(k)=\mathbf Z/n\mathbf Z$
by [lem-sc-primitive-root]. The vanishing for $q>2$ is
[lem-sc-cohomological-dimension].
