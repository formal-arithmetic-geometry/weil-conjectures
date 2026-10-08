+++
id = "sk-def-pic"
kind = "section"
title = "Picard group, degree, $\\Pic^0$"
order = 885
uses = ["sk-def-av-pic", "sk-def-curve", "sk-prop-hilbert90"]
lean = ["AlgebraicGeometry.Scheme.CohomologicalPicardGroup"]
+++
*Definition (sketch).*

For $C$ as in [sk-def-curve]: $\Pic(C)=H^1(C_{\Et},\mathbb G_m)$
(invertible $\mathcal O_C$-modules up to isomorphism). For $C$
smooth proper connected (in particular of dimension $1$,
[sk-def-curve]) there is a *degree* homomorphism
$\deg:\Pic(C)\to\Z$ and we set $\Pic^0(C)=\ker\deg$; for a group
$f$ and $n\ge1$, $f[n]$, $n\cdot f$, $f/n\cdot f$ denote kernel,
image and cokernel of the multiplication-by-$n$ map.

*Two facts are asserted, not defined, in the above and each
needs a proof of its own:*

- **(P1)** *(Equivalence of the definitions of $\Pic$.)* The
étale cohomology group $H^1(C_{\Et},\mathbb G_m)$ is canonically
isomorphic to the group of isomorphism classes of invertible
$\mathcal O_C$-modules under $\otimes$; equivalently, to
$H^1(C_{\mathrm{Zar}},\mathcal O_C^\times)$ and to the group of
divisors modulo principal divisors $\mathrm{Div}(C)/\mathrm{Princ}(C)$
when $C$ is moreover integral and regular.
- **(P2)** *(Well-definedness of $\deg$.)* For $C$ smooth
proper connected of dimension $1$,
$\deg\big(\sum_pn_p[p]\big)=\sum_pn_p[\kappa(p):k]$
kills principal divisors, hence descends to a homomorphism
$\Pic(C)\to\Z$; it is surjective and independent of all choices.

*Sketch.* The first two clauses of (P1) are
[sk-prop-hilbert90]: first cohomology of an abelian sheaf
classifies torsors, a $\mathbb G_m$-torsor is the sheaf of
isomorphisms of an invertible module, and the étale and the
Zariski computation agree by Hilbert 90 plus descent for
$\mathbb G_m$-torsors. The further identification with
$\mathrm{Div}(C)/\mathrm{Princ}(C)$ for $C$ integral regular is the
long exact cohomology sequence of the divisor sequence
[sk-prop-divisor-gen]: its middle term has
$H^1(C,i_*\mathbb G_{m,\eta})=0$, because Leray for $i:\eta\to C$
embeds this group into $H^1(\eta,\mathbb G_m)$, which vanishes by
the last assertion of [sk-prop-hilbert90]; so

$$
k(C)^\times=H^0(C,i_*\mathbb G_{m,\eta})
\xrightarrow{\ \operatorname{div}\ }
\mathrm{Div}(C)=H^0\Big(C,\bigoplus_pi_{p*}\Z\Big)
\longrightarrow H^1(C,\mathbb G_m)\longrightarrow0
$$

is exact, i.e. $\Pic(C)=\mathrm{Div}(C)/\mathrm{Princ}(C)$.

(P2) is the degree of a principal divisor
($\deg\operatorname{div}(f)=0$, Stacks `0BFL`): a nonconstant
$f\in k(C)^\times$ is a finite surjective morphism
$f:C\to\Pone$ of degree $d=[k(C):k(t)]$ with
$\operatorname{div}(f)=f^*[0]-f^*[\infty]$, and
$\deg(f^*D)=\deg f\cdot\deg D$ for a finite flat morphism $f$ of
proper curves and a divisor $D$ on its target (whereas pushforward
preserves degrees, $\deg(f_*D)=\deg D$, and $f_*f^*D=\deg f\cdot D$;
Stacks `02R3`, `0AZ0`), so
$\deg\operatorname{div}(f)=d-d=0$; a constant $f$ has
$\operatorname{div}(f)=0$. Hence $\deg$ descends to $\Pic(C)$, and
it is surjective because $C$, being of dimension $1$, has a closed
point $p$, and over algebraically closed $k$ a closed
point has $[\kappa(p):k]=1$ (for the zero-dimensional $C=\Spec k$,
$\Pic(C)=0$ and no surjective degree exists, which is why dimension
$1$ is required).

Uses: [sk-def-curve], [sk-prop-hilbert90]
