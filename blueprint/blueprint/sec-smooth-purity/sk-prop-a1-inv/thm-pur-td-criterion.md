+++
id = "thm-pur-td-criterion"
kind = "theorem"
title = "Trace–diagonal criterion"
order = 1956
uses = ["cor-sf-ambient-adjoint-discharge", "def-pur-conventions", "def-pur-td-datum", "def-weil-ambient-exceptional-adjoint", "def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-exceptional-adjoint-admissibility", "def-weil-exceptional-inverse-image", "def-weil-pbc-proetale-site"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $f:X\to Y$ be separated finite type; the
ambient exceptional right
adjoint datum of [def-weil-ambient-exceptional-adjoint] is not assumed,
the right adjoint $Rf^!$ of $Rf_!$ on the bounded constructible and
finite-Tor coefficients of this chapter being the theorem
[cor-sf-ambient-adjoint-discharge] there. Let
$L\in D^b_{ctf}(X,\Lambda)$ be tensor-invertible, and let
$(\operatorname{tr}_f,\operatorname{cl}_\Delta)$ be a
trace–diagonal datum. If the two
triangular composites are the identity,
naturally in $A$ and $K$, then:

$$
Rf_!\;\dashv\;G_L,
$$

i.e. $G_L$ is a right adjoint of $Rf_!$. Consequently there is a
unique isomorphism of functors

$$
Rf^!(-)\;\xrightarrow{\ \sim\ }\;Lf^*(-)\otimes^L_{\Lambda_X}L
$$

compatible with the counits; in particular

$$
\omega_f=Rf^!\Lambda_Y\;\cong\;L.
$$

## Proof

By [def-pur-td-datum], $\epsilon$ and $\eta$ are morphisms of
the ordinary functors $Rf_!$ and $G_L$, and the two assumed
equations are precisely the two triangular identities of an
adjunction. Thus $G_L$ is right adjoint to $Rf_!$. The functor
$Rf^!$ is another right adjoint of $Rf_!$, by the ambient datum of
[def-weil-ambient-exceptional-adjoint] together with
[def-weil-exceptional-inverse-image] — on the bounded constructible
and finite-Tor coefficients that occur here that datum is the theorem
[cor-sf-ambient-adjoint-discharge], so no hypothesis is used —
the uniqueness of right
adjoints gives the displayed identification, compatible with the
counits by construction. Taking the value at $\Lambda_Y$ gives
$\omega_f\cong L$, and hence the identification
$Rf^!\cong Lf^*(-)\otimes^L L$.
Consequently, for bounded constructible $L$, the identification
exhibits $Rf^!$ as an exact functor carrying bounded constructible
complexes with cohomology in an interval $[a,b]$ into those with
cohomology in $[a+p,b+q]$, where $[p,q]$ is a cohomological interval
for $L$: clause (2) of
[def-weil-exceptional-adjoint-admissibility] holds for $f$
whenever such a trace–diagonal datum and such an $L$ exist. No clause
of that definition is assumed in the argument.
