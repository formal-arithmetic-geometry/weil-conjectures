+++
id = "def-pod-conventions"
kind = "definition"
title = "Poincare duality conventions"
order = 2091
uses = ["cor-pur-finite-stage-smooth-dualizing-complex", "def-coefficient-twists-detailed", "def-compact-support-direct-image-detailed", "def-trf-frobenius-operators", "def-weil-algebraically-closed-coefficients", "def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-adjoint-admissibility", "def-weil-exceptional-inverse-image", "def-weil-finite-coefficient-point", "def-weil-finite-field-fiber", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-frobenius-coefficient-twists", "def-weil-geometric-hypotheses", "def-weil-global-geometric-frobenius", "def-weil-ordinary-compact-cohomology", "def-weil-pbc-proetale-site", "def-weil-weil-sheaf-complex"]
+++
Fix the global finite-field datum
$p,a,q,k_0,k$, where $q=p^a$, a prime $\ell\neq p$, a finite
extension $E/\Ql$ contained in a fixed algebraic closure $\Qlb$, with
valuation ring $\mathcal O_E$, a uniformizer $\varpi_E$, and an
integer $n\in\mathbf Z_{\geq1}$. Put $A=A_{E,n}$. Let $X_0$ be a
smooth, separated finite-type, geometrically
connected $k_0$-scheme of pure dimension $d\in\mathbf Z_{\geq0}$ (not
necessarily proper), put
$X=X_0\times_{k_0}k$, set $s=\Spec k$, and let
$a_X:X\to s$ be the structure morphism, assumed
exceptional-adjoint
admissible at every finite coefficient stage. On the
small pro-etale site of $X$,
use

$$
D^b_{ctf}(X,\Lambda)\qquad(\Lambda\in\{A,\mathcal O_E,E,\Qlb\}),
$$

the bounded
constructible and finite-Tor
categories, the
derived pullback, tensor,
and internal Hom, the
derived direct image, the
compact-support direct image,
and the exceptional inverse
image, with the constructions and adjunctions of those definitions;
in particular

$$
\omega_{X,\Lambda}=Ra_X^!\Lambda
$$

with $Rf_!\dashv Rf^!$, and the
ordinary and
compact-support cohomology are

$$
R\Gamma(X,K),\ \ R\Gamma_c(X,K),\ \ H^i(X,K),\ \ H_c^i(X,K).
$$

Use the coefficient twists
$K(m)=K\otimes^L_{\Lambda_X}\Lambda(m)$ and the
Frobenius normalization
on them ($q^{-m}$ on $\Lambda(m)$, $q^m$ on $\Lambda(-m)$). At the
point $s$, the finite
coefficient categories are $D^b_{\mathrm{fin}}(A_{E,n})$,
$D^b_{\mathrm{fg}}(\mathcal O_E)$, $D^b_{\mathrm{fd}}(E)$, and the
common-stage category of
algebraically
closed coefficients; write $A$ for the coefficient ring of the point.
For $C$ in such a category put

$$
C^\vee=R\operatorname{Hom}_A(C,A).
$$

The $F$-operators are the
global geometric Frobenius operators of [def-weil-global-geometric-frobenius] on the
global sections, with the
strict Weil structures of [def-pur-tate-datum] and the iterates of
[def-trf-frobenius-operators]. The canonical orientation is the one
of the smooth
dualizing complex supplied by the purity chapter ([thm-pur-diagonal-dualizing-object]; see
the interface record [rem-sf-orientation-pointer]): the canonical choice

$$
\eta_X:\omega_{X,\Lambda}\xrightarrow{\ \sim\ }\Lambda_X(d)[2d].
$$

For
$K\in D^b_{ctf}(X,\Lambda)$ put

$$
\mathbb D_XK=R\mathcal Hom_X\bigl(K,\omega_{X,\Lambda}\bigr),
\qquad
K^\vee=R\mathcal Hom_X\bigl(K,\Lambda_X\bigr),
$$

the *Verdier dual* and the *coefficient dual*.

Properness of $X_0$ is not part of this setting: the duality statements
formulated in it use compact supports $R\Gamma_c$ against ordinary
cohomology $R\Gamma$ and never compare the two. Properness is imposed
explicitly, and only, in the statements that need
$Ra_{X!}\cong Ra_{X*}$ (the untwisted trace on $H^{2d}$, the trace–cup
pairing on ordinary cohomology, and proper Poincare duality).
