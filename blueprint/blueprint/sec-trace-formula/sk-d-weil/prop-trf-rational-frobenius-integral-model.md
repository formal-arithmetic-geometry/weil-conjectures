+++
id = "prop-trf-rational-frobenius-integral-model"
kind = "theorem"
title = "Integral models of rational Frobenius operators"
order = 2301
tags = ["latex:proposition"]
uses = ["def-trf-coefficient-conventions", "def-trf-frobenius-coefficient-morphism", "def-trf-frobenius-operators", "def-trf-iterated-weil-map", "def-trf-scheme-frobenius", "def-weil-derived-complete-integral-detailed", "def-weil-derived-pullback-tensor-hom", "def-weil-global-geometric-frobenius", "def-weil-integral-rational-qbar-compact-support", "def-weil-pbc-adic-coefficient-datum", "def-weil-rationalization-karoubi", "def-weil-weil-sheaf-complex", "lem-trf-absolute-frobenius-site", "lem-trf-frobenius-operator-compact-description", "prop-trf-graph-frobenius-operator", "prop-trf-scheme-galois-comparison", "prop-weil-pbc-rational-transport", "thm-trf-frobenius-fixed-points"]
+++
Fix the global finite-field datum $p,a,q,k_0,k$ and the coefficient
conventions of [def-trf-coefficient-conventions], with $E$, $\mathcal O_E$,
a uniformizer $\varpi=\varpi_E$ and $A_n=A_{E,n}=\mathcal O_E/\varpi^n$.
Let $X_0$ be a separated finite-type $k_0$-scheme, $X=X_0\times_{k_0}k$,
$g_\gamma$ the geometric-Frobenius automorphism and $\Phi$ the $q$-power
scheme Frobenius of [def-trf-scheme-frobenius], and $\kappa^{(m)}$ the
comparison isomorphisms of [prop-trf-scheme-galois-comparison].

Let $K_{\mathcal O}\in D^b_c(X,\mathcal O_E)$ be an integral object
([def-weil-derived-complete-integral-detailed]) whose reductions
$K_n=K_{\mathcal O}\otimes^L_{\mathcal O_E}A_n$ lie in $D^b_{ctf}(X,A_n)$,
and let $K_E$ be the same object of the rationalized category
$D^b_c(X,E)=D^b_c(X,\mathcal O_E)[1/\varpi]$ of
[def-weil-rationalization-karoubi] (so $K_{\mathcal O}$ is a lattice of
$K_E$). Let

$$
\varphi_E:Lg_\gamma^*K_E\longrightarrow K_E
$$

be an arbitrary morphism of $D^b_c(X,E)$ (for instance the Weil
structure of an $E$-Weil complex, [def-weil-weil-sheaf-complex]); no
invertibility, and no invertibility on any lattice, is assumed.

*$E$-stage operators.* All functors below at the stage $E$ are the
rationalizations, by [prop-weil-pbc-rational-transport], of the
integral ones: the pullbacks $Lg_\gamma^{i*}$ with their composition
isomorphisms, $R\Gamma_c(X,-)$ of
[def-weil-integral-rational-qbar-compact-support], the compact-support
base-change isomorphisms $g_{\gamma,c}^{m,*}$ along the automorphisms
$g_\gamma^m$, and the stalk functors with the stalk transports
$\tau_{y,m}$ of [def-trf-frobenius-operators]. Put
$\varphi_E^{[m]}=\varphi_E\circ Lg_\gamma^*\varphi_E\circ\cdots\circ
L(g_\gamma^{m-1})^*\varphi_E:Lg_\gamma^{m*}K_E\to K_E$, as in
[def-trf-iterated-weil-map], and define, by the formulas of
[def-trf-frobenius-operators] in the form of
[lem-trf-frobenius-operator-compact-description],

$$
F_{c,K_E}^{\,m}=R\Gamma_c(X,\varphi_E^{[m]})\circ g_{\gamma,c}^{m,*},
\qquad
F_{y,m}=\varphi^{[m]}_{E,\bar y}\circ\tau_{y,m}
$$

on $R\Gamma_c(X,K_E)$ and on $K_{E,\bar y}$, for $m\geq1$ and
$y\in X_0(\mathbf F_{q^m})$ with geometric point $\bar y$. For $m=1$ and
invertible $\varphi_E$ the first is the compactly supported operator of
[def-weil-global-geometric-frobenius].

*Stalk normalization.* For $y\in X_0(\mathbf F_{q^m})$ one has
$\Phi^m\circ\bar y=\bar y$ ([thm-trf-frobenius-fixed-points]), whence a
natural identification $\iota_M:M_{\bar y}\cong(L\Phi^{m*}M)_{\bar y}$
for every $M$; as throughout, the stalk transport of
[def-trf-frobenius-operators] is taken in the form
$\tau_{y,m}=(\kappa^{(m)}_M)_{\bar y}\circ\iota_M$, natural in $M$ and
defined with no Weil structure on $M$, at every finite level $A_n$ (this
is the normalization under which the stalk map of the scheme-Frobenius
map $u_m$ of [def-trf-iterated-weil-map] is $F_{y,m}$). On integral
objects $\tau_{y,m}$ is the derived limit of these levelwise isomorphisms
on the reduction tower, and at the stage $E$ its rationalization. For a
Frobenius coefficient morphism $\psi$ on $K_n$ with iterates $\psi_m$,
the stalk endomorphism of $K_{n,\bar y}$ is
$\psi_{m,\bar y}=(\psi_m)_{\bar y}\circ\iota_{K_n}$, as in the
coefficient-morphism trace formula of the trace-formula chapter.

Then:

1. *Clearing denominators.* There are an integer $N\geq0$ and a morphism
$u:Lg_\gamma^*K_{\mathcal O}\to K_{\mathcal O}$ of
$D^b_c(X,\mathcal O_E)$ with $\varphi_E=\varpi^{-N}u$ in
$D^b_c(X,E)$; that is, $\varpi^N\varphi_E$ maps the lattice into itself.
1. *Integral Frobenius coefficient morphisms.* For such $(N,u)$ let
$u_n:Lg_\gamma^*K_n\to K_n$ be the reduction of $u$ modulo $\varpi^n$
and put
$$
\psi_n=u_n\circ\kappa_{K_n}:L\Phi^*K_n\longrightarrow K_n .
$$
Each $\psi_n$ is a Frobenius coefficient morphism on $K_n$ in the sense
of [def-trf-frobenius-coefficient-morphism] (in general not
invertible), the $\psi_n$ are compatible with the transitions
$K_{n+1}\otimes^L_{A_{n+1}}A_n\cong K_n$, and the iterates are
$$
\psi_{n,m}=u_n^{[m]}\circ\kappa^{(m)}_{K_n},\qquad
u_n^{[m]}=u_n\circ Lg_\gamma^*u_n\circ\cdots\circ L(g_\gamma^{m-1})^*u_n .
$$
1. *Global operator.* For every $n,m\geq1$,
$$
F_{c,m}(\psi_n)=T_{c_m}(\psi_{n,m})
=R\Gamma_c(X,u_n^{[m]})\circ g_{\gamma,c}^{m,*}
\quad\text{on }R\Gamma_c(X,K_n).
$$
Let $U_m=R\Gamma_c(X,u^{[m]})\circ g_{\gamma,c}^{m,*}$ be the integral
endomorphism of $R\Gamma_c(X,K_{\mathcal O})=R\varprojlim_nR\Gamma_c(X,K_n)$;
it is the derived limit of the levelwise operators $F_{c,m}(\psi_n)$
(the realization of the graph operators $T_{c_m}(\psi_{n,m})$), and
$$
\boxed{\,F_{c,K_E}^{\,m}=\varpi^{-Nm}\,\bigl(U_m\otimes_{\mathcal O_E}E\bigr)
\quad\text{on }R\Gamma_c(X,K_E)=R\Gamma_c(X,K_{\mathcal O})\otimes_{\mathcal O_E}E.\,}
$$
1. *Local operators.* For $y\in X_0(\mathbf F_{q^m})$ the stalk
endomorphism of $\psi_{n,m}$ is $\psi_{n,m,\bar y}=u^{[m]}_{n,\bar y}\circ\tau_{y,m}$
on $K_{n,\bar y}$; the integral endomorphism
$U_{y,m}=u^{[m]}_{\bar y}\circ\tau_{y,m}$ of $K_{\mathcal O,\bar y}$
reduces modulo $\varpi^n$ to $\psi_{n,m,\bar y}$, and
$$
\boxed{\,F_{y,m}=\varpi^{-Nm}\,\bigl(U_{y,m}\otimes_{\mathcal O_E}E\bigr)
\quad\text{on }K_{E,\bar y}=K_{\mathcal O,\bar y}\otimes_{\mathcal O_E}E.\,}
$$

Replacing $(N,u)$ by $(N+1,\varpi u)$ multiplies $U_m,U_{y,m}$ by
$\varpi^m$ and leaves the right-hand sides unchanged. *Example:* for
$X_0=\Spec\mathbf F_q$, $K_E=E^2$ and $\varphi_E=\operatorname{diag}(1,\ell)$,
one may take $N=0$ and $u=\operatorname{diag}(1,\ell)$ on
$\mathcal O_E^2$; no rescaling $c\,\varphi_E$ ($c\in E^\times$) is invertible
on any lattice, since its eigenvalues $c,c\ell$ are not both units, but
$\psi_n=u\bmod\varpi^n$ is a (non-invertible) Frobenius coefficient
morphism.

## Proof

*(1).* By [def-weil-rationalization-karoubi] the morphisms of
$D^b_c(X,E)$ are
$\operatorname{Hom}_{D^b_c(X,\mathcal O_E)}(Lg_\gamma^*K_{\mathcal O},K_{\mathcal O})\otimes_{\mathcal O_E}E$,
the rationalized pullback being that of the integral one
([prop-weil-pbc-rational-transport]). Since $E=\mathcal O_E[1/\varpi]$,
every element of $H\otimes_{\mathcal O_E}E=H[1/\varpi]$, for an
$\mathcal O_E$-module $H$, has the form $u\otimes\varpi^{-N}$ with
$u\in H$ and $N\geq0$. This is $\varphi_E=\varpi^{-N}u$.

*(2).* The reduction $u_n$ is the $n$-th evaluation of the morphism of
towers attached to $u$ by the functorial reduction tower of
[def-weil-pbc-adic-coefficient-datum], using
$(Lg_\gamma^*K_{\mathcal O})\otimes^L A_n\cong Lg_\gamma^*K_n$: since
$g_\gamma$ is an automorphism, $Lg_\gamma^*$ is an exact monoidal
equivalence fixing the constant coefficient sheaves
([def-weil-derived-pullback-tensor-hom]), so it commutes with the
reductions and with the transitions. Hence the $u_n$ are compatible with
the transitions. The isomorphism $\kappa$ of
[prop-trf-scheme-galois-comparison] is composed of the functoriality of
pullback for $\Phi=g_\gamma F_X^{(q)}$ and the trivialization of
absolute-Frobenius pullback of [lem-trf-absolute-frobenius-site], which is
induced on the pro-etale site itself; both are natural in the object and
compatible with the monoidal reduction $-\otimes^L_{A_{n+1}}A_n$.
Therefore $\psi_n=u_n\circ\kappa_{K_n}$ is a morphism
$L\Phi^*K_n\to K_n$, i.e. a Frobenius coefficient morphism, and the
$\psi_n$ are compatible with the transitions.

For the iterates argue by induction on $m$, the case $m=1$ being the
definition. Suppressing the composition isomorphisms of pullback (they
are part of both recursive definitions), the recursion of
[def-trf-frobenius-coefficient-morphism] and the induction hypothesis
give

$$
\psi_{n,m}=\psi_n\circ L\Phi^*\psi_{n,m-1}
=u_n\circ\kappa_{K_n}\circ L\Phi^*\bigl(u_n^{[m-1]}\bigr)\circ
L\Phi^*\bigl(\kappa^{(m-1)}_{K_n}\bigr).
$$

Naturality of $\kappa$ applied to
$u_n^{[m-1]}:Lg_\gamma^{(m-1)*}K_n\to K_n$ gives
$\kappa_{K_n}\circ L\Phi^*(u_n^{[m-1]})
=Lg_\gamma^*(u_n^{[m-1]})\circ\kappa_{Lg_\gamma^{(m-1)*}K_n}$, and the
multiplicativity of the iterates in [prop-trf-scheme-galois-comparison],
for $m=1+(m-1)$, gives
$\kappa_{Lg_\gamma^{(m-1)*}K_n}\circ L\Phi^*(\kappa^{(m-1)}_{K_n})
=\kappa^{(m)}_{K_n}$. Hence
$\psi_{n,m}=u_n\circ Lg_\gamma^*(u_n^{[m-1]})\circ\kappa^{(m)}_{K_n}
=u_n^{[m]}\circ\kappa^{(m)}_{K_n}$.

*(3).* The first equality is the definition of $F_{c,m}(\psi_n)$ in
[def-trf-frobenius-coefficient-morphism]. By (2),
$\psi_{n,m}=v\circ\kappa^{(m)}_{K_n}$ with $v=u_n^{[m]}$, and the general
clause of [prop-trf-graph-frobenius-operator], which allows an arbitrary,
not necessarily invertible $v$ and no Weil structure on $K_n$, gives
$T_{c_m}(\psi_{n,m})=R\Gamma_c(X,u_n^{[m]})\circ g_{\gamma,c}^{m,*}$.

By [def-weil-integral-rational-qbar-compact-support],
$R\Gamma_c(X,-)$ on $D^b_c(X,\mathcal O_E)$ is the derived limit of the
levelwise compact-support cohomology of the reduction tower of
[def-weil-pbc-adic-coefficient-datum]; on morphisms it is the derived
limit of the levelwise maps. The integral morphism $u^{[m]}$ (formed from
$u$ by the integral pullbacks) has reductions $u_n^{[m]}$, because
$Lg_\gamma^{i*}$ commutes with the reductions as in (2); and the integral
base-change isomorphism $g_{\gamma,c}^{m,*}$ is the derived limit of the
levelwise ones, the pullback $Lg_\gamma^{m*}$ carrying the reduction tower
of $K_{\mathcal O}$ to that of $Lg_\gamma^{m*}K_{\mathcal O}$. Hence
$U_m$ is the derived limit of the levelwise composites
$R\Gamma_c(X,u_n^{[m]})\circ g_{\gamma,c}^{m,*}=F_{c,m}(\psi_n)$.

At the stage $E$, $R\Gamma_c(X,K_E)=R\Gamma_c(X,K_{\mathcal O})\otimes_{\mathcal O_E}E$
([def-weil-integral-rational-qbar-compact-support]), and every
rationalized functor or natural transformation acts on
$\operatorname{Hom}\otimes_{\mathcal O_E}E$ by $f\otimes\lambda\mapsto
F(f)\otimes\lambda$ ([prop-weil-pbc-rational-transport]); composition in
$D^b_c(X,E)$ is $E$-bilinear. Hence
$L(g_\gamma^{i})^*\varphi_E=\varpi^{-N}\,L(g_\gamma^{i})^*u$ for each $i$,
the composition isomorphisms are those of the integral pullbacks, and

$$
\varphi_E^{[m]}=\prod_{i=0}^{m-1}\varpi^{-N}\cdot
\bigl(u\circ Lg_\gamma^*u\circ\cdots\circ L(g_\gamma^{m-1})^*u\bigr)
=\varpi^{-Nm}u^{[m]}.
$$

Applying the $E$-linear map induced by the rationalized $R\Gamma_c(X,-)$
and composing with the rationalization of the integral
$g_{\gamma,c}^{m,*}$ gives
$F_{c,K_E}^{\,m}=\varpi^{-Nm}\bigl(R\Gamma_c(X,u^{[m]})\circ g_{\gamma,c}^{m,*}\bigr)\otimes E
=\varpi^{-Nm}(U_m\otimes E)$.

*(4).* By the stalk normalization and (2),
$\psi_{n,m,\bar y}=(u_n^{[m]})_{\bar y}\circ(\kappa^{(m)}_{K_n})_{\bar y}\circ\iota_{K_n}
=u^{[m]}_{n,\bar y}\circ\tau_{y,m}$. The stalk functor $L\bar y^*$ is a
pullback, hence monoidal and compatible with the reductions
([def-weil-derived-pullback-tensor-hom]), and $\tau_{y,m}$ is natural and
compatible with the reductions by the same argument as for $\kappa$ in
(2), its integral form being the derived limit of the levelwise ones; so
$U_{y,m}=u^{[m]}_{\bar y}\circ\tau_{y,m}$ reduces modulo
$\varpi^n$ to $u^{[m]}_{n,\bar y}\circ\tau_{y,m}=\psi_{n,m,\bar y}$. At
the stage $E$, the stalk of $K_E$ is $K_{\mathcal O,\bar y}\otimes E$ and,
exactly as in (3), $\varphi^{[m]}_{E,\bar y}=\varpi^{-Nm}(u^{[m]}_{\bar y}\otimes E)$,
whence $F_{y,m}=\varphi^{[m]}_{E,\bar y}\circ\tau_{y,m}
=\varpi^{-Nm}(U_{y,m}\otimes E)$.

The remark on $(N+1,\varpi u)$ is $(\varpi u)^{[m]}=\varpi^mu^{[m]}$, by
$\mathcal O_E$-linearity of the pullbacks. In the example, identify the
coefficient categories of $X=\Spec k$ with complexes of modules, so that
$u=\operatorname{diag}(1,\ell)$ is an endomorphism of the lattice
$\mathcal O_E^2$. If $c\,\varphi_E$ were an automorphism of some lattice
$L\subset E^2$, then its characteristic polynomial and that of its inverse
would have coefficients in $\mathcal O_E$, so its eigenvalues $c$ and
$c\ell$ would both be units of the integral closure of $\mathcal O_E$;
then so would be their quotient $\ell$, which is absurd.
