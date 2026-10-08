+++
id = "prop-trf-exceptional-kunneth"
kind = "theorem"
title = "Exceptional Kunneth; the $\\alpha$ map"
order = 2226
tags = ["latex:proposition"]
uses = ["def-sf-kv-maps", "def-trf-admissibility", "lem-sf-mate", "lem-sf-triangle-two-out-of-three", "lem-trf-devissage-generation", "lem-trf-ordinary-kunneth", "prop-sf-open-closed-triangle-all-stages", "thm-pur-affine-line-purity", "thm-sf-ctf-stability"]
+++
For $i=1,2$, let $f_i:X_i\to Y_i$ be morphisms of separated
finite-type schemes satisfying the
exceptional-adjoint admissibility of
[def-trf-admissibility], and let $L_i\in D^b_{ctf}(Y_i,A)$. The
canonical comparison of [def-sf-kv-maps] (ii), formed with the geometric operations,

$$
\alpha:f_1^!L_1\boxtimes_A^{\mathrm L} f_2^!L_2
\longrightarrow
(f_1\times f_2)^!\bigl(L_1\boxtimes_A^{\mathrm L} L_2\bigr)
$$

is an isomorphism, natural in the $L_i$.

## Proof

First, shriek Kunneth: by $!$-base change and the projection formula
for the exceptional adjoint pair of [def-trf-admissibility], the
comparison

$$
(f_1\times f_2)_!\bigl(f_1^!L_1\boxtimes_A^{\mathrm L} f_2^!L_2\bigr)
\xrightarrow{\ \sim\ }
(f_1)_!f_1^!L_1\boxtimes_A^{\mathrm L}(f_2)_!f_2^!L_2
$$

is invertible. Evaluating it on the $f_i^!L_i$ and composing with the
two exceptional counits of [def-trf-admissibility] produces a map
to $L_1\boxtimes_A^{\mathrm L}L_2$; the exceptional adjoint of this
composite defines $\alpha$.

It remains to see that $\alpha$ is invertible. For a constant auxiliary
coefficient, smooth maps are handled by smooth purity with compatibility
of the smooth trace under base change [thm-pur-affine-line-purity],
and closed immersions by localization together with the
open-product base change, which is the case $Q=\underline A_Z$ of
[lem-trf-ordinary-kunneth]. An affine factorization of a general
$f_i$ into a closed immersion followed by a smooth projection
therefore gives the local case. This settles constant coefficients
$L_i=\underline A_{Y_i}$, and by additivity finite free ones.

Lisse coefficients. If $L_i$ is lisse with flat stalks, invertibility of
$\alpha$ is étale-local on $Y_1\times Y_2$: for an étale $u$ one has
$u^!=u^*$, so by the composition isomorphism of exceptional inverse images
([lem-sf-mate]) $f^!$ commutes with étale pullback, compatibly with
$\alpha$. On a finite étale cover trivializing the $L_i$ they become finite
free, the case above. This is a local reduction, not a dévissage: lisse
coefficients cannot be replaced by constant ones globally
([lem-trf-devissage-generation]).

General coefficients. Argue by induction on
$\delta=\dim\operatorname{supp}L_1+\dim\operatorname{supp}L_2$; the claim is
trivial if some $L_i=0$. Both sides of $\alpha$ are exact in each $L_i$, so
the two-out-of-three property [lem-sf-triangle-two-out-of-three] applies to
distinguished triangles in either variable.

Closed pushforward. Let $g_1:Z_1\hookrightarrow Y_1$ be a closed immersion,
with $g_1':X_1\times_{Y_1}Z_1\hookrightarrow X_1$ and
$f_1':X_1\times_{Y_1}Z_1\to Z_1$ the projections. The dual base change
$f_1^!Rg_{1*}\cong Rg'_{1*}f_1'^!$ (the mate of the $!$-base change,
[lem-sf-mate]) and the identity-factor Künneth
$Rg_{1*}M_1\boxtimes L_2\cong R(g_1\times\mathrm{id})_*(M_1\boxtimes L_2)$
of [lem-trf-ordinary-kunneth] identify $\alpha_f(Rg_{1*}M_1,L_2)$ with
$R(g_1'\times\mathrm{id})_*\,\alpha_{f_1'\times f_2}(M_1,L_2)$, compatibly
with the definition of $\alpha$ as an exceptional adjoint (a mate-calculus
check); likewise in the second variable. Since $L_i\cong Rg_{i*}g_i^*L_i$
for $Z_i=\operatorname{supp}L_i$ (the open–closed triangle
[prop-sf-open-closed-triangle-all-stages], as $L_i$ vanishes on the
complement), we may assume $\dim Y_i=\dim\operatorname{supp}L_i$. Then by
the generation [lem-trf-devissage-generation] on $Y_i$ it suffices to treat
the generators $L_i=Rg_{i*}j_{i!}F_i$ with $F_i$ lisse with flat stalks on a
stratum $U_i$ dense in $\overline U_i$, $\dim\overline U_i\le\dim Y_i$, and
by the closed pushforward just described we may take $\overline U_i=Y_i$,
$L_i=j_{i!}F_i$.

Open localization. The functor $f^!$ does not commute with $j_!$, so pass
through $Rj_*$. For the open immersion $j=j_1\times j_2$ with base changes
$j'$ and $f'$, the dual base change $f^!Rj_*\cong Rj'_*f'^!$ (the mate of
the base change for $j_!$) and [lem-trf-ordinary-kunneth], which gives
$Rj_{1*}F_1\boxtimes Rj_{2*}F_2\cong Rj_*(F_1\boxtimes F_2)$ and
$Rj'_{1*}f_1'^!F_1\boxtimes Rj'_{2*}f_2'^!F_2\cong
Rj'_*(f_1'^!F_1\boxtimes f_2'^!F_2)$, identify
$\alpha_f(Rj_{1*}F_1,Rj_{2*}F_2)$ with $Rj'_*\,\alpha_{f'}(F_1,F_2)$,
compatibly with $\alpha$ as before; the latter is the lisse case already
treated, so $\alpha$ is invertible on $(Rj_{1*}F_1,Rj_{2*}F_2)$. The
open–closed triangle [prop-sf-open-closed-triangle-all-stages] for
$M=Rj_{i*}F_i$ reads $j_{i!}F_i\to Rj_{i*}F_i\to T_i\xrightarrow{+1}$ with
$T_i=i_{i*}i_i^*Rj_{i*}F_i\in D^b_{ctf}(Y_i,A)$ ([thm-sf-ctf-stability]), a
general object of $D^b_{ctf}$ supported on the boundary
$Z_i=Y_i\setminus U_i$, of dimension $<\dim Y_i$. By the induction
hypothesis $\alpha$ is invertible on $(T_1,j_{2!}F_2)$ and on
$(Rj_{1*}F_1,T_2)$, the support dimensions having dropped; two-out-of-three
in the second variable gives $(Rj_{1*}F_1,j_{2!}F_2)$, and then in the first
variable $(j_{1!}F_1,j_{2!}F_2)$. Thus $\alpha$ is an isomorphism.
