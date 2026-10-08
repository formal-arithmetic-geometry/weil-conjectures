+++
id = "sk-thm-sf-kunneth-verdier"
kind = "section"
title = "Künneth–Verdier isomorphism"
order = 2224
uses = ["sk-def-sf-kv-maps", "sk-def-sf-operations", "sk-lem-sf-ctf-generation", "sk-lem-sf-kunneth-star", "sk-lem-sf-mate", "sk-prop-sf-biduality-general", "sk-prop-sf-closed-unit", "sk-prop-sf-dualizable-biduality", "sk-prop-sf-localization", "sk-prop-sf-open-closed-triangle", "sk-thm-regular", "sk-thm-sf-ctf-stability", "sk-thm-sf-tensor-hom", "sk-thm-smooth-purity"]
lean = ["AlgebraicGeometry.Etale.hasKunnethComparisons"]
+++
*Theorem (sketch).*

The three maps of [sk-def-sf-kv-maps] are isomorphisms, natural in their
variables, under the hypotheses of that definition (the $Rf_i^!$ are the
constructible exceptional adjoints of [sk-def-sf-operations] (vi); no
admissibility datum of [sk-def-sf-admissible] is assumed): the
exceptional Künneth $\alpha$, the external Hom $\beta$, and
in particular, for $X,Y$ separated of finite type over $k$, with the structure
morphism $a_Y$ and the product projection $p_X=\operatorname{id}_X\times a_Y$
as in [sk-def-sf-kv-maps] (iv), and
$M\in\Dctf(X,\Lambda)$, $N\in\Dctf(Y,\Lambda)$,

$$
\kappa_{M,N}:M\boxtimes\mathbb D_YN\ \xrightarrow{\ \sim\ }\
\RHom\bigl(p_Y^*N,Rp_X^!M\bigr).
$$

## Proof

*The map $\alpha$.* Take first a constant auxiliary coefficient. For
smooth $f_i$ of relative dimension $d_i$, [sk-thm-smooth-purity] identifies
$Rf_i^!$ with $Lf_i^*(d_i)[2d_i]$, and its compatibility with base change and
with composition identifies the smooth product comparison with the ordinary
pullback–tensor comparison and the sum of the twists; the smooth trace is the
exceptional counit under this orientation, and its base-change square is the
adjoint of the same purity comparison, using the adjunction coherence of
fix-prop-adjunctions and the mate calculus [sk-lem-sf-mate]. Closed immersions are handled by supported
localization [sk-prop-sf-localization] together with the closed-immersion unit
[sk-prop-sf-closed-unit] and the case $Q=\Lambda_Z$ of
[sk-lem-sf-kunneth-star]; the regular case carries the fundamental class of
[sk-thm-regular]. An affine factorization of a general $f_i$ into a closed
immersion followed by a smooth projection gives the map locally. This
settles constant coefficients $L_i=\Lambda_{Y_i}$, hence, by additivity,
finite free ones. For $L_i$ lisse with flat stalks the invertibility of
$\alpha$ is étale-local on $Y_1\times Y_2$ — $Rf^!$ commutes with étale
pullback (for étale $u$, $Ru^!=Lu^*$, and the composition isomorphism of
[sk-lem-sf-mate]), compatibly with $\alpha$ — and on a finite étale cover
trivializing the $L_i$ they become finite free, the case just treated; this
is a local reduction, not a dévissage (the lisse coefficients cannot be
replaced by constant ones globally, [sk-lem-sf-ctf-generation]). For
general $L_i\in\Dctf(Y_i,\Lambda)$ argue by induction on
$\delta=\dim\operatorname{supp}L_1+\dim\operatorname{supp}L_2$; the claim is
trivial if some $L_i=0$, and both sides of $\alpha$ are exact in each $L_i$,
so two-out-of-three applies to triangles in either variable.
*Closed pushforward.* For a closed immersion $g_1:Z_1\hookrightarrow
Y_1$, with $g_1':X_1\times_{Y_1}Z_1\hookrightarrow X_1$ and
$f_1':X_1\times_{Y_1}Z_1\to Z_1$ the projections, the dual base change
$Rf_1^!Rg_{1*}\cong Rg'_{1*}Rf_1'^!$ (the mate of $\operatorname{Ex}_!$ under
[sk-lem-sf-mate]) and $Rg_{1*}M_1\boxtimes L_2\cong
R(g_1\times\mathrm{id})_*(M_1\boxtimes L_2)$ ([sk-lem-sf-kunneth-star])
identify $\alpha_f(Rg_{1*}M_1,L_2)$ with
$R(g_1'\times\mathrm{id})_*\,\alpha_{f_1'\times f_2}(M_1,L_2)$, compatibly
with the definition of $\alpha$ as an exceptional adjoint (a mate-calculus
check, [sk-lem-sf-mate]); likewise in the second variable. Since
$L_i\cong Rg_{i*}g_i^*L_i$ for $Z_i=\operatorname{supp}L_i$
([sk-prop-sf-open-closed-triangle], as $L_i$ vanishes on the complement),
we may assume $\dim Y_i=\dim\operatorname{supp}L_i$. Then by the generation
[sk-lem-sf-ctf-generation] on $Y_i$ it suffices to treat the generators
$L_i=Rg_{i*}j_{i!}F_i$ with $F_i$ lisse with flat stalks on a stratum $U_i$
dense in $\overline U_i$, $\dim\overline U_i\le\dim Y_i$, and by the closed
pushforward just described we may take $\overline U_i=Y_i$, $L_i=j_{i!}F_i$.
*Open localization.* $Rf^!$ does not commute with $j_!$, so pass
through $Rj_*$: for the open immersion $j=j_1\times j_2$ with base changes
$j'$ and $f'$, the dual base change $Rf^!Rj_*\cong Rj'_*Rf'^!$ (the mate of
the base change for $j_!$) and [sk-lem-sf-kunneth-star], which gives
$Rj_{1*}F_1\boxtimes Rj_{2*}F_2\cong Rj_*(F_1\boxtimes F_2)$ and
$Rj'_{1*}Rf_1'^!F_1\boxtimes Rj'_{2*}Rf_2'^!F_2\cong
Rj'_*(Rf_1'^!F_1\boxtimes Rf_2'^!F_2)$, identify
$\alpha_f(Rj_{1*}F_1,Rj_{2*}F_2)$ with $Rj'_*\,\alpha_{f'}(F_1,F_2)$,
compatibly with $\alpha$ as before; the latter is the lisse case already
treated, so $\alpha$ is invertible on $(Rj_{1*}F_1,Rj_{2*}F_2)$. The
open–closed triangle [sk-prop-sf-open-closed-triangle] for
$M=Rj_{i*}F_i$ reads
$j_{i!}F_i\to Rj_{i*}F_i\to T_i\xrightarrow{+1}$ with
$T_i=i_{i*}i_i^*Rj_{i*}F_i\in\Dctf(Y_i,\Lambda)$
([sk-thm-sf-ctf-stability]), a general object of $\Dctf$ supported on the
boundary $Z_i=Y_i\setminus U_i$, of dimension $<\dim Y_i$. By the induction
hypothesis $\alpha$ is invertible on $(T_1,j_{2!}F_2)$ and on
$(Rj_{1*}F_1,T_2)$, the support dimensions having dropped; two-out-of-three
in the second variable gives $(Rj_{1*}F_1,j_{2!}F_2)$, and then in the first
variable $(j_{1!}F_1,j_{2!}F_2)$. Hence $\alpha$ is invertible.

*The map $\beta$.* Both sides are exact in each $E_i$, so dévissage in
both $E_i$, by [sk-lem-sf-ctf-generation], reduces to $E_i=Rh_{i!}F_i$ with
$h_i=g_ij_i$, $g_i$ finite and $j_i$ open, and $F_i$ lisse on $U_i$ with flat
stalks. Such an $F_i$ is dualizable: its stalks are finite flat, hence free,
over the local ring $\Lambda$, so $F_i$ is locally finite free and
[sk-prop-sf-dualizable-biduality] gives $\RHom(F_i,-)\simeq
F_i^\vee\otimes^L-$. Tensor–Hom and the exceptional adjunction then give
$\RHom(E_i,L_i)\simeq Rh_{i*}\RHom(F_i,Rh_i^!L_i)\simeq
Rh_{i*}\bigl(F_i^\vee\otimes^LRh_i^!L_i\bigr)$ ([sk-thm-sf-tensor-hom]).
With $h=h_1\times h_2$ and $F=F_1\boxtimes F_2$, so that
$F^\vee\simeq F_1^\vee\boxtimes F_2^\vee$ and $E_1\boxtimes E_2\simeq Rh_!F$
($\mathrm{Ku}_!$), the comparison becomes

$$
 Rh_{1*}\bigl(F_1^\vee\otimes^LRh_1^!L_1\bigr)\boxtimes
 Rh_{2*}\bigl(F_2^\vee\otimes^LRh_2^!L_2\bigr)
 \xrightarrow[\text{twice}]{\ \mathrm{Ku}_*\ }
 Rh_*\bigl(F^\vee\otimes^L(Rh_1^!L_1\boxtimes Rh_2^!L_2)\bigr)
 \xrightarrow{\ Rh_*(1\otimes\alpha)\ }
 Rh_*\bigl(F^\vee\otimes^LRh^!(L_1\boxtimes L_2)\bigr),
$$

the first arrow being [sk-lem-sf-kunneth-star] in each factor (after the
symmetry of $\otimes^L$) and the second the $\alpha$ just proved; by the same
identifications the target is $\RHom(E_1\boxtimes E_2,L_1\boxtimes L_2)$.
Taking ordinary and then exceptional adjoints identifies this composite with
the specified $\beta$: both paths become the tensor product of the two
evaluation maps after the projection formula. Hence $\beta$ is invertible.

*The map $\kappa$.* Apply $\beta$ to the pairs $(\Lambda_X,M)$ and
$(N,\omega_Y)$, then $\RHom(1,\alpha)$ for the identification
$M\boxtimes\omega_Y\simeq Rp_X^!M$, which is $\alpha$ for
$\operatorname{id}_X\times a_Y$. Their composite is $\kappa_{M,N}$ by
[sk-def-sf-kv-maps] (iv), and both factors have just been shown invertible.

Uses: `\Cref{def-sf-kv-maps}`, `\Cref{sk-lem-sf-ctf-generation}`, `\Cref{sk-lem-sf-kunneth-star}`, `\Cref{sk-prop-sf-biduality-general}`, `\Cref{sk-prop-sf-dualizable-biduality}`, `\Cref{sk-thm-sf-tensor-hom}`, `\Cref{lem-sf-mate}`, `\Cref{sk-prop-sf-closed-unit}`, `\Cref{sk-prop-sf-localization}`, `\Cref{sk-thm-regular}`, `\Cref{sk-thm-smooth-purity}`
