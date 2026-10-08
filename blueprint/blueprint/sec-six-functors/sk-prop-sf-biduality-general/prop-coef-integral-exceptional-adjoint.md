+++
id = "prop-coef-integral-exceptional-adjoint"
kind = "theorem"
title = "The integral exceptional adjoint on constructible complexes"
order = 2149
tags = ["latex:proposition"]
uses = ["lem-coef-finite-exceptional", "lem-coef-integral-compact-support", "lem-coef-normalized-dvr-effectivity", "lemma-weil-pbc-completed-pullback-reduction", "prop-coef-integral-dualizing", "thm-coef-integral-verdier"]
+++
For a separated finite-type $f:X\to Y$, define

$$
G_fL=R\varprojlim_n\operatorname{Res}_n Rf_n^!L_n.
$$

Then $G_f$ maps $D^b_c(Y,R)$ to $D^b_c(X,R)$, is right
adjoint to integral $Rf_!$ on these categories, and has canonical
identifications

$$
G_fL\cong D_{X,R}f^*_{\mathrm{comp}}D_{Y,R}L,
\qquad (G_fL)\otimes_R^L A_n\cong Rf_n^!L_n.
$$

Here $f^*_{\mathrm{comp}}$ is completed pullback. For input
reduction Tor interval $[a,b]$, one output interval is
$[a-2\dim X,b+2\dim Y]$. The comparison identifies the
canonical units and counits; in particular the dualizing object
of [prop-coef-integral-dualizing] is $G_aR$.
This is an adjunction on the stated constructible categories.

## Proof

By [lem-coef-finite-exceptional] the displayed exceptional
tower is normalized, including its adjunction maps. Alternatively,
consider the integral object
$H=D_{X,R}f^*_{\mathrm{comp}}D_{Y,R}L$.
It exists in the integral category by
[thm-coef-integral-verdier] and
[lemma-weil-pbc-completed-pullback-reduction].
The latter gives finite reductions equal to ordinary pullback;
pullback preserves the reduction Tor interval. Applying the two
duality bounds gives $[a-2\dim X,b+2\dim Y]$.
The finite dual formula in [lem-coef-finite-exceptional]
identifies its reductions with $Rf_n^!L_n$, compatibly with
the transition maps. Reconstruction, or
[lem-coef-normalized-dvr-effectivity], gives $H\cong G_fL$.

For $K\in D^b_c(X,R)$, use the reduction of integral compact
supports in [lem-coef-integral-compact-support] and derived
coefficient adjunction to compute

$$
\begin{aligned}
R\operatorname{Hom}_Y(Rf_!K,L)
&\cong R\varprojlim_n R\operatorname{Hom}_{Y,A_n}(Rf_{!,n}K_n,L_n)\\
&\cong R\varprojlim_n R\operatorname{Hom}_{X,A_n}(K_n,Rf_n^!L_n)\\
&\cong R\operatorname{Hom}_X(K,G_fL).
\end{aligned}
$$

Finite units and counits commute with the transition maps by
[lem-coef-finite-exceptional]. Hence this calculation defines
the adjunction and its specified maps; the triangle identities
follow from the same identities before taking the derived limit.
For the structure morphism and $L=R$, the defining tower is
the one in [prop-coef-integral-dualizing]. This proves the
last identification with its adjunction, without an assertion about
unrestricted unbounded pro-etale inputs.
