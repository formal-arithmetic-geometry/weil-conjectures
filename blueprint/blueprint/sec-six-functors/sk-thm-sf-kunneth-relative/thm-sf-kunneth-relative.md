+++
id = "thm-sf-kunneth-relative"
kind = "theorem"
title = "Relative product theorem"
order = 2188
uses = ["def-pur-support-cohomology", "def-sf-datum", "def-sf-pf"]
+++
In the setting of [def-sf-datum], let $B$ be a separated finite-type
$k$-scheme, $f:X\to B$, $g:Y\to B$ separated finite type, $p,q$ the
projections of $X\times_BY$ (so $f\times_Bg=g\circ q$), and put $K\boxtimes L=p^*K\otimes^L_\Lambda q^*L$ for $K\in D^b_{ctf}(X,\Lambda)$, $L\in D^b_{ctf}(Y,\Lambda)$.
Define the canonical map as the composite of the inverse of the
composition isomorphism $Rg_!Rq_!\cong R(f\times_Bg)_!$ of (A4), the inverse
of the projection transformation of [def-sf-pf] for $q$ at $(p^*K,L)$, the
inverse of the base-change exchange
$\operatorname{Ex}_!:Lg^*Rf_!K\to Rq_!Lp^*K$ of (A2), the symmetry of
$\otimes^L_\Lambda$, and the inverse of the projection transformation for $g$
at $(L,Rf_!K)$ followed by the symmetry, i.e. of the four steps of the proof
below (its coherence — symmetry, triple products, base change, projection
formula — is the separate coherence lemma for the relative product). Then this
canonical map

$$
R(f\times_Bg)_!\bigl(K\boxtimes L\bigr)\xrightarrow{\ \sim\ }
Rf_!K\otimes^L_\Lambda Rg_!L
$$

is an isomorphism, natural in $K$ and $L$, compatible with base change
$B'\to B$, finite reduction, scalar extension, and with the
identifications $Rf_!\cong Rf_*$ for proper $f$. For $B=\operatorname{Spec}k$
and closed immersions $i_Z:Z\hookrightarrow X$, $i_W:W\hookrightarrow Y$,
it gives the compact-support product on the closed subschemes:

$$
R\Gamma_c(Z,i_Z^*K)\otimes^L_\Lambda R\Gamma_c(W,i_W^*L)
\cong R\Gamma_c(Z\times_kW,(i_Z\times i_W)^*(K\boxtimes L)).
$$

This is cohomology of the restrictions to the closed subschemes.
Cohomology with supports $R\Gamma_Z(X,K)=R\Gamma(Z,Ri_Z^!K)$ is a different
object from $R\Gamma_c(Z,i_Z^*K)$; its product formula over $\operatorname{Spec}k$ is
[lem-pur-kunneth-supported], proved directly for smooth purity, and is
deduced again from the display above by Verdier duality later in the
Poincaré duality chapter. Over a general base $B$ the supports version
fails, so only the compact-support form is stated relatively.

## Proof

The operations are those of [def-sf-datum] and [def-sf-pf],
cohomology with supports has its separate meaning in
[def-pur-support-cohomology].
Step 1: by (A4), $R(f\times_Bg)_!=Rg_!\circ Rq_!$, so
$R(f\times_Bg)_!(K\boxtimes L)=Rg_!\bigl(Rq_!(q^*L\otimes^L_\Lambda p^*K)\bigr)$. Step 2: the projection formula (A3) for $q$, whose target is
$Y$, gives $Rq_!(q^*L\otimes^L p^*K)\cong L\otimes^L_\Lambda Rq_!(p^*K)$.
Step 3: base change (A2) for the Cartesian square with $p,q,f,g$ gives
$Rq_!(p^*K)\cong Lg^*Rf_!K$. Step 4: applying the projection formula to
$g$ with first variable $L$ and second variable $Rf_!K$ gives
$Rg_!\bigl(L\otimes^L_\Lambda Lg^*Rf_!K\bigr)\cong Rg_!L\otimes^L_\Lambda Rf_!K$, which is the displayed isomorphism. Step 5:
apply the same formula to the separated finite-type morphisms
$Z\to\operatorname{Spec}k$, $W\to\operatorname{Spec}k$ and the
pullbacks $i_Z^*K,i_W^*L$. Pullback preserves their finite-Tor
hypotheses, and the exterior product is the pullback of $K\boxtimes L$.
This proves the claimed compact-support formula on the closed subschemes.
