+++
id = "cor-sf-duality-pullback"
kind = "theorem"
title = "Duality against pullback"
order = 2230
tags = ["latex:corollary"]
uses = ["def-sf-datum", "def-sf-orientation", "fix-prop-adjunctions", "lem-sf-mate", "thm-fix-general-biduality", "thm-sf-verdier-exchange"]
+++
In the setting of [def-sf-datum], let $f:X\to Y$ be separated of finite
type. Then

$$
D_XLf^*\xrightarrow{\ \sim\ }Rf^!D_Y
$$

as functors $D^b_{ctf}(Y,\Lambda)\to D^b_{ctf}(X,\Lambda)$, naturally in $f$.
If an orientation datum is fixed and $f$ is smooth of pure relative
dimension $d$, this reads $D_XLf^*\cong Lf^*D_Y(d)[2d]$.

## Proof

The Verdier exchange $D_YRf_!\cong Rf_*D_X$ is [thm-sf-verdier-exchange],
proved in this chapter from the tensor–Hom exchange and the projection
formula; biduality, axiom (A6), is [def-sf-datum] of this chapter,
where its geometric input is [thm-fix-general-biduality]; and the adjunctions $Lf^*\dashv Rf_*$ and
$Rf_!\dashv Rf^!$ are those of [fix-prop-adjunctions]. Since $D_Y$ is
an anti-equivalence with inverse $D_Y$ by biduality, its right adjoint is
$D_Y$ itself, so the right adjoint of $D_YRf_!$ is $Rf^!D_Y$ and that of
$Rf_*D_X$ is $D_XLf^*$; passing to right adjoints, which is again the mate
calculus of [lem-sf-mate], gives the displayed isomorphism. The second
assertion substitutes the orientation $Rf^!\cong Lf^*(-)(d)[2d]$, which is
the content of [def-sf-orientation] as constructed in the purity
chapter.
