+++
id = "fix-cor-verdier-exchange"
kind = "theorem"
title = "Verdier-duality exchange"
order = 2117
tags = ["latex:corollary"]
uses = ["def-fix-six-functor-datum", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-adjoint-admissibility", "def-weil-exceptional-inverse-image", "fix-lem-tensor-adjunction", "fix-prop-adjunctions", "thm-sf-comp-composition"]
+++
In the six-functor datum of
[def-fix-six-functor-datum], assume that $f$ and the structure
morphisms $a_X$, $a_Y$ are
exceptionally
admissible, and put

$$
\omega_{Y,\Lambda}=Ra_Y^!\Lambda,\qquad
\omega_{X,\Lambda}=Ra_X^!\Lambda,\qquad
D_Y(-)=R\mathcal Hom_{\Lambda}(-,\omega_{Y,\Lambda}),\qquad
D_X(-)=R\mathcal Hom_{\Lambda}(-,\omega_{X,\Lambda}).
$$

For every $M\in D^b_{ctf}(X,\Lambda)$ there is a canonical
isomorphism

$$
D_Y(Rf_!M)\xrightarrow{\ \sim\ }Rf_*D_X(M),
$$

natural in $M$, compatible with finite reduction, scalar extension,
and shifts.

## Proof

Step 1: the relation $Rf^!\omega_{Y,\Lambda}\cong\omega_{X,\Lambda}$.
The composition law $R(a_Y\circ f)_!\cong R(a_Y)_!Rf_!$ of
[thm-sf-comp-composition] and the adjunctions of
[fix-prop-adjunctions] give, by the mate calculus for a
composite adjunction (the pasted units and counits of
[fix-prop-adjunctions]), the canonical isomorphism

$$
Rf^!\omega_{Y,\Lambda}=Rf^!Ra_Y^!\Lambda
\xrightarrow{\ \sim\ }Ra_X^!\Lambda=\omega_{X,\Lambda}.
$$

Step 2: the exchange. Applying [fix-lem-tensor-adjunction]
with $N=\omega_{Y,\Lambda}$ (an object of $D^b_{ctf}(Y,\Lambda)$
by the finite-Tor preservation of
[def-weil-exceptional-inverse-image]) gives

$$
\begin{aligned}
D_Y(Rf_!M)
&=R\mathcal Hom_Y(Rf_!M,\omega_{Y,\Lambda})\\
&\xrightarrow{\ \sim\ }Rf_*R\mathcal Hom_X(M,f^!\omega_{Y,\Lambda})\\
&\xrightarrow{\ \sim\ }Rf_*R\mathcal Hom_X(M,\omega_{X,\Lambda})
=Rf_*D_X(M),
\end{aligned}
$$

the first isomorphism being the one of
[fix-lem-tensor-adjunction], the second the transport along
step 1. Step 3: the compatibilities. Naturality in $M$ and the
compatibility with finite reduction, scalar extension, and shifts are
those of [fix-lem-tensor-adjunction] and of step 1.
