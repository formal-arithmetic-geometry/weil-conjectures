+++
id = "thm-trf-fixed-point-base-change"
kind = "theorem"
title = "Base change in the fixed-point square"
order = 2314
uses = ["def-exchange-projection", "def-trf-admissibility", "def-trf-coefficient-conventions", "def-trf-correspondence", "def-trf-fixed-scheme", "def-weil-derived-pullback-tensor-hom", "def-weil-finite-field-fiber", "prop-functor-package", "prop-trf-fixed-square-cartesian"]
+++
Fix the global finite-field datum
and the coefficient
conventions, $A=A_{E,n}$, and let
$c=(c_1,c_2):C\to X\times_sX$ be an
admissible
cohomological correspondence with
fixed scheme
$F=\operatorname{Fix}(c)$, so that the
fixed square of
[prop-trf-fixed-square-cartesian] is Cartesian.

1. *Pullback along the ordinary leg.* For
$K\in D^b_{ctf}(X,A)$,
$$
Li_F^*Lc_2^*K\xrightarrow{\ \sim\ }Ld^*K,
$$
the functoriality of the
derived pullback along
the equality $c_2i_F=d$.
1. *Base change for the total correspondence.* For
$M\in D^b_{ctf}(C,A)$,
$$
L\Delta_X^*Rc_!M\xrightarrow{\ \sim\ }Rd_!Li_F^*M,
$$
the
compact-support base change of the
six-operations package in the Cartesian fixed square. For
$N\in D^b_{ctf}(X,A)$, its right-adjoint form (from the
compatibility of the exchange with the adjunction data of
[def-trf-admissibility]) is
$$
Rc^!R\Delta_{X*}N\xrightarrow{\ \sim\ }Ri_{F*}Rd^!N.
$$

## Proof

The first identification is the functoriality of the derived pullback
along the equality $c_2i_F=d$ of
[prop-trf-fixed-square-cartesian]:

$$
Li_F^*Lc_2^*K=L(c_2i_F)^*K=Ld^*K.
$$

The second is the compact-support exchange
$Lg^*Rf_!\xrightarrow{\sim}Rf'_!Lg'^*$ of
[def-exchange-projection] (and of the six-operations package
[prop-functor-package], item (4)) applied to the Cartesian fixed
square of [prop-trf-fixed-square-cartesian] with $f=c$,
$g=\Delta_X$, $f'=d$, $g'=i_F$. The right-adjoint form is
obtained by taking right adjoints of the two sides and using the
compatibility of the exchange with the units and counits of the
adjunctions of [def-trf-admissibility]: the right adjoint of
$L\Delta_X^*Rc_!$ is $Rc^!R\Delta_{X*}$, and that of $Rd_!Li_F^*$
is $Ri_{F*}Rd^!$. (The derived pullbacks of
[def-weil-derived-pullback-tensor-hom] used in the first
identification are the ones defined by exact inverse image followed by
the flat extension along the constant coefficient sheaf; no analogue of
these statements for the single exceptional leg $c_1$ is asserted
(the naive version $Li_F^*Rc_1^!K\cong Rd^!K$ is false).
