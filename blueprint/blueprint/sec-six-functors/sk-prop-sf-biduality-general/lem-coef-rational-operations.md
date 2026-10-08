+++
id = "lem-coef-rational-operations"
kind = "lemma"
title = "Identification with the rational internal Hom and exceptional inverse image"
order = 2152
uses = ["cor-coef-integral-internal-hom", "def-weil-derived-complete", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-inverse-image", "def-weil-integral-rational-qbar-compact-support", "def-weil-rationalization-karoubi", "lem-coef-integral-finite-extension", "lem-coef-integral-residue-tor", "lem-coef-normalized-dvr-effectivity", "lem-sf-tensor-ctf", "prop-coef-integral-exceptional-adjoint", "prop-weil-pbc-rational-transport", "thm-coef-rational-verdier"]
+++
In the rationalized constructible categories, the internal Hom
and exceptional inverse image agree with the operations defined
by coefficient passage in the manuscript. The integral tensor
product used for this passage is the completed derived tensor
product. In particular

$$
D_{X,E}K=R\mathcal Hom_E(K,\omega_{X,E}),
\qquad
Rf_E^!M\cong D_{X,E}f^*D_{Y,E}M
$$

for every separated finite-type $f:X\to Y$. The functor
$Rf_E^!$ is right adjoint to $Rf_{!,E}$ on these
constructible categories, and $\omega_{X,E}=Ra_{X,E}^!E$.
These identifications preserve evaluations, units, and counits,
including under finite scalar extension.

## Proof

Put $R=\mathcal O_E$, $\pi=\varpi_E$, and $A_n=R/\pi^n$.
For integral constructible $P,K$, their completed tensor is

$$
P\widehat\otimes_R^LK
=R\varprojlim_n(P_n\otimes_{A_n}^LK_n).
$$

The input reductions have uniform Tor intervals by
[lem-coef-integral-residue-tor]. Finite tensor preservation
[lem-sf-tensor-ctf] gives constructible tensor reductions
with the sum of those intervals. Tensor associativity makes
this a normalized tower, so
[lem-coef-normalized-dvr-effectivity] gives precisely these
reductions of the displayed complete object. It is therefore
an object of the integral constructible category.

Here is the completion adjunction needed to use ambient
tensor–Hom adjunction. For any ambient $R$-complex $N$,
set $\widehat N=R\varprojlim_n(N\otimes_R^LA_n)$.
The same effectivity lemma, which does not require boundedness,
shows that the canonical map $N\to\widehat N$ is an
isomorphism modulo every $\pi^n$. Its cone $C$ has
$C\otimes_R^LA_1=0$. The two-term free resolution of
$A_1$ shows that multiplication by $\pi$ on $C$ is
invertible. For a complete $M$, write
$M=R\varprojlim_n M_n$ as in
[def-weil-derived-complete]. The derived mapping complex
$R\operatorname{Hom}(C,M_n)$ is zero: multiplication by
$\pi$ is invertible through its first argument, whereas
$\pi^n$ is zero through its second argument. Since mapping
into a derived limit preserves that limit,
$R\operatorname{Hom}(C,M)=0$. Thus

$$
R\operatorname{Hom}(\widehat N,M)
\xrightarrow{\sim}R\operatorname{Hom}(N,M).
$$

This proves the required left-adjoint property of completion
directly for the completed coefficient sheaf used here.

Integral internal Hom preserves $D^b_c$ by
[cor-coef-integral-internal-hom]. Localize its functor in
both arguments and localize completed tensor product. Apply
the just proved completion adjunction to $N=P\otimes_R^LK$
and the complete integral representative $M$. Ambient
tensor–Hom adjunction then gives

$$
\Hom(P\widehat\otimes_R^LK,M)\otimes_RE
\cong
\Hom(P,R\mathcal Hom_R(K,M))\otimes_RE.
$$

By [def-weil-rationalization-karoubi], these are exactly
the Hom groups in the rationalized category. Naturality for
fractional morphisms follows by linearity. This identifies the
localized internal Hom with the coefficient-passage operation of
[def-weil-derived-pullback-tensor-hom], including its
evaluation. With $M=\omega$ it gives the first formula and
the functor of [thm-coef-rational-verdier].

The integral exceptional adjunction, its units and counits, and
the integral formula $Rf^!=D_Xf^*D_Y$ are
[prop-coef-integral-exceptional-adjoint]. Localize their
Hom-group adjunction by [prop-weil-pbc-rational-transport].
The localized left adjoint is precisely the compact-support
functor in [def-weil-integral-rational-qbar-compact-support].
The right adjoint is therefore the operation characterized in
[def-weil-exceptional-inverse-image]; uniqueness of a right
adjoint with its counit identifies the localized formula and all
its adjunction data. Taking $f=a_X$ gives the dualizing-object
identification.

For finite scalar extension, compact support commutes with the
finite free coefficient tensor: at finite levels this is the
projection comparison for a finite sum of the coefficient unit,
and finite free tensor commutes with the derived limit defining
integral compact support. The comparisons of
[lem-coef-integral-finite-extension] and coefficient
compatibility of pullback give the corresponding comparison for
$D_Xf^*D_Y$. Transposing it through the integral adjunction
identifies it with the mate of that compact-support comparison:
the adjunction formula uses exactly the evaluations and counits
preserved by the duality comparisons. Thus the units and
counits agree under finite extension as well as under
rationalization.

This proof is an identification inside the
specified constructible coefficient categories; it does not
replace scalar localization by an assertion that internal Hom
commutes with an arbitrary infinite coefficient extension on the
whole ambient derived category of sheaves.
