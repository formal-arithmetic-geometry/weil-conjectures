+++
id = "lem-trf-correspondence-class"
kind = "lemma"
title = "The class of a correspondence"
order = 2278
uses = ["def-trf-admissibility", "def-trf-correspondence-between-pairs", "def-trf-supported-class", "def-weil-derived-pullback-tensor-hom", "prop-functor-package"]
+++
In the setting of [def-trf-correspondence-between-pairs], let
$c=(c_1,c_2):C\to Z=Y\times_sX$ be the support of a correspondence from
$(X,K)$ to $(Y,L)$, and assume that $c$ and the projection
$p_1:Z\to Y$ are exceptionally admissible at $A$
([def-trf-admissibility]). Then tensor–Hom adjunction, the projection
formula and exceptional adjunction give a canonical isomorphism

$$
\operatorname{Hom}_{D(Z,A)}\bigl(Rc_!A_C,
R\mathcal Hom_A(Lp_2^*K,Rp_1^!L)\bigr)
\xrightarrow{\ \sim\ }
\operatorname{Hom}_{D(C,A)}\bigl(Lc_2^*K,Rc_1^!L\bigr),
$$

natural in $K$ and $L$. For a correspondence
$u:Lc_2^*K\to Rc_1^!L$, its *class* $[u]$ is the inverse image of $u$
under this isomorphism; it is a class supported on $c$ with values in
$R\mathcal Hom_A(Lp_2^*K,Rp_1^!L)$ in the sense of
[def-trf-supported-class], i.e. $[u]\in
H^0_C\bigl(Z,R\mathcal Hom_A(Lp_2^*K,Rp_1^!L)\bigr)$.

## Proof

Put $M=Lp_2^*K$ and $N=Rp_1^!L$; both lie in the bounded constructible
finite-Tor category on $Z$, the first by the pullback clause of
[def-weil-derived-pullback-tensor-hom], the second because $p_1$ is
exceptionally admissible. Then

$$
\begin{aligned}
\operatorname{Hom}_Z\bigl(Rc_!A_C,R\mathcal Hom_A(M,N)\bigr)
&\cong\operatorname{Hom}_Z\bigl(Rc_!A_C\otimes_A^{\mathrm L}M,N\bigr)\\
&\cong\operatorname{Hom}_Z\bigl(Rc_!(A_C\otimes_A^{\mathrm L}Lc^*M),N\bigr)
=\operatorname{Hom}_Z\bigl(Rc_!Lc^*M,N\bigr)\\
&\cong\operatorname{Hom}_C\bigl(Lc^*M,Rc^!N\bigr)\\
&\cong\operatorname{Hom}_C\bigl(Lc_2^*K,Rc_1^!L\bigr).
\end{aligned}
$$

The first arrow is the tensor–internal-Hom adjunction of
[def-weil-derived-pullback-tensor-hom]. The second is the
compact-support projection formula of [prop-functor-package] (clause
five) for $c$, applied with the constant sheaf $A_C$ in the first
variable and the finite-Tor complex $M$ in the second, and
$A_C\otimes_A^{\mathrm L}(-)$ is the identity. The third is the
exceptional adjunction $Rc_!\dashv Rc^!$ of [def-trf-admissibility]
for the admissible $c$. The last uses the pullback composition
$Lc^*Lp_2^*\cong L(p_2c)^*=Lc_2^*$ of
[def-weil-derived-pullback-tensor-hom] and the composition isomorphism
$Rc^!Rp_1^!\cong R(p_1c)^!=Rc_1^!$ of the exceptional inverse image
supplied with the admissibility datum of [def-trf-admissibility]. Every
arrow is a bijection natural in $K$ and $L$, so the composite is the
asserted isomorphism and $[u]$ is well defined. The final assertion is
the definition of $H^0_C$ in [def-trf-supported-class] with $i=c$,
$T=C$ and $P=R\mathcal Hom_A(M,N)$.
