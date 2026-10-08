+++
id = "def-weil-pbc-intrinsic-completion"
kind = "definition"
title = "Intrinsic derived completion"
order = 1247
uses = ["def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-derived-inverse-limit"]
+++
For $m\geq1$, let

$$
 Q_m=K(A_T;a_1^m,\dots,a_r^m)
   =\bigotimes_{j=1}^r[A_T\xrightarrow{a_j^m}A_T]
$$

in cohomological degrees $[-r,0]$. For each factor define a chain map

$$
 [A_T\xrightarrow{a_j^{m+1}}A_T]
 \longrightarrow[A_T\xrightarrow{a_j^m}A_T]
$$

whose degree $-1$ component is multiplication by $a_j$ and whose degree $0$
component is the identity. Their tensor product is a chain map
$q_{m+1,m}:Q_{m+1}\to Q_m$; the composites $q_{m+2,m}=q_{m+1,m}q_{m+2,m+1}$
make $(Q_m)_m$ a strict tower.

For a functorial K-flat representative $QK$, the complexes
$QK\otimes_{A_T}Q_m$ form an object of $D(\operatorname{Tow}_{A}(T))$. Define

$$
 K^{\wedge}_{\mathrm{Kos}}
   =\Rlim_m(QK\otimes_{A_T}Q_m).
$$

The compatible degree-zero maps $A_T\to Q_m$ define $K\to
K^{\wedge}_{\mathrm{Kos}}$. The object $K$ is derived $I$-complete if this
map is an isomorphism.

Derived completeness here is the condition
$K\xrightarrow{\sim}\Rlim(K\otimes^L_\Lambda\underline{\Lambda/I^n})$ of
Stacks Project, Lemma 61.20.1 (Tag
[099M](https://stacks.math.columbia.edu/tag/099M), Section 61.20, Tag
[099L](https://stacks.math.columbia.edu/tag/099L)): the Stacks entry assumes
a Noetherian ring $\Lambda$ and an ideal $I$, and presents the completion as
the left adjoint of $D_{comp}(\mathcal C,\Lambda)\subset D(\mathcal
C,\Lambda)$, whereas the form used here is the Koszul model $Q_m$ over
$A=\mathcal O_E$, $I=(\varpi)$, whose agreement with the quotient-tower form
of 61.20.1 is [prop-weil-pbc-koszul-reconstruction].
