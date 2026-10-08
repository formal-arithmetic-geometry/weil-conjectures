+++
id = "thm-pur-smooth-base-change-coherence"
kind = "theorem"
title = "Smooth base-change coherence"
order = 2018
uses = ["cor-pur-vector-bundle-purity", "def-coefficient-twists-detailed", "def-exchange-projection", "def-pur-conventions", "def-pur-smooth-purity-map", "def-sbc-smooth-morphisms", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-pur-coprojection", "lem-pur-diagonal-base-change", "lem-pur-smb-extraordinary", "thm-pur-cohomological-smoothness", "thm-pur-diagonal-dualizing-object", "thm-pur-dnc-invariance"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
$A=A_{E,n}$, and let

$$
\begin{array}{ccc}
X'&\xrightarrow{\ u\ }&X\\
f'\downarrow&&\downarrow f\\
Y'&\xrightarrow{\ v\ }&Y
\end{array}
$$

be a Cartesian square with $f$ smooth of relative dimension $d$ and
$K\in D^b_{ctf}(Y,\Lambda)$. The square

$$
\begin{array}{ccc}
Lu^*Lf^*K(d)[2d]
& \xrightarrow{\ Lu^*\gamma_{f,K}\ }
& Lu^*Rf^!K\\
\big\downarrow\ \sim
& & \big\downarrow\ \operatorname{Ex}^{!,\mathrm{sm}}_{f,v,K}\\
Lf'^*Lv^*K(d)[2d]
& \xrightarrow{\ \gamma_{f',Lv^*K}\ }
& Rf'^!Lv^*K
\end{array}
$$

commutes, i.e. the pullback of the purity isomorphism is the purity
isomorphism of the base change.

## Proof

Both composites are built from the purity construction of
[def-pur-smooth-purity-map] for $f$ and for $f'$. The dualizing-object
versions are compatible: the identification
$\omega_f\cong\Lambda_X(d)[2d]$ of [thm-pur-diagonal-dualizing-object]
is compatible with the base change $v$ because its constituents are:
the diagonal (the square of $f'$ is the base change of the square of
$f$ – the diagonal of the base change is the base change of the
diagonal of $f$, [lem-pur-diagonal-base-change] – and
[thm-pur-dnc-invariance] and
[cor-pur-vector-bundle-purity] are compatible with base change by
their statements, the tangent bundle of the base change being the base
change of the tangent bundle), the smooth base change
[lem-pur-smb-extraordinary] (the exchange is base-change
compatible by [def-exchange-projection]), and the co-projection
[lem-pur-coprojection]. The tensor formula
[thm-pur-cohomological-smoothness] is compatible
with base change together with the adjunction (the canonical map is the
mate of the projection formula, and base change of the adjunction is
the adjunction of the base change), and the twist isomorphisms
[def-coefficient-twists-detailed] are compatible with the pullback; the
square is the composite of these compatibilities. The transitivity
under successive base changes is the same statement for the transposed
compositions of the canonical base-change maps (the exchange of
[def-exchange-projection] composes, and the constructions are all
canonical).
