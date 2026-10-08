+++
id = "lem-trf-trace-map-exchange"
kind = "lemma"
title = "Exchange of the trace maps: evaluation and support"
order = 2331
uses = ["def-exchange-projection", "def-sf-kv-maps", "def-trf-coefficient-pushforward", "def-trf-kernel-pushforward-maps", "fix-lem-exchanges", "fix-prop-adjunctions", "fix-prop-projection-formula", "lem-sf-kunneth-coherence", "lem-sf-mate", "lem-trf-fixed-map-proper", "prop-trf-fixed-square-cartesian", "thm-sf-comp-composition", "thm-sf-kunneth-relative", "thm-trf-dualizing-complex-composition", "thm-trf-fixed-point-base-change"]
+++
Let $(f,g):(C,c)\to(D,b)$ be a proper pushforward diagram of
[def-trf-coefficient-pushforward] (no Cartesian leg square, no properness
over $s$), with the notation and admissibility of
[def-trf-kernel-pushforward-maps]. Then:

1. *(evaluation)* as maps $Rq_*P_X\to R\Delta_{Y*}\omega_Y$,
$$
\delta_{K'}\circ\rho_f=R\Delta_{Y*}\tau_f\circ Rq_*\delta_K ;
$$
1. *(support)* as maps
$Rg_*Ri_{c*}\omega_{F_c}=Ri_{b*}Rh_*\omega_{F_c}\to Rb^!R\Delta_{Y*}\omega_Y$,
$$
Rb^!\bigl(R\Delta_{Y*}\tau_f\bigr)\circ\mathsf E\circ Rg_*\zeta_c
=\zeta_b\circ Ri_{b*}\tau_h ,
$$
where the source identification is $gi_c=i_bh$.

Moreover, for a Cartesian square $(\beta',\alpha',\beta,\alpha)$
($\beta:V\to W$, $\alpha:U\to W$ proper, $V'=V\times_WU$) the exceptional
adjoint of the right-adjoint base-change isomorphism
$R\alpha'_*R\beta'^!\cong R\beta^!R\alpha_*$ (the mate of
$\operatorname{Ex}_!$) is
$R\beta_!R\alpha'_*R\beta'^!\cong R\alpha_!R\beta'_!R\beta'^!
\xrightarrow{\varepsilon}R\alpha_*$, the composition law followed by the
counit of $\beta'$.

## Proof

*The last assertion.* The base-change isomorphism is the mate of
$\operatorname{Ex}_!:\alpha^*R\beta_!\cong R\beta'_!\alpha'^*$ under the four
adjunctions ([fix-prop-adjunctions], item 4). Taking the exceptional adjoint
of a mate and using the triangle identities (the mate calculus of
[lem-sf-mate]) expresses it through $\operatorname{Ex}_!$, the unit of
$\alpha$ and the counits of $\alpha'$ and $\beta'$; since $\alpha,\alpha'$ are
proper, $\operatorname{Ex}_!=\operatorname{Ex}_*$ is compatible with the
composition law $R\beta_!R\alpha'_!\cong R\alpha_!R\beta'_!$
([fix-lem-exchanges], items 1 and 4; [thm-sf-comp-composition]), and the
unit–counit pair of $\alpha'$ cancels. What remains is the displayed
composite.

*Evaluation (1).* Both sides are maps into $R\Delta_{Y*}\omega_Y$, so it
suffices to compare their adjoints for $\Delta_Y^*\dashv R\Delta_{Y*}$. The
adjoint of $\delta_{K'}$ is $\mathrm{ev}_{K'}\circ\mathrm{sym}:K'\otimes
D_YK'\to\omega_Y$, so the left side has adjoint
$\mathrm{ev}_{K'}\circ\mathrm{sym}\circ(1\otimes\chi_f)\circ\Delta_Y^*\Pi_f^{-1}$.
The adjoint of the right side is
$\tau_f\circ Rf_*(\mathrm{ev}_K\circ\mathrm{sym})\circ\mathrm{Ex}$, where
$\mathrm{Ex}:\Delta_Y^*Rq_*\to Rf_*\Delta_X^*$ is the exchange map of the
commutative square $q\Delta_X=\Delta_Yf$ (adjoint to
$f^*\Delta_Y^*Rq_*=\Delta_X^*q^*Rq_*\xrightarrow{\varepsilon_q}\Delta_X^*$, as in
[def-exchange-projection]). We claim

$$
\mathrm{Ex}\circ\Delta_Y^*\Pi_f=\mu_f:
Rf_*K\otimes Rf_*D_XK\longrightarrow Rf_*(K\otimes D_XK).
$$

Indeed $\mathrm{Ku}_!$ of [def-sf-kv-maps] (i) is the composite of
[thm-sf-kunneth-relative], built from the composition law, two projection
formulas and one base change; for proper maps these are the direct-image
projection maps and $\operatorname{Ex}_*$ (compatibility with $Rf_!\cong Rf_*$,
[thm-sf-kunneth-relative], with the projection formula,
[lem-sf-kunneth-coherence] (iv), [fix-prop-projection-formula]), each adjoint to a
counit ([def-exchange-projection]). By naturality and the triangle
identities ([fix-prop-adjunctions]) the inverse $\Pi_f$ is therefore the
adjoint of $q^*(K'\boxtimes Rf_*D_XK)=f^*Rf_*K\boxtimes f^*Rf_*D_XK
\xrightarrow{\varepsilon_f\boxtimes\varepsilon_f}K\boxtimes D_XK$, i.e.
$\varepsilon_q\circ q^*\Pi_f=\varepsilon_f\boxtimes\varepsilon_f$. Then
$\mathrm{Ex}\circ\Delta_Y^*\Pi_f$ is adjoint to
$\Delta_X^*(\varepsilon_q\circ q^*\Pi_f)=\varepsilon_f\otimes\varepsilon_f$,
which is the defining adjoint of $\mu_f$. With the claim, the adjoint of
the right side composed with $\Delta_Y^*\Pi_f$ is
$\tau_f\circ Rf_*(\mathrm{ev}_K\circ\mathrm{sym})\circ\mu_f$, and by the
definition of $\chi_f$ (after the symmetry, which commutes with $\mu_f$) this
is $\mathrm{ev}_{K'}\circ\mathrm{sym}\circ(1\otimes\chi_f)$. Since $\Pi_f$ is
an isomorphism, the two adjoints agree, proving (1).

*Support (2).* Both sides are maps into $Rb^!(-)$; compare their exceptional
adjoints for $Rb_!\dashv Rb^!$, which are maps
$Rb_!Ri_{b*}Rh_*\omega_{F_c}\to R\Delta_{Y*}\omega_Y$. The fixed squares of $c$
and $b$ are Cartesian ([prop-trf-fixed-square-cartesian]), $i_c,i_b$ are closed
immersions (base changes of the diagonals of the separated $X$, $Y$), and
$\zeta_c,\zeta_b$ are built from the right-adjoint base change of
[thm-trf-fixed-point-base-change] and
[thm-trf-dualizing-complex-composition]. By the last assertion, the exceptional
adjoint of $\zeta_c$ is
$Rc_!Ri_{c*}\omega_{F_c}\cong Rc_!Ri_{c!}Rd_c^!\omega_X\cong R\Delta_{X*}Rd_{c!}Rd_c^!\omega_X
\xrightarrow{\varepsilon_{d_c}}R\Delta_{X*}\omega_X$, and likewise for
$\zeta_b$.

For the left side, the definition of $\mathsf E$ gives
$\varepsilon_b\circ Rb_!\mathsf E=Rq_*\varepsilon_c\circ\Xi$, so its adjoint is

$$
R\Delta_{Y*}\tau_f\circ Rq_*\bigl(\varepsilon_c\circ Rc_!\zeta_c\bigr)\circ\Xi
=R\Delta_{Y*}\bigl(\tau_f\circ Rf_*\varepsilon_{d_c}\bigr)
$$

after the composition-law identifications, and
$\tau_f\circ Rf_*\varepsilon_{d_c}$ is the counit of $R(fd_c)_!\dashv R(fd_c)^!$
at $\omega_Y$ ([fix-prop-adjunctions], item 3), with
$\omega_{F_c}\cong R(fd_c)^!\omega_Y$ by
[thm-trf-dualizing-complex-composition]. For the right side, its adjoint is
$R\Delta_{Y*}\bigl(\varepsilon_{d_b}\circ Rd_{b*}\tau_h\bigr)$, and
$\varepsilon_{d_b}\circ Rd_{b*}\tau_h$ is the counit for $d_bh$ at $\omega_Y$
by the same pasting. Since $fd_c=d_bh$ ([def-trf-coefficient-pushforward]),
these are the counit for one and the same morphism, and the two
composition-law identifications of the source with
$R\Delta_{Y*}R(fd_c)_!\omega_{F_c}$ agree by the associativity of
[thm-sf-comp-composition] (the maps $h$, $q$, $g$ being proper by
[lem-trf-fixed-map-proper]). Hence the adjoints agree, proving (2). Only the
two fixed squares are used as Cartesian squares.
