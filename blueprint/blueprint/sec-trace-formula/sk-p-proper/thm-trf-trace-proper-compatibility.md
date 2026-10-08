+++
id = "thm-trf-trace-proper-compatibility"
kind = "theorem"
title = "Proper global trace comparison; Varshavsky 1.2.5"
order = 2332
uses = ["def-trf-borel-moore-pushforward", "def-trf-coefficient-pushforward", "def-trf-kernel-pushforward-maps", "def-trf-trace-class", "fix-prop-adjunctions", "lem-trf-fixed-map-proper", "lem-trf-trace-map-exchange", "lem-trf-trace-map-from-external-duality", "lem-trf-trace-source-exchange", "prop-trf-pairing-point-normalization", "thm-sf-comp-composition"]
+++
Let $(C,c,u)$ be an admissible correspondence on $(X,K)$, with
$K\in D^b_{ctf}(X,A)$, and let $(f,g):(C,c)\to(D,b)$ be a proper pushforward
diagram of [def-trf-coefficient-pushforward]: $f:X\to Y$ and $g:C\to D$ are
proper and $b_ig=fc_i$ for $i=1,2$. Assume the exceptional admissibility of
[def-trf-kernel-pushforward-maps]. Let
$h:F_c=\operatorname{Fix}(c)\to F_b=\operatorname{Fix}(b)$ be the induced
map, proper by [lem-trf-fixed-map-proper]. Then

$$
h_*\operatorname{Tr}_c(u)
=
\operatorname{Tr}_b\bigl([f,g]_!u\bigr)
\qquad\text{in }\operatorname{Hom}(A_{F_b},\omega_{F_b}),
$$

where $\operatorname{Tr}$ is the trace class of [def-trf-trace-class] and
$h_*$ is the Borel–Moore pushforward of [def-trf-borel-moore-pushforward].
No properness over $s$ of $X,Y,C,D$ and no Cartesian leg square is
required.

## Proof

Write $u'=[f,g]_!u$ and use the notation of
[def-trf-kernel-pushforward-maps].

*Step 1: the trace class in adjoint form.* By [def-trf-trace-class] and the
construction of $\mathfrak t_{c,K}$ in
[lem-trf-trace-map-from-external-duality] (recalled at the end of
[def-trf-kernel-pushforward-maps]), $\operatorname{Tr}_c(u)$ is the
$i_c^*\dashv Ri_{c*}$ adjoint of

$$
T_c:A_C\xrightarrow{\widetilde u}\mathcal H_c(K)\cong Rc^!P_X
\xrightarrow{Rc^!\delta_K}Rc^!R\Delta_{X*}\omega_X
\xrightarrow{\zeta_c^{-1}}Ri_{c*}\omega_{F_c},
$$

that is, $T_c=Ri_{c*}\operatorname{Tr}_c(u)\circ\eta_{i_c}$; similarly
$T_b=Ri_{b*}\operatorname{Tr}_b(u')\circ\eta_{i_b}$. By the definition of the
kernel class, the exceptional adjoint of $\zeta_cT_c$ is
$\delta_K\circ[u]_P:Rc_!A_C\to R\Delta_{X*}\omega_X$, and that of $\zeta_bT_b$
is $\delta_{K'}\circ[u']_P$. (This is the diagonal dictionary of
[prop-trf-pairing-point-normalization], read before restriction to the
diagonal.)

*Step 2: transport along $g$.* For any $\varphi:A_C\to Rc^!M$ with
exceptional adjoint $\varphi^\flat$, the exceptional adjoint of
$\mathsf E\circ Rg_*\varphi\circ\eta_g:A_D\to Rb^!Rq_*M$ is
$Rq_*\varphi^\flat\circ\Xi\circ Rb_!\eta_g$: indeed
$\varepsilon_b\circ Rb_!\mathsf E=Rq_*\varepsilon_c\circ\Xi$ by the definition
of $\mathsf E$, and $\Xi$ is natural. Moreover postcomposition with $Rb^!\psi$
corresponds to postcomposition with $\psi$.

*Step 3: the kernel calculations.* By [lem-trf-trace-source-exchange] and
part (1) of [lem-trf-trace-map-exchange],

$$
\delta_{K'}[u']_P=\delta_{K'}\rho_f\,Rq_*[u]_P\,\Xi\,Rb_!\eta_g
=R\Delta_{Y*}\tau_f\circ Rq_*\bigl(\delta_K[u]_P\bigr)\circ\Xi\circ Rb_!\eta_g .
$$

By Step 1 and Step 2 (with $\varphi=\zeta_cT_c$, $M=R\Delta_{X*}\omega_X$,
$\psi=R\Delta_{Y*}\tau_f$), the right side is the exceptional adjoint of
$Rb^!(R\Delta_{Y*}\tau_f)\circ\mathsf E\circ Rg_*(\zeta_cT_c)\circ\eta_g$, while
the left side is the exceptional adjoint of $\zeta_bT_b$. Hence, using part
(2) of [lem-trf-trace-map-exchange],

$$
\zeta_bT_b
=Rb^!(R\Delta_{Y*}\tau_f)\,\mathsf E\,Rg_*\zeta_c\circ Rg_*T_c\circ\eta_g
=\zeta_b\circ Ri_{b*}\tau_h\circ Rg_*T_c\circ\eta_g ,
$$

and cancelling the isomorphism $\zeta_b$,
$T_b=Ri_{b*}\tau_h\circ Rg_*T_c\circ\eta_g$.

*Step 4: the unit identities.* The units of composite adjunctions are the
composite units ([fix-prop-adjunctions], item 3), and
$gi_c=i_bh$ ([def-trf-coefficient-pushforward]), so, with the composition
isomorphisms of [thm-sf-comp-composition],

$$
Rg_*\eta_{i_c}\circ\eta_g=\eta_{gi_c}=\eta_{i_bh}=Ri_{b*}\eta_h\circ\eta_{i_b}.
$$

Substituting $T_c=Ri_{c*}\operatorname{Tr}_c(u)\circ\eta_{i_c}$ and using the
naturality of $\eta$,

$$
T_b=Ri_{b*}\bigl(\tau_h\circ Rh_*\operatorname{Tr}_c(u)\circ\eta_h\bigr)\circ\eta_{i_b}.
$$

Comparing with $T_b=Ri_{b*}\operatorname{Tr}_b(u')\circ\eta_{i_b}$ and taking
$i_b^*\dashv Ri_{b*}$ adjoints,

$$
\operatorname{Tr}_b([f,g]_!u)=\tau_h\circ Rh_*\operatorname{Tr}_c(u)\circ\eta_h .
$$

The right side is the composite defining $h_*\operatorname{Tr}_c(u)$ in
[def-trf-borel-moore-pushforward] ($\eta_h$, then $Rh_*$ of the section, then
$Rh_*\omega_{F_c}\cong Rh_!Rh^!\omega_{F_b}\to\omega_{F_b}$, which is
$\tau_h$). This proves the theorem. Throughout, $Rc_!$ and $Rb_!$ are
retained, so the proper-support hypothesis of SGA 5, III, Theorem 4.4 is not
imposed.
