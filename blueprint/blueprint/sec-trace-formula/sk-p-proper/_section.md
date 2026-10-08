+++
id = "sk-p-proper"
kind = "section"
title = "Proper pushforward compatibility"
order = 2329
uses = ["sk-d-corr", "sk-d-integral", "sk-d-proper-pushforward", "sk-d-trace-class", "sk-def-sf-kv-maps", "sk-p-pairing", "sk-thm-sf-comp-composition", "sk-thm-sf-kunneth-verdier", "sk-thm-sf-package"]
lean = ["AlgebraicGeometry.ProEtale.GeometricOperations.borelMoorePushforward_traceClass"]
+++
*Proposition (sketch).*

Let $(C,c,u)$ be an endocorrespondence on $(X,K)$ and
let $(f,g):(C,c)\to(D,b)$ be a
proper pushforward diagram, with
$f:X\to Y$ and $g:C\to D$ proper and $b_i g=fc_i$ for $i=1,2$.
Put $F_c=\Fix(c)$, $F_b=\Fix(b)$, and let $h:F_c\to F_b$ be the induced map.
Then the trace classes satisfy

$$
\boxed{h_*\Tr_c(u)=\Tr_b([f,g]_!u)}
\quad\text{in }\operatorname{Hom}(A_{F_b},\omega_{F_b}),
$$

where $h_*$ is Borel–Moore pushforward.
No properness over $s$ of $X,Y,C,D$ and no Cartesian leg square are required.

## Proof

For the diagram of [sk-d-proper-pushforward], factor

$$
h:F_c\xrightarrow{\kappa}C\times_D F_b\xrightarrow{\pi}F_b.
$$

The map $\pi$ is the base change of the proper map $g$.
The middle scheme maps to $X\times_YX$ by $(c_1,c_2)$, and $\kappa$ is
the base change of the diagonal $\Delta_f:X\to X\times_YX$:
the fiber product imposes exactly the equality of the two legs defining
$F_c$ in [sk-d-corr]. Since $f$ is proper, its diagonal is a closed
immersion. Thus $\kappa$ and $h$ are proper, so the pushforward of
[sk-d-integral] is defined.

Put $q=f\times f$, $K'=Rf_*K$, $P_X=K\boxt D_XK$ and
$P_Y=K'\boxt D_YK'$. In the package of [sk-thm-sf-package], let
$\tau_f:Rf_*\omega_X\to\omega_Y$ be the exceptional counit and
$\mu_f:Rf_*M\otimes Rf_*N\to Rf_*(M\otimes N)$ the ordinary
adjoint of $\varepsilon_f^*\otimes\varepsilon_f^*$.
Define $\chi_f:Rf_*D_XK\to D_YK'$ by taking the tensor–Hom
adjoint of $\tau_f\,Rf_*\overline{\mathrm{ev}}_K\,\mu_f$.
With the comparison of [sk-def-sf-kv-maps], set

$$
\Pi_f=\mathrm{Ku}_!(f,f;K,D_XK)^{-1},\qquad
\rho_f=(1\boxt\chi_f)\Pi_f^{-1}:Rq_*P_X\to P_Y.
$$

Let $\delta_K:P_X\to R\Delta_{X*}\omega_X$ be adjoint to
$\overline{\mathrm{ev}}_K$, and define $\delta_{K'}$ similarly.
Here evaluation is preceded by tensor symmetry.

The proof has two kernel calculations. Writing
$\widetilde u=\kappa_X^{-1}[u]$ using [sk-d-corr], [sk-thm-sf-kunneth-verdier], they give

$$
\begin{aligned}
\widetilde{[f,g]_!u}
&=\rho_f\,Rq_*\widetilde u\,Rb_!\eta_g^*,\\
\delta_{K'}\rho_f
&=R\Delta_{Y*}\tau_f\,Rq_*\delta_K.
\end{aligned}
$$

For the first, tensor–Hom and exceptional adjunctions turn kernel
transport into the coefficient composite defining $[f,g]_!u$ in
[sk-d-proper-pushforward]. Compatibility with the specified
Künneth–Verdier maps is checked after the same two adjunctions:
both paths evaluate $f^*K'\to K$ against $D_XK$, then apply the
structural counit. For the second, take the ordinary diagonal adjoint.
The diagonal pullback of $\Pi_f$, followed by ordinary exchange,
is $\mu_f$, so both paths are the defining evaluation of $\chi_f$.
These are the two evaluation calculations of SGA 5, III,
(4.4.3)–(4.4.5), using only the data of [sk-thm-sf-package].

For the support calculation write $j:F_c\to C$, $a:F_c\to X$,
$i:F_b\to D$, $a_b:F_b\to Y$. Right-adjoint $!$-base change gives
$\zeta_c:Rj_*\omega_{F_c}\simeq Rc^!R\Delta_{X*}\omega_X$
and $\zeta_b$ similarly. Define
$\mathsf E:Rg_*Rc^!\to Rb^!Rq_*$ to be adjoint to
$Rb_!Rg_*Rc^!\simeq Rq_*Rc_!Rc^!\to Rq_*$.
Then

$$
Rb^!(R\Delta_{Y*}\tau_f)\,\mathsf E\,Rg_*\zeta_c
=\zeta_b\,Ri_*\tau_h.
$$

Indeed, after $Rb_!\dashv Rb^!$ both sides are exceptional
counits for the same composite $fa=a_bh$, pushed along $\Delta_Y$.
This verifies the support comparison of SGA 5, III, (4.4.6)–(4.4.7).
Only the two defining fixed squares are used as Cartesian squares.

Finally insert the diagonal dictionary of [sk-p-pairing] into
these three identities. The remaining ordinary units satisfy

$$
Rg_*\eta_j^*\,\eta_g^*=\eta_{gj}^*
=\eta_{ih}^*=Ri_*\eta_h^*\,\eta_i^*.
$$

Cancel $\zeta_b$ and take $i^*\dashv Ri_*$ adjoints. The result is

$$
\Tr_b([f,g]_!u)=\tau_h\,Rh_*\Tr_c(u)\,\eta_h^*,
$$

which is precisely [sk-d-integral]. Throughout, $Rc_!$ and $Rb_!$
are retained: the additional proper-support hypothesis in the statement
of SGA 5, III, Theorem 4.4 is not imposed. The full blueprint proves
the three comparisons separately; general trace compatibility is no
longer an external input.

Uses: [sk-d-corr], [sk-d-integral], [sk-d-proper-pushforward], [sk-d-trace-class], [sk-def-sf-kv-maps], [sk-p-pairing], [sk-thm-sf-kunneth-verdier], [sk-thm-sf-package]
