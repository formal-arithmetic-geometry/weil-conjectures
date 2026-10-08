+++
id = "lem-trf-trace-source-exchange"
kind = "lemma"
title = "Exchange of the trace-class sources: the kernel of the coefficient pushforward"
order = 2330
uses = ["def-exchange-projection", "def-sf-kv-maps", "def-trf-coefficient-pushforward", "def-trf-kernel-pushforward-maps", "fix-prop-adjunctions", "fix-prop-coherence", "fix-prop-projection-formula", "lem-trf-correspondence-class", "lem-trf-exceptional-internal-hom-exchange", "thm-trf-kunneth-verdier", "thm-trf-verdier-duality"]
+++
Let $(f,g):(C,c)\to(D,b)$ be a proper pushforward diagram of
[def-trf-coefficient-pushforward] (no Cartesian leg square, no properness
over $s$), with the notation and admissibility of
[def-trf-kernel-pushforward-maps]. Then the kernel class of the coefficient
pushforward $[f,g]_!u$ is the transported kernel class of $u$:

$$
[\,[f,g]_!u\,]_P
=\rho_f\circ Rq_*[u]_P\circ\Xi\circ Rb_!\eta_g
\quad:\ Rb_!A_D\longrightarrow P_Y ,
$$

where $\eta_g:A_D\to Rg_*A_C$ is the unit.

## Proof

Throughout, $p_1,p_2$ and $p'_1,p'_2$ are the projections of
$X\times_sX$ and $Y\times_sY$, so that $p'_iq=fp_i$; put
$H_X=R\mathcal Hom(p_2^*K,p_1^!K)$ and $H_Y=R\mathcal Hom(p'^*_2K',p'^!_1K')$,
and let $\kappa_X=\kappa_{K,K}:P_X\xrightarrow{\sim}H_X$,
$\kappa_Y=\kappa_{K',K'}:P_Y\xrightarrow{\sim}H_Y$ be the Künneth–Verdier
isomorphisms of [thm-trf-kunneth-verdier].

*Step 0: kernel class versus class.* For a correspondence $v$ on
$(X,K)$ supported on $c$, let $[v]:Rc_!A_C\to H_X$ be its class of
[lem-trf-correspondence-class]. The external duality of
[thm-trf-verdier-duality] is the exchange
$\mathcal H_c(K)\cong Rc^!H_X$ of [lem-trf-exceptional-internal-hom-exchange]
followed by $Rc^!\kappa_X^{-1}$, and that exchange is built from the
tensor–Hom adjunction, the projection formula and $Rc_!\dashv Rc^!$ in
the same order as the bijection of [lem-trf-correspondence-class]. Hence
the exceptional adjoint of $A_C\to\mathcal H_c(K)\cong Rc^!H_X$ is $[v]$,
and $[v]_P=\kappa_X^{-1}[v]$. Likewise $[w]_P=\kappa_Y^{-1}[w]$ on $D$.

*Step 1: the transport map.* Let $\delta_1:Rq_*p_1^!\to p'^!_1Rf_*$ be the
exceptional adjoint of
$Rp'_{1!}Rq_!p_1^!\cong Rf_!Rp_{1!}p_1^!\xrightarrow{Rf_!\varepsilon}Rf_!$
(the recipe of $\delta$ in [def-trf-coefficient-pushforward] for the square
$p'_1q=fp_1$). Let $\Phi:Rq_*H_X\to H_Y$ be the tensor–Hom adjoint of

$$
\begin{aligned}
Rq_*H_X\otimes p'^*_2K'
&\xrightarrow{\ \mathrm{PF}\ }Rq_*\bigl(H_X\otimes p_2^*f^*Rf_*K\bigr)
\xrightarrow{\ \varepsilon_f\ }Rq_*\bigl(H_X\otimes p_2^*K\bigr)\\
&\xrightarrow{\ \mathrm{ev}\ }Rq_*p_1^!K
\xrightarrow{\ \delta_1\ }p'^!_1K',
\end{aligned}
$$

with $\mathrm{PF}$ the projection map of [fix-prop-projection-formula] for
the proper $q$ and $q^*p'^*_2=p_2^*f^*$. The lemma follows from the two
identities

$$
\text{(a)}\quad \kappa_Y\circ\rho_f=\Phi\circ Rq_*\kappa_X,
\qquad
\text{(b)}\quad [\delta\circ Rg_*v\circ\gamma]
=\Phi\circ Rq_*[v]\circ\Xi\circ Rb_!\eta_g ,
$$

since with $v=u$, Step 0 turns (b) into
$[\,[f,g]_!u\,]_P=\kappa_Y^{-1}\Phi\,Rq_*(\kappa_X[u]_P)\,\Xi\,Rb_!\eta_g$,
and (a) turns this into the assertion.

*Step 2: proof of (b).* A map $Rb_!A_D\to H_Y$ is determined by its
image under the bijection of [lem-trf-correspondence-class], and further
by the adjoint of that image along $Rb_{1!}\dashv b_1^!$, a map
$Rb_{1!}b_2^*K'\to K'$ (using $Rb_{1!}=Rp'_{1!}Rb_!$ and
$b^!p'^!_1=b_1^!$). For the left side of (b), the definition of $\delta$
gives the adjoint

$$
Rb_{1!}b_2^*K'\xrightarrow{Rb_{1!}\gamma}Rb_{1!}Rg_*c_2^*K
\xrightarrow{\Xi_1}Rf_!Rc_{1!}c_2^*K
\xrightarrow{Rf_!v^\flat}Rf_!K=K',
$$

where $v^\flat=\varepsilon_{c_1}\circ Rc_{1!}v$ is the adjoint of $v$. For the right
side, unwind the bijection: tensor with $p'^*_2K'$, apply the projection
formula for $b$, then $\Phi$, then the counit of $p'_1$. By the definition
of $\delta_1$, the counit of $p'_1$ after $Rp'_{1!}\delta_1$ is
$Rf_!$ of the counit of $p_1$; by the naturality of $\mathrm{PF}$ and its
compatibility with the composition law ([fix-prop-projection-formula],
[fix-prop-coherence]), the projection formulas for $b$, $q$ and $c$
combine into the projection formula for $bg=qc$, and the class $[v]$ is
turned back into $v^\flat$. The right side thus becomes

$$
Rb_{1!}b_2^*K'\xrightarrow{\eta_g}Rb_{1!}Rg_*g^*b_2^*K'
=Rb_{1!}Rg_*c_2^*f^*K'
\xrightarrow{\varepsilon_f}Rb_{1!}Rg_*c_2^*K
\xrightarrow{\Xi_1}Rf_!Rc_{1!}c_2^*K\xrightarrow{Rf_!v^\flat}K' .
$$

Its first two arrows are $Rb_{1!}\gamma$ by the definition of $\gamma$,
so the two adjoints coincide, proving (b).

*Step 3: proof of (a).* Both sides are maps $Rq_*P_X\to H_Y$; compare
their adjoints $Rp'_{1!}(Rq_*P_X\otimes p'^*_2K')\to K'$ as in Step 2. By
[def-sf-kv-maps] (iv), $\kappa_X$ is $\beta$ followed by the exceptional
Künneth $\alpha_{\operatorname{id},a_X}$, whose exceptional adjoint is the
counit $\varepsilon_{a_X}$ of $Ra_{X!}\dashv Ra_X^!$ after $\mathrm{Ku}_!$
([def-sf-kv-maps] (ii)). Hence the adjoint of $\kappa_X$ evaluates the
factor $D_XK$ of $P_X$ against the $p_2^*K$-variable and then applies
$\varepsilon_{a_X}$ to $\omega_X$ in the second factor; similarly for
$\kappa_Y$. On the left side, $\rho_f$ first undoes $\Pi_f$, and the
defining evaluation of $\chi_f$ turns the evaluation of $D_YK'$ against
$K'$ into $\tau_f\circ Rf_*\mathrm{ev}_K\circ\mu_f$; since
$\varepsilon_{a_Y}\circ Ra_{Y!}\tau_f=\varepsilon_{a_X}$ (the counit of
$a_X=a_Yf$ is the pasted counit, [fix-prop-adjunctions], item 3), and
$\mu_f$ and $\Pi_f$ are adjoint to $\varepsilon_f\otimes\varepsilon_f$
(the projection maps and the exchange $\operatorname{Ex}_*$ entering
$\mathrm{Ku}_!$ are adjoint to counits, [def-exchange-projection],
[fix-prop-projection-formula]), the left side becomes: apply
$\varepsilon_f:f^*K'\to K$ to the $p_2^*K'$-variable, evaluate $D_XK$
against it, and apply $\varepsilon_{a_X}$. On the right side, $\Phi$ applies
the same $\varepsilon_f$ and then the adjoint of $\kappa_X$, followed by
$\delta_1$ and the counit of $p'_1$, which together are $Rf_!$ of the
counit of $p_1$; this is the same composite. Hence (a) holds, and with it
the lemma.
