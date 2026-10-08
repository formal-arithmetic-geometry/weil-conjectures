+++
id = "lemma-weil-pbc-completed-map-reduction"
kind = "lemma"
title = "Finite reduction of the completed map"
order = 1347
uses = ["def-weil-pbc-completed-base-change-map", "def-weil-pbc-completed-frobenius-structures", "def-weil-pbc-completed-reduction-square", "lem-weil-pbc-finite-reduction-reconstruction", "lem-weil-pbc-rectangle-derived-limit", "lemma-weil-pbc-completed-frobenius-equivariance", "lemma-weil-pbc-completed-pullback-reduction", "lemma-weil-pbc-frobenius-tower-compatibility", "lemma-weil-pbc-level-map-derived-limit"]
+++
For every $n$, the diagram

$$
\begin{CD}
S\otimes^LP_n @>{\overline\xi_n}>> T\otimes^LP_n\\
@V{\alpha_n}V{\sim}V @VV{\delta_n}V{\sim}\\
B_n @>{v'_n}>> D_n
\end{CD}
$$

commutes. Hence reduction of
$\operatorname{Ex}^{\mathrm{comp}}_{\square,K}$ modulo $I^n$, conjugated
by the displayed canonical reduction isomorphisms, is exactly the S8
transported finite-level exchange map $v'_n=\operatorname{Ex}_{\square,K_n}$.
The squares for $n+1\to n$ commute, and the assertion is natural for
compatible tower endomorphisms. Under a Frobenius-equivariant datum, use
$\Phi_{Y'}P_n=P_n$ to give the two reductions their induced Weil structures.
Then

$$
\begin{aligned}
\alpha_n(\Theta_S\otimes1)
&=\Theta_{B,n}\Phi_{Y'}(\alpha_n),\\
\delta_n(\Theta_T\otimes1)
&=\Theta_{D,n}\Phi_{Y'}(\delta_n),
\end{aligned}
$$

and the displayed reduction square is a square of Weil objects.

## Proof

Under $S=A_\infty$ and the direct-image completion identification
$T\simeq C_\infty$, the completed exchange map is both limit composites

$$
V'H=H'V:A_\infty\longrightarrow D_\infty,
$$

followed by the inverse of direct-image/limit commutation. More explicitly,
if $d:T\to D_\infty$ is direct-image/limit commutation and
$c:C_\infty\to T$ is direct-image completion, then its construction gives
$dc=H'$. Functorial finite
reduction and the component equations of the limit rectangle give

$$
\tau_n\overline\xi_n=v_n\sigma_n.
$$

Consequently the two composites around the completed reduction square are

$$
\delta_n\overline\xi_n
=h'_n\tau_n\overline\xi_n=h'_nv_n\sigma_n
$$

and

$$
v'_n\alpha_n=v'_nh_n\sigma_n.
$$

They are equal term by term because $h'_nv_n=v'_nh_n$ in the finite-level
rectangle. Naturality of finite reduction makes $\sigma_n$ and $\tau_n$
commute with $n+1\to n$, and functoriality of tensor reduction does the same
for $\overline\xi_n$. Together with the four transition equations, this
shows that the completed squares commute with $K_{n+1}\to K_n$ on every
corner. The limit construction and all four reduction edges are
operator-equivariant, so the conjugated equality is operator-natural as well.

For Frobenius, the definition of $\Theta_S$ transports
$\Theta_{A,\infty}$ across $s$, and the $n$th product-cone component followed
by $h_n$ is $\alpha_n$. This gives the first displayed Weil equation. The
definition of $\Theta_T$ transports $\Theta_{D,\infty}$ across $t$, and its
$n$th component is $\delta_n$, giving the second. The completed Frobenius
equation for $\overline\xi_n$, together with finite-level equivariance of
$v'_n$, now says that every arrow of the reduction square is a Weil morphism.

## Detailed form

For every $n$, reduction of $\Ex^{\mathrm{comp}}_{\square,K}$ of
[def-weil-pbc-completed-base-change-map] modulo $I^n$, conjugated by
the canonical reduction isomorphisms, is exactly
$$
 \Ex_{\square,K_n}:Lg_n^*Rf_*K_n
 \xrightarrow{\sim}Rf'_*Lg_n'^*K_n.
$$
These reduction squares commute with $n+1\to n$ and with compatible
endomorphisms.

*Source note:* the reduction of the completed pullback is the formula
$Lf^*_{comp}M=\Rlim Lf^*(M\otimes^L_\Lambda\underline{\Lambda/I^n})$ of
Stacks Project, Lemma 61.20.2 ([Tag
099N](https://stacks.math.columbia.edu/tag/099N)), whose $n$-th level is
$Lf_n^*$ of the $n$-th level; Stacks states the formula for the completed
pullback of one object of $D(\mathcal C,\Lambda)$, whereas the displayed
statement reduces the completed base-change exchange map of
[def-weil-pbc-completed-base-change-map], which the verified entries
do not construct, and the blueprint adds that reduction together with its
compatibility with the transitions and with compatible endomorphisms.

## Proof

Tensoring the defining composite of
[def-weil-pbc-completed-base-change-map] with $P_n$ and using the
finite-reduction identifications of the reconstruction lemma and of the
completed-pullback reduction collapses it to the $n$-th component of the
rectangle equality of [lem-weil-pbc-rectangle-derived-limit], which is the
finite-level exchange isomorphism; the compatibilities with the transitions
follow from the tower structures.
