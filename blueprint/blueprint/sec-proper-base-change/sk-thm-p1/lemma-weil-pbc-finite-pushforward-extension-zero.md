+++
id = "lemma-weil-pbc-finite-pushforward-extension-zero"
kind = "lemma"
title = "Finite pushforward and extension by zero"
order = 1176
uses = ["def-weil-pbc-extension-by-zero", "def-weil-pbc-finite-open-comparison", "lemma-weil-pbc-curve-locally-constant-reduction", "lemma-weil-pbc-finite-open-comparison-inverse", "lemma-weil-pbc-finite-stalk-formula", "lemma-weil-pbc-geometric-stalk-conservative"]
+++
In a Cartesian square with $j,j'$ open immersions and $\bar v$ finite,

$$
j_!v_*G\xrightarrow{\sim}\bar v_*j'_!G
$$

is the map of Definition [def-weil-pbc-finite-open-comparison]. It is
functorial in $G$, compatible with identity and composite finite maps, and
commutes with arbitrary base change.

## Proof

The preceding lemma proves that the specified map is an isomorphism and
gives both inverse equations.

For a morphism $\phi:G\to H$, naturality is the commutative square

$$
\begin{CD}
j_!v_*G @>{\beta_G}>> \bar v_*j'_!G\\
@V{j_!v_*\phi}VV @VV{\bar v_*j'_!\phi}V\\
j_!v_*H @>{\beta_H}>> \bar v_*j'_!H.
\end{CD}
$$

At $\bar y\in V$, both routes send
$(s_{\bar x})_{\bar x\mapsto\bar y}$ to
$(\phi_{\bar x}(s_{\bar x}))_{\bar x\mapsto\bar y}$; outside $V$ all four
stalks vanish. Thus the square commutes. The same calculation with the
inverse maps $\gamma_G,\gamma_H$ proves naturality of the inverse.

If $\bar v=\operatorname{id}_Y$ and $v=\operatorname{id}_V$, every fibre sum
has one summand. Both the unit–base-change construction of $\beta$ and the
section formula are the identity of $j_!G$. This proves identity
compatibility.

For composition, let $f_1:X_1\to Y$ and $f_2:X_2\to X_1$ be finite. Put
$U_i=X_i\times_YV$, let $g_1:U_1\to V$, $g_2:U_2\to U_1$, and denote the
open immersions by $j_0:V\to Y$, $j_i:U_i\to X_i$. The compatibility to
prove is the outer equality in

$$
\begin{CD}
(j_0)_!(g_1g_2)_*G
@>{\beta_{f_1,g_{2,*}G}}>>
f_{1,*}(j_1)_!g_{2,*}G
@>{f_{1,*}\beta_{f_2,G}}>>
f_{1,*}f_{2,*}(j_2)_!G\\
@V{\beta_{f_1f_2,G}}V{\sim}V
@. @VV{=}V\\
(f_1f_2)_*(j_2)_!G @= (f_1f_2)_*(j_2)_!G
@= (f_1f_2)_*(j_2)_!G .
\end{CD}
$$

At $\bar y\in V$, the upper route first groups a tuple by
$\bar x_1\mapsto\bar y$ and then by
$\bar x_2\mapsto\bar x_1$:

$$
\bigoplus_{\bar x_1\mapsto\bar y}
\left(\bigoplus_{\bar x_2\mapsto\bar x_1}G_{\bar x_2}\right)
\longrightarrow
\bigoplus_{\bar x_2\mapsto\bar y}G_{\bar x_2}.
$$

It is the canonical flattening of the doubly indexed finite sum. The lower
route is the same flattening for the composite fibre. Outside $V$ every
term is zero. This proves composition compatibility; applying the reverse
grouping proves the corresponding equation for $\gamma$.

Finally let $h:\widetilde Y\to Y$ be arbitrary and put tildes on all four
schemes and maps after base change. If $h_X,h_V,h_U$ are the projections,
open and finite base change give the vertical isomorphisms in

$$
\begin{CD}
h^{-1}(j_Y)_!v_*G
@>{h^{-1}\beta_{\bar v,j_Y,G}}>>
h^{-1}\bar v_*(j_X)_!G\\
@V{\sim}VV @VV{\sim}V\\
(\widetilde j_Y)_!\widetilde v_*h_U^{-1}G
@>{\beta_{\widetilde{\bar v},\widetilde j_Y,h_U^{-1}G}}>>
\widetilde{\bar v}_*(\widetilde j_X)_!h_U^{-1}G .
\end{CD}
$$

The left vertical map is
$h^{-1}(j_Y)_!\cong(\widetilde j_Y)_!h_V^{-1}$ followed by
$h_V^{-1}v_*\cong\widetilde v_*h_U^{-1}$; the right vertical map uses the
same two comparisons in the other order. At a geometric point of
$\widetilde V$, both routes pull each component $s_{\bar x}$ to the
corresponding component over the pulled-back geometric fibre. Off
$\widetilde V$, both routes are zero. The rectangle therefore commutes,
and the inverse rectangle follows from the two inverse equations. This
supplies the functoriality omitted at Tag `0GJ1`.

## Detailed form

The morphism $\beta_{\bar v,j_V,G}$ of
[def-weil-pbc-finite-open-comparison] is an isomorphism. It is
natural in $G$, compatible with identity and composite finite maps, and stable
under extension of the ground field.

## Proof

At a geometric point $\bar y\to Y$, the stalk of the left side is
$(v_*G)_{\bar y}$ if $\bar y\in V$ and $0$ otherwise; the stalk of the right
side is the sum over the geometric points of the finite fibre $X_{\bar y}$ of
the stalks of the extension by zero [def-weil-pbc-extension-by-zero], namely
$G_{\bar x}$ for $\bar x\in U_{\bar y}$ and $0$ otherwise, and $U_{\bar
y}=X_{\bar y}$ precisely when $\bar y\in V$. By
[lemma-weil-pbc-finite-stalk-formula] both sides are the same finite direct sum,
and the map of [def-weil-pbc-finite-open-comparison] is the
identity on each summand; conservativity of geometric stalks gives the
isomorphism. The remaining compatibilities are built into the construction.
