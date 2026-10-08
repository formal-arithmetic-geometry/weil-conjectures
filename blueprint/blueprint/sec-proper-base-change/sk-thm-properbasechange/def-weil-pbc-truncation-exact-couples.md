+++
id = "def-weil-pbc-truncation-exact-couples"
kind = "definition"
title = "The two truncation exact couples"
order = 1317
uses = ["def-weil-pbc-derived-exchange", "def-weil-pbc-hypercohomology-filtrations"]
+++
For every $q\geq a$, set

$$
\begin{aligned}
A_q&=g^{-1}Rf_*\tau_{\leq q}K,&
G_q&=g^{-1}Rf_*\mathcal H^q(K)[-q],\\
B_q&=Rf'_*g'^{-1}\tau_{\leq q}K,&
H_q&=Rf'_*g'^{-1}\mathcal H^q(K)[-q].
\end{aligned}
$$

The canonical truncation triangle and its exchanged image are

$$
\begin{CD}
A_{q-1}@>{i_q}>>A_q@>{j_q}>>G_q@>{k_q}>>A_{q-1}[1]\\
@V{e_{q-1}}VV@V{e_q}VV@V{\bar e_q}VV@VV{e_{q-1}[1]}V\\
B_{q-1}@>{i'_q}>>B_q@>{j'_q}>>H_q@>{k'_q}>>B_{q-1}[1].
\end{CD}
$$

For total degree $n$, define

$$
\begin{aligned}
D_A^{q,n}&=\mathcal H^n(A_q),&
\mathcal E_A^{p,q}&=\mathcal H^{p+q}(G_q)
=g^{-1}R^pf_*\mathcal H^q(K),\\
D_B^{q,n}&=\mathcal H^n(B_q),&
\mathcal E_B^{p,q}&=\mathcal H^{p+q}(H_q)
=R^pf'_*g'^{-1}\mathcal H^q(K).
\end{aligned}
$$

The exact-couple differential is

$$
d_1=(j_{q-1})_*\circ(k_q)_*:
\mathcal E_A^{p,q}\longrightarrow\mathcal E_A^{p+2,q-1},
$$

and likewise $d'_1=(j'_{q-1})_*(k'_q)_*$. This first
exact-couple page is the page conventionally denoted $E_2$ in the
hypercohomology indexing.

## Detailed form

For $q\geq a$, apply $g^{-1}Rf_*$ and $Rf'_*g'^{-1}$ to the truncation
triangle

$$
 \tau_{\leq q-1}K\to\tau_{\leq q}K
 \to\mathcal H^q(K)[-q]\to.
$$

The exchange morphisms [def-weil-pbc-derived-exchange] on its three terms give
a morphism between the resulting exact couples. Its first graded component in
bidegree $(p,q)$ is

$$
 g^{-1}R^pf_*\mathcal H^q(K)\longrightarrow
 R^pf'_*g'^{-1}\mathcal H^q(K).
$$
