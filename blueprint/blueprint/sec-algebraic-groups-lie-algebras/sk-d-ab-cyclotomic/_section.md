+++
id = "sk-d-ab-cyclotomic"
kind = "section"
title = "The cyclotomic Tate module"
order = 2565
uses = ["sk-d-ab-field", "sk-d-ab-tate"]
lean = ["cyclotomicTateModule"]
+++
*Definition (sketch).*

The multiplicative group scheme $\mathbf G_m$ has
$\mathbf G_m(R)=R^\times$ for each commutative
$k_0$-algebra $R$.
Write $\mu_{\ell^n}(\bar k)=\{u\in\bar k^\times:u^{\ell^n}=1\}$ and set

$$
\begin{aligned}
\Zell(1)&=\{(u_n)_{n\ge1}:u_n\in\mu_{\ell^n}(\bar k),\,
u_{n+1}^{\ell}=u_n\},\\
\Qell(1)&=\Zell(1)[1/\ell].
\end{aligned}
$$

These are the Tate constructions for the abelian
group $\bar k^\times$, written multiplicatively: addition is coordinatewise
multiplication, and multiplication by $c\in\Zell$ sends $u_n$ to
$u_n^{c_n}$. Galois acts on every coordinate.
def:ab-multiplicative;def:ab-cyclotomic;lem:ab-cyclotomic-module

Uses: [sk-d-ab-field], [sk-d-ab-tate]
