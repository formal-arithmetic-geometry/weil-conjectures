+++
id = "lem-rp-upper-bound"
kind = "lemma"
title = "Upper bound via the largest determinant weight"
order = 2664
uses = ["cor-mg-det-weight-finite-tensor", "cor-rp-euler-product", "d-real-cohom", "def-mg-determinantal-weight-multiset", "def-mg-weil-composition-series", "def-mg-weil-semisimplification", "def-real-weil-representation-operations", "def-wf-determinantal-weight", "def-wf-iota-real", "def-wf-weil-category", "lem-mg-normal-restriction-semisimple", "lem-mg-semisimplification-independent", "lem-rp-even-tensor-positivity", "lem-rp-hc2-eigenvalue-determinant-weight", "lem-rp-positive-product-radius", "p-linear-filtration", "p-linear-spectra"]
+++
Let $U_0$ be a smooth geometrically connected affine curve, let
$U=U_0\times_{k_0}k$, let $\mathcal G_0$ be a lisse
Weil sheaf on $U_0$ which is
$\iota$-real, and let $\beta$ be the
maximum of the determinant weights of $\mathcal G_0$ (for the fixed
$\iota$). Then for every closed point $x\in|U_0|$ and every
eigenvalue $\alpha$ of the local Frobenius $F_x$ on
$\mathcal G_{0,\bar x}$,

$$
|\iota(\alpha)|^2\le q_x^{\beta}.
$$

## Proof

If $\mathcal G_0=0$ there is nothing to prove, so assume it is
nonzero. Choose a composition series as in
[def-mg-weil-composition-series]. At every closed point, local
Frobenius is block upper triangular in a basis adapted to that series,
so its characteristic polynomial is the product ([p-linear-filtration]) of those of the
successive quotients. Therefore replacing $\mathcal G_0$ by the
direct sum of those quotients, its Weil semisimplification in
[def-mg-weil-semisimplification], leaves all local characteristic
polynomials, hence $\iota$-reality in
[def-wf-iota-real], unchanged. It also leaves the
determinant-weight multiset unchanged, by its definition in
[def-mg-determinantal-weight-multiset] together with
[lem-mg-semisimplification-independent].
We make this replacement and keep the same notation. The resulting
representation is geometrically semisimple by
[lem-mg-normal-restriction-semisimple].

Fix $k\ge1$ and put
$\mathcal G^{(2k)}_0:=\mathcal G_0^{\otimes 2k}$, the tensor power of
[def-real-weil-representation-operations]. By
[cor-mg-det-weight-finite-tensor], whose geometric-semisimplicity
hypothesis has just been verified, the largest determinant weight of
$\mathcal G^{(2k)}_0$ is $2k\beta$.
Step 1 (the $H_c^2$-factor). If $\lambda$ is an eigenvalue of the
global Frobenius $F$ on $H_c^2(U,\mathcal G^{(2k)})$, then
[lem-rp-hc2-eigenvalue-determinant-weight] gives a determinant weight

$$
\frac{\log\bigl(|\iota(\lambda q^{-1})|^2\bigr)}{\log(q)}
$$

of $\mathcal G^{(2k)}_0$. It is therefore at most $2k\beta$, and

$$
|\iota(\lambda)|^2\le q^{2k\beta+2}.
$$

Consequently every zero of the coefficientwise complex polynomial
$\iota\det(1-Ft,H_c^2(U,\mathcal G^{(2k)}))$ has modulus at least

$$
R_k:=q^{-k\beta-1}.
$$

Step 2 (formal Euler product and local zero-freeness). Apply
[cor-rp-euler-product] to $\mathcal G^{(2k)}_0$ and then apply
$\iota$ coefficientwise. The resulting formal series is

$$
\prod_{x\in|U_0|} f_x(t),\qquad
f_x(t):=\iota\det(1-F_xt^{d(x)},\mathcal G^{(2k)}_{0,\bar x})^{-1}.
$$

The family is locally finite in each coefficient because only finitely many
closed points have a fixed degree [d-real-cohom]. By
[lem-rp-even-tensor-positivity], every $f_x$ lies in
$1+t\mathbf R_{\ge0}[[t]]$. The Euler identity identifies the formal
product with the Taylor series at $0$ of the rational function

$$
\frac{\iota\det(1-Ft,H_c^1(U,\mathcal G^{(2k)}))}
{\iota\det(1-Ft,H_c^2(U,\mathcal G^{(2k)}))}.
$$

Step 1 shows that this function is holomorphic on $|t|<R_k$. Hence
[lem-rp-positive-product-radius] applies and says that every local
polynomial
$\iota\det(1-F_xt^{d(x)},\mathcal G^{(2k)}_{0,\bar x})$ is zero-free
on that disc.

Step 3 (the estimate). Let $\alpha$ be an eigenvalue of $F_x$ on
$\mathcal G_{0,\bar x}$. Then by [p-linear-spectra] $\alpha^{2k}$ is an eigenvalue of the
$2k$-fold tensor Frobenius, so
$t^{d(x)}\iota(\alpha)^{2k}=1$ has a root of modulus
$|\iota(\alpha)|^{-2k/d(x)}$. The local zero-freeness from Step 2 gives

$$
|\iota(\alpha)|^{-2k/d(x)}\ge R_k=q^{-k\beta-1},
$$

and therefore

$$
|\iota(\alpha)|^2\le q^{d(x)(2k\beta+2)/(2k)}
=q_x^{\beta+1/k}.
$$

Letting $k\to\infty$ proves
$|\iota(\alpha)|^2\le q_x^\beta$.
