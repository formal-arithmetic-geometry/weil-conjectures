+++
id = "thm-rp-real-lisse-purity-affine"
kind = "theorem"
title = "Purity of real lisse sheaves on curves"
order = 2667
uses = ["cor-mg-det-weight-exterior", "d-real-setup", "def-real-weil-representation-operations", "def-rp-weight-blocks", "def-weil-punctual-weights", "def-wf-determinantal-weight", "def-wf-iota-real", "def-wf-weil-category", "lem-mg-exterior-direct-sum", "lem-mg-normal-restriction-semisimple", "lem-rp-exterior-reality", "lem-rp-upper-bound", "lem-tw-dual-negation", "lem-wf-dense-open-pi1-surjective", "lem-wf-determinantal-weight-exists", "lem-wf-real-semisimplification", "p-linear-spectra"]
+++
Let $C_0/\mathbf F_q$ be a smooth geometrically connected curve in the
sense of [d-real-setup] (not necessarily affine; e.g. proper) and let
$\mathcal G_0$ be a lisse
Weil sheaf on $C_0$ which is
$\iota$-real. Then every irreducible
constituent $\mathcal W$ of $\mathcal G_0$ (in the sense of
[def-real-weil-representation-operations]) is
punctually $\iota$-pure of
weight $\dw_\iota(\mathcal W)$, its
determinant weight with
respect to $\iota$.

## Proof

Step 0 (reduction to an affine curve). Punctual purity is a condition
at each closed point separately ([def-weil-punctual-weights]), so fix a
closed point $x$ of $C_0$ and an irreducible constituent $\mathcal W$
of $\mathcal G_0$, of rank $r$. Choose an affine open
$U_0\subseteq C_0$ containing $x$ (every point of a scheme has one). It
is again a smooth geometrically connected curve: $U=U_0\times_{\mathbf F_q}k$
is a nonempty open of the smooth connected, hence irreducible, curve
$C=C_0\times_{\mathbf F_q}k$, so it is connected. Let
$u:U_0\hookrightarrow C_0$ be the inclusion.

(a) *Reality.* $\iota$-reality in the sense of [def-wf-iota-real] is a
condition on the local characteristic polynomials at the closed points,
so $u^*\mathcal G_0$ is an $\iota$-real lisse Weil sheaf on $U_0$.

(b) *Constituents.* Restriction $u^*$ is exact, and by
[lem-wf-dense-open-pi1-surjective] (4) it carries irreducible lisse
Weil sheaves on $C_0$ to irreducible ones on $U_0$. Hence it carries a
composition series of $\mathcal G_0$ through which $\mathcal W$ occurs
as a successive quotient to a composition series of $u^*\mathcal G_0$,
and $u^*\mathcal W$ is an irreducible constituent of
$u^*\mathcal G_0$.

(c) *Determinant weight.* $\det(u^*\mathcal W)=u^*\det(\mathcal W)$,
and $\det(\mathcal W)$ is punctually $\iota$-pure of weight $a$ with
$\dw_\iota(\mathcal W)=a/r$ by [lem-wf-determinantal-weight-exists] and
[def-wf-determinantal-weight]; its restriction is punctually pure of the
same weight $a$ at the closed points of $U_0$, so by the uniqueness in
[lem-wf-determinantal-weight-exists] on $U_0$ we get
$\dw_\iota(u^*\mathcal W)=a/r=\dw_\iota(\mathcal W)$.

The local Frobenius $F_x$ on $\mathcal W_{\bar x}$ is the same as on
$(u^*\mathcal W)_{\bar x}$. Therefore it suffices to prove the theorem
for the smooth geometrically connected affine curve $U_0$ and the
$\iota$-real lisse sheaf $u^*\mathcal G_0$: its conclusion at $x$ for
the constituent $u^*\mathcal W$ is the required purity of
$\mathcal W$ of weight $\dw_\iota(\mathcal W)$ at $x$. In Steps 1–4 we
thus assume that $C_0=U_0$ is affine, and write $\mathcal G_0$ for the
sheaf on $U_0$.

Step 1 (reduction to the semisimple case). Replacing
$\mathcal G_0$ by its semisimplification does not change the local
characteristic polynomials (by the Brauer–Nesbitt argument of
[lem-wf-real-semisimplification]), hence changes neither
$\iota$-reality in the sense of [def-wf-iota-real] nor the
determinant weights of $\mathcal G_0$. The resulting semisimple Weil
representation is geometrically semisimple by
[lem-mg-normal-restriction-semisimple]. We therefore assume that
$\mathcal G_0$ is semisimple, with distinct
determinant weights

$$
\gamma_1>\gamma_2>\cdots>\gamma_r,
$$

and write $\mathcal G_0=\bigoplus_{i=1}^{r}\mathcal G_0(i)$ where
$\mathcal G_0(i)$ is the direct sum of the irreducible constituents
of determinant weight $\gamma_i$, of total rank $r(i)$; note
$\sum_i r(i)=\operatorname{rank}\mathcal G_0$. In the notation of
[def-rp-weight-blocks], $\mathcal G_0(i)=\mathcal G_0(\gamma_i)$ is the
weight block of weight $\gamma_i$, so this decomposition does not
depend on the choice of decomposition into irreducible summands.
Step 2 (the global upper and lower bounds). Applying
[lem-rp-upper-bound] to $\mathcal G_0$ (of largest determinant
weight $\gamma_1$) gives, at every closed point $x$ and every
eigenvalue $\alpha$ of $F_x$ on $\mathcal G_{0,\bar x}$,

$$
|\iota(\alpha)|^2\le q_x^{\gamma_1}.
$$

The dual sheaf $\mathcal G_0^\vee$ is also $\iota$-real (its local
eigenvalue multiset is the inverse ([p-linear-spectra]) of the conjugation-stable multiset
of $\mathcal G_0$), has determinant weights $-\gamma_i$ (the
determinant of the dual of a constituent is the dual of its
determinant, of weight $-r\gamma_i$ by
[lem-tw-dual-negation]; the constituents of the dual are the
duals of the constituents), hence largest determinant weight
$-\gamma_r$, and the upper bound of [lem-rp-upper-bound]
applied to $\mathcal G_0^\vee$ gives

$$
|\iota(\alpha^{-1})|^2\le q_x^{-\gamma_r}
\qquad\text{hence}\qquad
|\iota(\alpha)|^2\ge q_x^{\gamma_r}
$$

for every eigenvalue $\alpha$ of $F_x$ on
$\mathcal G_{0,\bar x}$.
Step 3 (the estimates for each isotypic part). Fix $n\ge0$ with
$r(n+1)>0$ (writing $r(i)=0$ for $i>r$). Put

$$
N:=\sum_{i=1}^{n}r(i),\qquad
\mathcal T_0:=\bigwedge\nolimits^{N+1}\mathcal G_0.
$$

In the notation of [def-rp-weight-blocks], $N=N_{\gamma_{n+1}}$ and
$\sum_{i\le n}r(i)\gamma_i=B_{\gamma_{n+1}}$.

By [cor-mg-det-weight-exterior] the determinant weights of
$\mathcal T_0$ are the sums $\sum_{i}n_i\gamma_i$ with
$0\le n_i\le r(i)$ and $\sum_in_i=N+1$, and the maximum of these
is

$$
\gamma_{n+1}+\sum_{i=1}^{n}r(i)\gamma_i,
$$

attained exactly at $n_i=r(i)$ for $i\le n$ and $n_{n+1}=1$;
any other tuple either omits some rank at $i\le n+1$ or uses an
index $i>n+1$, and the weights are strictly decreasing, so the value
is strictly smaller. The sheaf $\mathcal T_0$ is $\iota$-real by
[lem-rp-exterior-reality], so
[lem-rp-upper-bound] applied to it gives, at every closed point
$x$ and every eigenvalue $\lambda$ of $F_x$ on
$\mathcal T_{0,\bar x}$,

$$
|\iota(\lambda)|^2\le
q_x^{\gamma_{n+1}+\sum_{i\le n}r(i)\gamma_i}.
$$

Take the particular eigenvalue

$$
\lambda=\alpha^{(n+1)}_j\cdot
\prod_{i=1}^{n}\prod_{j=1}^{r(i)}\alpha^{(i)}_j,
$$

where the $\alpha^{(i)}_j$ are the eigenvalues (with multiplicity)
of $F_x$ on $\mathcal G_0(i)_{\bar x}$ and
$\alpha^{(n+1)}_j$ is any eigenvalue of $F_x$ on
$\mathcal G_0(n+1)_{\bar x}$: for the admissible tuple
$n_i=r(i)$ ($i\le n$), $n_{n+1}=1$ the corresponding summand of
the direct-sum decomposition of
[lem-mg-exterior-direct-sum], together with
[cor-mg-det-weight-exterior], contains the summand

$$
\mathcal L:=\bigl(\det\mathcal G_0(1)\otimes\cdots\otimes
\det\mathcal G_0(n)\bigr)\otimes\mathcal G_0(n+1),
$$

since the exterior power in maximal degree of a module is its
determinant line; this nonzero summand carries the displayed
eigenvalue $F_x$. Hence

$$
|\iota(\alpha^{(n+1)}_j)|^2
\cdot q_x^{\sum_{i\le n}r(i)\gamma_i}
\le q_x^{\gamma_{n+1}+\sum_{i\le n}r(i)\gamma_i},
$$

because for each $i\le n$ the product

$$
\prod_{j=1}^{r(i)}|\iota(\alpha^{(i)}_j)|^2=q_x^{r(i)\gamma_i}
$$

is the eigenvalue of the local Frobenius on the determinant line of
the isotypic part $\mathcal G_0(i)$, hence of weight
$r(i)\gamma_i$ (by [lem-wf-determinantal-weight-exists] and
[def-wf-determinantal-weight]: the
determinant of an irreducible constituent of weight $\gamma$ is a
rank-one sheaf of weight $r\gamma$, and the determinants of the
constituents tensor up to the determinant of the isotypic part, whose
weights add). Since this holds for every closed point $x$ and
every $j$,

$$
|\iota(\alpha)|^2\le q_x^{\gamma_{n+1}}
$$

for every eigenvalue $\alpha$ of $F_x$ on
$\mathcal G_0(n+1)_{\bar x}$. For the lower bound, apply the same
argument to the dual sheaf $\mathcal G_0^\vee$, whose distinct
determinant weights in decreasing order are
$-\gamma_r>\cdots>-\gamma_1$ and whose isotypic part of weight
$-\gamma_i$ is the dual of $\mathcal G_0(i)$, at the block which is
the dual of $\mathcal G_0(n+1)$ (the $(r-n)$-th block of the dual,
of weight $-\gamma_{n+1}$): the same computation, with
$N^\vee:=\sum_{j=n+2}^{r}r(j)$ and the isotypic parts of the
dual of weights $-\gamma_r,\ldots,-\gamma_{n+2}$, whose determinant
lines have weights $r(j)(-\gamma_j)$ by
[def-wf-determinantal-weight], gives

$$
|\iota(\alpha^{-1})|^2\le q_x^{-\gamma_{n+1}},
\qquad\text{i.e.}\qquad
|\iota(\alpha)|^2\ge q_x^{\gamma_{n+1}}.
$$

So every eigenvalue satisfies
$|\iota(\alpha)|=q_x^{\gamma_{n+1}/2}$, which is the punctual
purity of weight $\gamma_{n+1}$ of
[def-weil-punctual-weights] for the constituents of
$\mathcal G_0(n+1)$.
Step 4 (conclusion). The estimate of Step 3 applies to every $n$
with $r(n+1)>0$, so every isotypic part $\mathcal G_0(i)$ — and
hence every irreducible constituent $\mathcal W$ of
$\mathcal G_0$ — is punctually $\iota$-pure of weight
$\dw_\iota(\mathcal W)=\gamma_i$, as asserted.
