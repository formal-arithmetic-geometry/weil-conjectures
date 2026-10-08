+++
id = "lem-fd-realness-pushforward"
kind = "lemma"
title = "Reality survives the Fourier projection"
order = 2773
uses = ["cor-trf-point-counting", "def-fd-transform", "def-weil-constructible-heart", "def-wf-iota-real", "prop-weil-pbc-strict-henselization-stalk-formula", "thm-trf-grothendieck-lefschetz-qbar"]
+++
Let $k_0=\mathbf F_q$, let
$X_0=\mathbf A^1_{k_0}\times_{k_0}\mathbf A^1_{k_0}$ with second
projection $p_2:X_0\to\mathbf A^1_{k_0}$ of
[def-fd-transform], and let $\mathcal K$ be a
constructible Weil sheaf on
$X_0$ which is $\iota$-real in the sense of
[def-wf-iota-real]. Assume that

$$
R^\nu p_{2,!}\mathcal K=0\qquad(\nu\neq1).
$$

Then $R^{1}p_{2,!}\mathcal K$ is $\iota$-real.

## Proof

Step 1 (the traces on a fibre). Let $\xi\in|\mathbf A^1_{k_0}|$ be a
closed point with residue field $\kappa(\xi)=\mathbf F_{q^d}$, and let
$m\geq1$. The stalk of the higher direct image at $\bar\xi$ is the
compact-support cohomology of the fibre, by the strict-henselization
stalk formula for the compact-support direct image
[prop-weil-pbc-strict-henselization-stalk-formula]; by the
hypothesis, only degree one of $R\Gamma_c(X_{\bar\xi},\mathcal K)$ is
nonzero. The Grothendieck–Lefschetz trace formula
[thm-trf-grothendieck-lefschetz-qbar] in its point-counting form
[cor-trf-point-counting], applied over the residue field
$\kappa(\xi)$ to the fibre, therefore gives

$$
-\operatorname{Tr}\bigl(F_\xi^m\mid(R^{1}p_{2,!}\mathcal K)_{\bar\xi}\bigr)
=\sum_{x\in X_\xi(\mathbf F_{q^{dm}})}\operatorname{Tr}\bigl(F_x^m\mid\mathcal K_{\bar x}\bigr),
$$

the right-hand side being the sum of the local traces over the
$\mathbf F_{q^{dm}}$-points of the fibre of the closed point $\xi$: only
the surviving degree contributes, and it contributes with the sign
$(-1)^1$.

Step 2 (each term is real). At every closed point $x\in|X_0|$, reality
of $\mathcal K$ means that the multiset $\{s_j\}$ of eigenvalues of $F_x$
on $\mathcal K_{\bar x}$ is stable under $\iota$-conjugation. For every
$m$ conjugation therefore permutes the multiset $\{s_j^m\}$ of $m$-th
powers, because $\overline{\iota(s_j^m)}=\overline{\iota(s_j)}^m$, and
the sum of a conjugation-stable multiset is conjugation-fixed,

$$
\overline{\iota\Bigl(\sum_j s_j^m\Bigr)}=\iota\Bigl(\sum_j s_j^m\Bigr):
$$

the local trace $\operatorname{Tr}(F_x^m\mid\mathcal K_{\bar x})$ is
$\iota$-real. Every term on the right-hand side of Step 1 is real, and
so is the trace on the left, the sign being immaterial.

Step 3 (real traces give a real factor). Write

$$
P_\xi(T):=\det\bigl(1-TF_\xi\mid(R^{1}p_{2,!}\mathcal K)_{\bar\xi}\bigr)
=\sum_{r=0}^{\rho}(-1)^re_r(\xi)T^r .
$$

By Newton's identities the elementary symmetric functions $e_r$ are
polynomials with rational coefficients in the power sums
$\operatorname{Tr}(F_\xi^m\mid(R^{1}p_{2,!}\mathcal K)_{\bar\xi})$,
$1\leq m\leq r$; since $\iota$ is a field isomorphism which is the
identity on $\mathbf Q$, the $\iota$-image of each $e_r(\xi)$ is the same
polynomial evaluated at the $\iota$-images of those power sums, which are
real by Step 2. Hence $\iota(P_\xi)\in\mathbf R[T]$ for every closed
point $\xi$, which is the $\iota$-reality of
$R^{1}p_{2,!}\mathcal K$ in the sense of [def-wf-iota-real].
