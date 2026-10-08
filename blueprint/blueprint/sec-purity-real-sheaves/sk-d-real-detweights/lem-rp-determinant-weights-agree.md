+++
id = "lem-rp-determinant-weights-agree"
kind = "lemma"
title = "Rank-one purity discharges the finite-determinant hypotheses"
order = 2635
uses = ["cor-wf-rank-one-punctual-purity-curve", "d-weights", "def-mg-determinant-line", "def-wf-determinantal-weight", "lem-wf-determinantal-weight-exists", "thm-wf-rank-one-finite-geometric-image-curve"]
+++
Let $X_0$ be a normal geometrically connected curve over $k_0$, put
$|k_0|=q$, fix $\iota:\Qlb\xrightarrow{\sim}\mathbf C$, and let
$\lambda_\iota(a)=2\log|\iota(a)|/\log q$ be the real weight character
of [d-weights]. Every nonzero lisse Weil sheaf $\mathcal Q$ on $X_0$
has finite geometric determinant in the sense of [d-weights]. If
$\mathcal Q$ is irreducible, then

$$
\dw_\iota(\mathcal Q)=\dw_{\lambda_\iota}(\mathcal Q),
$$

the left side as in [def-wf-determinantal-weight] and the right side as
in [d-weights].

## Proof

A continuous $\Qlb$-representation of $W(X_0)$ is defined over a finite
extension $E$ of $\mathbf Q_\ell$, and so are its irreducible
subquotients after enlarging $E$. Hence the determinant line
$\det\mathcal Q$ of [def-mg-determinant-line] is given by a continuous
character $\chi_{\det}=\det\circ\rho_{\mathcal Q}:W(X_0)\to E^\times$
with $E/\mathbf Q_\ell$ finite. The finite geometric image theorem
[thm-wf-rank-one-finite-geometric-image-curve], applied to the normal
geometrically connected curve $X_0$ and to $\chi_{\det}$, says that
$\chi_{\det}(\pi_1(X))$ is finite; this is finite geometric determinant.

Let $r$ be the rank of $\mathcal Q$ and $s$ a degree-one element. By
[cor-wf-rank-one-punctual-purity-curve], $\det\mathcal Q$ is punctually
$\iota$-pure of weight

$$
2\log_q|\iota(\chi_{\det}(s))|=\lambda_\iota(\det\rho_{\mathcal Q}(s)).
$$

If $\mathcal Q$ is irreducible, the uniqueness in
[lem-wf-determinantal-weight-exists] identifies this number with the
weight $a$ used in [def-wf-determinantal-weight], so

$$
\dw_\iota(\mathcal Q)=\frac{a}{r}
=\frac{\lambda_\iota(\det\rho_{\mathcal Q}(s))}{r}
=\dw_{\lambda_\iota}(\mathcal Q).
$$
