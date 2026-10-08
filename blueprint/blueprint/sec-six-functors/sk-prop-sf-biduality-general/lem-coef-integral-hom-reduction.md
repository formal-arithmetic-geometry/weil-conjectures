+++
id = "lem-coef-integral-hom-reduction"
kind = "lemma"
title = "Integral internal Hom and reduction"
order = 2134
uses = ["def-weil-completed-integral-coefficients", "def-weil-derived-complete", "def-weil-derived-pullback-tensor-hom"]
+++
For arbitrary ambient complexes $K,L$ of $R_X$-modules,
the canonical evaluation-defined comparison is an isomorphism

$$
R\mathcal Hom_R(K,L)\otimes_R^L A_n
\xrightarrow{\sim}R\mathcal Hom_{A_n}(K_n,L_n).
$$

It preserves evaluation and its transposes. If $L$ is derived
complete, then $R\mathcal Hom_R(K,L)$ is derived complete.
No site-perfectness assumption on $K$ is imposed.

## Proof

The complex $[R_X\xrightarrow{\pi^n}R_X]$ is a finite-free
resolution of $A_n$. Applying the exact $R$-linear functor
$R\mathcal Hom_R(K,-)$ to this two-term coefficient construction
gives

$$
R\mathcal Hom_R(K,L)\otimes_R^L A_n
\cong R\mathcal Hom_R(K,L\otimes_R^L A_n).
$$

The extension–restriction adjunction for the coefficient sheaves of
[def-weil-completed-integral-coefficients] identifies the latter
with
$\operatorname{Res}_nR\mathcal Hom_{A_n}(K_n,L_n)$.
Indeed, testing on a complex on each slice of the site reduces this
identity to the derived tensor–Hom adjunction of
[def-weil-derived-pullback-tensor-hom]. The resulting map is
$A_n$-linear and is precisely the canonical comparison in the
statement. The finite-free construction and this adjunction use the
actual evaluation maps, which proves their compatibility as well.

If $L$ is complete, write $L=R\varprojlim_n\operatorname{Res}_nL_n$.
Internal Hom preserves derived limits in its second variable, since
it is right adjoint to derived tensor. Consequently

$$
R\mathcal Hom_R(K,L)
\cong R\varprojlim_n\operatorname{Res}_n
R\mathcal Hom_{A_n}(K_n,L_n).
$$

The preceding comparison identifies this with its own quotient
completion, giving [def-weil-derived-complete].
This proof uses perfectness of $A_n$ over $R$, not
perfectness of $A_n$ over a larger finite quotient ring.
