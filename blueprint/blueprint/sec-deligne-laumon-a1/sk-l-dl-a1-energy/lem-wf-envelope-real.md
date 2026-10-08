+++
id = "lem-wf-envelope-real"
kind = "lemma"
title = "The envelope is real"
order = 2765
uses = ["def-weil-punctual-weights", "def-wf-iota-real", "def-wf-normalized-real-envelope"]
+++
The envelope $\operatorname{Env}_\iota(\mathcal F;b)$ of
[def-wf-normalized-real-envelope] is $\iota$-real in the sense of
[def-wf-iota-real].

## Proof

At a closed point $y$, the local characteristic factor of the
envelope is the product of the local factors of the two summands, with
eigenvalues $\beta_j$ (of $\mathcal F^0_{\bar y}$) and
$\beta_j^{-1}$ (of its dual), where
$|\iota(\beta_j)|=q_y^{0}=1$ by the normalization of
[def-wf-normalized-real-envelope] and the punctual purity of
weight $0$ of [def-weil-punctual-weights]. Hence

$$
\iota\bigl(\beta_j^{-1}\bigr)=\overline{\iota(\beta_j)}
$$

($\overline z=|z|^2z^{-1}=z^{-1}$ for $|z|=1$), so the local
eigenvalue multiset is stable under complex conjugation; by
[def-wf-iota-real] the envelope is $\iota$-real.
