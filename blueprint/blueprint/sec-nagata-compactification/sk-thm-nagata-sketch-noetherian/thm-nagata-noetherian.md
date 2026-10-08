+++
id = "thm-nagata-noetherian"
kind = "theorem"
title = "Nagata compactification over a Noetherian base"
order = 325
lean = ["AlgebraicGeometry.nagataCompactification_of_isNoetherian"]
uses = ["def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-dense-affine-cover", "def-nagata-noetherian-compactification", "def-nagata-partial-affine-unions", "lemma-nagata-dense-affine-cover"]
+++
The recursively constructed factorization
$\mathsf C_{\mathrm{Noeth}}(X/S)$ is a compactification of $X\to S$.
Consequently $X\to S$ is compactifiable.

## Proof

The final component $h_n$ of the dependent recursive datum in
[def-nagata-noetherian-compactification] has the three fields required
by [def-nagata-compactification], and $X_n=X$. Thus
$\mathsf C_{\mathrm{Noeth}}(X/S)$ is a compactification of $X\to S$. No
later induction theorem is used to define any earlier $\mathsf C_r$.
