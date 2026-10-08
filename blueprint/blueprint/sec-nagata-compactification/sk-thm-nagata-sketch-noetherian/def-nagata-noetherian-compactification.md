+++
id = "def-nagata-noetherian-compactification"
kind = "definition"
title = "Recursive Noetherian compactification construction"
order = 324
lean = ["AlgebraicGeometry.noetherianCompactificationConstruction"]
uses = ["def-nagata-affine-compactification", "def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-dense-affine-cover", "def-nagata-partial-affine-unions", "def-nagata-two-open-compactification-candidate", "lemma-nagata-affine-finite-type-is-quasi-affine", "lemma-nagata-final-density", "lemma-nagata-partial-union-overlap-dense", "lemma-nagata-two-open-candidate-proper", "lemma-nagata-two-open-valuative-lifting", "prop-nagata-affine-compactification", "thm-nagata-two-open"]
+++
Let $S$ be Noetherian and let $X\to S$ be separated and of finite type.
Then $X$ is Noetherian, hence qcqs, and the finite generic-point argument
supplies the selected dense affine cover
$\mathcal U_X=(U_1,\ldots,U_n)$ from
[def-nagata-dense-affine-cover]. Define pairs $(\mathsf C_r,h_r)$
recursively along the partial unions of
[def-nagata-partial-affine-unions], where $h_r$ is an explicit proof
that $\mathsf C_r$ is a compactification of $X_r\to S$. Since
$X_0=\emptyset$, the morphism $X_0\to S$ is proper, so set

$$
(\mathsf C_0,h_0)
=\bigl(\emptyset\hookrightarrow\emptyset\to S,
\text{the witness that a proper morphism compactifies itself}\bigr).
$$

Given $(\mathsf C_{r-1},h_{r-1})$, the next stage is $X_r=X_{r-1}\cup U_r$.
If $r>n$ there is nothing to add and $X_r=X_{r-1}$. If $r=1$ then
$X_1=U_1$ is affine and
[prop-nagata-affine-compactification] supplies $(\mathsf C_1,h_1)$.
Otherwise apply [thm-nagata-two-open] to the open cover
$X_r=X_{r-1}\cup U_r$, using $h_{r-1}$, the affine compactification witness
for $U_r$ from [prop-nagata-affine-compactification], and the dense
overlap from [lemma-nagata-partial-union-overlap-dense]. Choose the
resulting candidate and its compactification proof as
$(\mathsf C_r,h_r)$, and finally define

$$
\mathsf C_{\mathrm{Noeth}}(X/S)=\mathsf C_n,
\qquad h_{\mathrm{Noeth}}=h_n.
$$

The recursive datum is therefore a dependent finite sequence of pairs, not
an unproved sequence of candidates. At every stage also record that
$X_r\to S$ is separated and of finite type, as follows by restricting the
corresponding properties of $X\to S$ to the open $X_r\subseteq X$; these
are the hypotheses used at the next application of the two-open theorem.
