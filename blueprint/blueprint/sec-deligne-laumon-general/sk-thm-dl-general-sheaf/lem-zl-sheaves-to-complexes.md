+++
id = "lem-zl-sheaves-to-complexes"
kind = "lemma"
title = "Passage from sheaves to complexes"
order = 2846
uses = ["def-weil-complex-weights", "def-weil-pbc-hypercohomology-filtrations", "def-weil-pbc-qbar-category", "def-weil-punctual-weights", "lem-a1-extension-bounds", "lem-a1-subquotient-extension-bounds", "lemma-weil-pbc-hypercohomology-convergence", "prop-functor-package"]
+++
Suppose that, for a separated finite-type map $f:X_0\to Y_0$, every
mixed Weil sheaf $\mathcal F$ of weights at most $v$ has
$R^af_!\mathcal F$ mixed of weights at most $v+a$, for every $a$.
Then $Rf_!$ carries $D_{\le w}(X_0)$ into $D_{\le w}(Y_0)$.

## Proof

Apply the hypercohomology spectral sequence provided by the truncation
construction of [def-weil-pbc-hypercohomology-filtrations] and the
exact triangulated functor $Rf_!$ of [prop-functor-package]:

$$
E_2^{a,b}=R^af_!\bigl(\mathcal H^b(K)\bigr)
\quad\Longrightarrow\quad \mathcal H^{a+b}\bigl(Rf_!K\bigr),
$$

with the finite image filtration of
[lemma-weil-pbc-hypercohomology-convergence]. By
[def-weil-complex-weights], each $\mathcal H^b(K)$ is
$\iota$-mixed of weights at most $w+b$; by the hypothesis of the
lemma every $E_2^{a,b}$ is mixed of weights at most $w+a+b$. Every
later page $E_{r+1}^{a,b}$ is a subquotient of $E_r^{a,b}$, and the
abutment $\mathcal H^n(Rf_!K)$ is filtered with graded pieces
$E_\infty^{a,b}$, $a+b=n$; the subquotient and extension bounds of
[lem-a1-subquotient-extension-bounds], [lem-a1-extension-bounds]
(stalkwise, with the
punctual weight convention of
[def-weil-punctual-weights]) show that $\mathcal H^n(Rf_!K)$ is
$\iota$-mixed of weights at most $w+n$, i.e. $Rf_!K\in D_{\le w}(Y_0)$
by [def-weil-complex-weights].
