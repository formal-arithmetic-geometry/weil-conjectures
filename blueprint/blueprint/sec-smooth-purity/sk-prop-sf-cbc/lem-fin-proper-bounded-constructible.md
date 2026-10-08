+++
id = "lem-fin-proper-bounded-constructible"
kind = "lemma"
title = "Bounded constructible complexes under a proper direct image"
order = 1624
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-derived-categories", "def-weil-pbc-direct-image", "def-weil-pbc-scheme-conventions", "sbc-def-coefficient-conventions", "thm-constructible-serre", "thm-fin-proper-case", "thm-sp-truncation-e2"]
+++
Let $b:Y\to S$ be proper
between finite-type $k$-schemes, with the finite coefficients of
[sbc-def-coefficient-conventions].
For an ordinary derived
complex $K\in\hyperref[def-weil-pbc-constructible-complexes]{D^b_c(Y,\Lambda)}$,
its derived direct image
$Rb_*K$ belongs to $D^b_c(S,\Lambda)$.

## Proof

Choose $[a,c]$ containing the cohomological support of $K$,
and choose $d$ bounding the dimensions of the geometric fibres
of $b$. Such a $d$ exists for a finite-type morphism: a finite
affine cover of source and target gives finite lists of algebra
generators, bounding the fibre dimensions.
The hypercohomology sequence of [thm-sp-truncation-e2] is

$$
E_2^{p,q}=R^pb_*\mathcal H^q(K)\Longrightarrow
\mathcal H^{p+q}(Rb_*K).
$$

By [thm-fin-proper-case], its terms are constructible and zero
unless $0\leq p\leq2d$ and $a\leq q\leq c$.
Every page is constructible by kernels and cokernels in
[thm-constructible-serre].
The bounded rectangle gives convergence with a finite filtration
on every abutment. Extensions prove constructibility, and the
same rectangle makes the abutment zero outside $[a,c+2d]$.
