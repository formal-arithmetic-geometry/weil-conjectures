+++
id = "lem-exc-constant-inverse-image-flat"
kind = "lemma"
title = "Constant-coefficient inverse image preserves flat sheaves"
order = 1830
uses = ["def-weil-derived-tensor", "def-weil-pbc-proetale-operations", "def-weil-pbc-site-comparison-morphism", "prop-weil-pbc-site-comparison-finite-level"]
+++
For a finite commutative coefficient ring $A$, the
site inverse
image $\nu_T^*$ takes flat etale $A$-module sheaves
to flat pro-etale $A$-module sheaves. Flat means that
the ordinary tensor
product with the sheaf preserves injections of module sheaves.

## Proof

By [prop-weil-pbc-site-comparison-finite-level], inverse
image is exact and takes constant modules and constant
coefficient matrices to the same constants. We use the
finite-relation criterion for flatness, interpreted locally
for module sheaves. For completeness, a relation is a
finite tuple $(m_1,\ldots,m_r)$ with
$\sum a_im_i=0$. Flatness means that locally this tuple
is a sum $\sum_j b_jn_j$, with
$b_j\in\ker(A^r\xrightarrow{(a_i)}A)$.
The criterion is the ordinary equational criterion for
flat modules; for sheaves its proof is the same local
calculation: tensor elements use finitely many sections,
and equality in a sheafified tensor product is locally
a finite relation. Thus this criterion tests the tensor
injections in [def-weil-derived-tensor].

Locally all the coefficients $a_i$ are constant.
Since $A$ is Noetherian, choose a finite generating set
of the kernel of this row matrix, and write it as the
columns of a matrix $B:A^s\to A^r$. The relation
criterion for a flat sheaf $F$ says exactly that

$$
\operatorname{im}(B:F^s\to F^r)
=\ker((a_i):F^r\to F).
$$

Exact inverse image preserves this equality of images
and kernels and preserves the finite sums. The identical
matrix equation therefore holds for $\nu_T^*F$.
It holds for every row and for locally constant coefficients,
so the same relation criterion proves flatness on the
whole pro-etale site. This proof does not test flatness
only at ordinary geometric points.
