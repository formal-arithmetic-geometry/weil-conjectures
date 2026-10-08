+++
id = "lem-pur-kummer-coefficient-base-change"
kind = "lemma"
title = "Base change of the Kummer coefficients"
order = 1925
uses = ["def-coefficient-twists-detailed", "def-pur-conventions", "def-sbc-smooth-morphisms", "def-sc-curves", "def-weil-pbc-etale-sheaves", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-pur-finite-kummer-level"]
+++
Fix the finite-field datum of [def-pur-conventions], let $k$ be
algebraically closed, let $N\geq1$, and let $A$ be a finite
$\mathbf Z/\ell^N\mathbf Z$-module which is free of finite rank (for
instance $A=A_{E,n}$ with $N=n\cdot v_\ell(\varpi_E)$ under the
hypothesis $e(E/\Ql)\mid n$ of [lem-pur-finite-kummer-level]). For every
smooth separated curve $C$ over $k$ and every
integer $q\geq0$, the natural map

$$
H^q(C_{\Et},\mu_{\ell^N})\otimes_{\mathbf Z/\ell^N}A
\longrightarrow
H^q(C_{\Et},\mu_{\ell^N}\otimes_{\mathbf Z/\ell^N}A)
$$

is an isomorphism, compatibly with the Kummer boundary maps of the Kummer
sequence with $A$-coefficients.

## Proof

The sheaf $\mu_{\ell^N}$ is a finite locally constant
$\mathbf Z/\ell^N\mathbf Z$-module sheaf. Since $A$ is free of finite
rank over $\mathbf Z/\ell^N\mathbf Z$, the coefficient tensor
$\mu_{\ell^N}\otimes_{\mathbf Z/\ell^N}A$ is a finite direct sum of
copies of $\mu_{\ell^N}$; by [def-weil-pbc-etale-sheaves],
cohomology and the tensor product commute with finite direct sums, so the
displayed isomorphism is the assembly of the summand isomorphisms. Its compatibility with the Kummer boundary maps is
the naturality in the Kummer sequence: the exact sequence

$$
0\to\mu_{\ell^N}\otimes A\to\mathbf G_m\otimes A\to\mathbf G_m\otimes A\to0
$$

is the tensor of the Kummer sequence with the free module $A$.
