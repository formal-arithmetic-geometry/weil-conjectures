+++
id = "p-linear-spectra"
kind = "theorem"
title = "Spectra of the operations"
order = 2551
uses = ["d-weights", "p-linear-triangular"]
tags = ["latex:proposition"]
lean = ["LinearMap.charpoly_roots_tensorProduct", "LinearMap.charpoly_roots_exteriorPower", "LinearMap.charpoly_roots_dualMap_symm"]
+++
If $f$ has eigenvalue multiset
$\operatorname{eig}(f)=\{\alpha_1,\ldots,\alpha_r\}$ and $g$ has
$\{\beta_1,\ldots,\beta_t\}$, both with multiplicity, then

$$
\operatorname{eig}(f\otimes g)=\{\alpha_i\beta_j\},\quad
\operatorname{eig}\bigl(\textstyle\bigwedge^sf\bigr)
=\{\alpha_{i_1}\cdots\alpha_{i_s}:i_1<\cdots<i_s\},\quad
\operatorname{eig}(f^\vee)=\{\alpha_i^{-1}\}
$$

(the last for invertible $f$); in particular $\alpha^n$ is an eigenvalue of
$f^{\otimes n}$. Concretely, in an exterior basis a diagonal map with
entries $c_1,\ldots,c_r$ has entries $c_{i_1}\cdots c_{i_s}$ with
$i_1<\cdots<i_s$. Applied to $\rho_V(w)$ and $\rho_W(w)$, these compute the spectra of the
tensor, exterior-power and determinant representations of [d-weights].
lem:exterior-basis

## Proof

Use [p-linear-triangular] to pick bases in which $f$ and $g$ are
upper triangular, with diagonals $\alpha_1,\ldots,\alpha_r$ and
$\beta_1,\ldots,\beta_t$. In the tensor basis $e_i\otimes h_u$, ordered
lexicographically, $f\otimes g$ is again upper triangular: each
$fe_i\otimes gh_u$ is $\alpha_i\beta_u\,e_i\otimes h_u$ plus terms
involving strictly earlier basis vectors. Its diagonal is therefore
$\{\alpha_i\beta_u\}$, and taking $g=f$ repeatedly gives $\alpha^n$ among
the eigenvalues of $f^{\otimes n}$. For $\bigwedge^s$, use the exterior
basis $e_{i_1}\wedge\cdots\wedge e_{i_s}$ with $i_1<\cdots<i_s$, ordered
so that the flag of $f$ induces one on $\bigwedge^sV$; expanding
$fe_{i_1}\wedge\cdots\wedge fe_{i_s}$ and collecting increasing-index
terms, with the sign bookkeeping of the alternating map, gives
$\alpha_{i_1}\cdots\alpha_{i_s}$ on the diagonal and smaller index sets
off it. In particular a diagonal $f$ with entries $c_1,\ldots,c_r$ has
exterior entries $c_{i_1}\cdots c_{i_s}$, which is the concrete form used
below. For the dual, in dual bases $f^\vee$ has the transpose matrix of
$f^{-1}$, upper triangular for the dual flag with diagonal
$\{\alpha_i^{-1}\}$; invertibility of $f$ makes every $\alpha_i$ nonzero.
The exterior basis and the sign rule are Mathlib's
`exteriorPower.basis_apply` and
`AlternatingMap.map_perm`; the tensor, exterior and dual spectra
themselves are absent there.

Uses: [d-weights], [p-linear-triangular]
