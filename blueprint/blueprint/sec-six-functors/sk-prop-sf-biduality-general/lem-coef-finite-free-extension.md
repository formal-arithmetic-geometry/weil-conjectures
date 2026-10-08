+++
id = "lem-coef-finite-free-extension"
kind = "lemma"
title = "Finite free coefficient extensions and cofinal levels"
order = 2143
uses = ["cor-coef-finite-verdier", "def-coefficient-twists-detailed", "def-weil-derived-pullback-tensor-hom", "lem-coef-finite-closed-shriek", "lem-coef-finite-direct-image", "lem-coef-finite-dualizing", "thm-coef-finite-hom"]
+++
Let $E\subset L$ be a finite extension of coefficient fields,
with ramification index $e$. For every $n\geq1$, put

$$
A=\mathcal O_E/\varpi_E^n,\qquad
B=\mathcal O_L/\varpi_E^n\mathcal O_L
=\mathcal O_L/\varpi_L^{en}=A_{L,en}.
$$

Equality here is equality of ideals; a unit relating the chosen
uniformizers does not change the quotient. The coefficient ring
$B$ is finite free over $A$. For finite-Tor constructible
complexes the canonical maps give isomorphisms

$$
\begin{aligned}
(Rf_{*,A}K)\otimes_A B&\cong Rf_{*,B}(K\otimes_A B),\\
(Ri_A^!M)\otimes_A B&\cong Ri_B^!(M\otimes_A B),\\
\omega_{X,A}\otimes_A B&\cong\omega_{X,B},\\
R\mathcal Hom_A(K,M)\otimes_A B
&\cong R\mathcal Hom_B(K\otimes_A B,M\otimes_A B),\\
(D_{X,A}K)\otimes_A B&\cong D_{X,B}(K\otimes_A B).
\end{aligned}
$$

They respect evaluation, double-dual maps and the adjunction
counits, are compatible with further finite coefficient-field
extension, and commute with coefficient reduction. Their formation
is natural under scheme isomorphisms, in particular Frobenius.
Thus the levels $en$ give the coefficient comparisons on a
cofinal subsystem of the $\mathcal O_L$-adic tower.

## Proof

The module $\mathcal O_L$ is finite and torsion free over the
DVR $\mathcal O_E$, hence finite free; reducing a free basis
modulo $\varpi_E^n$ proves the assertion about $B/A$.
The ordinary direct-image projection comparison is an isomorphism
for a finite free coefficient module by additivity; this is the
finite-free starting case of [lem-coef-finite-direct-image].
Apply it to the closed-support triangle exactly as in
[lem-coef-finite-closed-shriek]. This proves the closed
exceptional comparison with the same counit-defined map.
The local closed-embedding computation of
[lem-coef-finite-dualizing] then proves the comparison for
$\omega_X$. The Tate twists of [def-coefficient-twists-detailed]
commute with coefficient extension: they are the tensor extensions
of the same prime-to-characteristic root-of-unity sheaves, and
the affine-space trace uses their coefficient-linear counit.

For internal Hom one can either repeat the strata argument of
[thm-coef-finite-hom], or use finite freeness directly.
The tensor–Hom adjunction in
[def-weil-derived-pullback-tensor-hom] identifies the
underlying $A$-object of the target with
$R\mathcal Hom_A(K,M\otimes_A B)$.
For a finite free coefficient module, additivity identifies this
with $R\mathcal Hom_A(K,M)\otimes_A B$. The canonical
identification is independent of the temporary choice of a
free basis, since it is the map adjoint to evaluation. Combining
this with the dualizing comparison gives the Verdier comparison
by precisely the construction of [cor-coef-finite-verdier].

For two field extensions, or a quotient followed by extension,
transpose both proposed composite comparisons under the same
adjunction. Both are tensor reassociation followed by the same
evaluation or counit. This proves their equality, as well as
evaluation and double-dual compatibility. The constructions use
only pullback, tensor, evaluation, and natural adjunction maps,
so they are unchanged by transporting along a scheme
isomorphism. Finally the positive multiples $en$ are cofinal
among the positive integers, and
$(\varpi_E^n)\mathcal O_L=(\varpi_L^{en})$. These are exactly
the finite levels needed when reconstructing after scalar extension;
one does not identify equal numerical indices for the two different
uniformizers.
