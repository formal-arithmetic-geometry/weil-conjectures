+++
id = "lem-cbc-extension-zero-projection-formula"
kind = "lemma"
title = "Projection formula for extension by zero"
order = 1585
uses = ["def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-pbc-extension-by-zero", "def-weil-pbc-scheme-conventions", "lem-cbc-proetale-extension-zero"]
+++
For an open immersion
$j:U\hookrightarrow X$, a finite coefficient ring $\Lambda$, a
complex $K$ of $\Lambda$-modules on $U_{\Proet}$, and a complex
$L$ of $\Lambda$-modules on $X_{\Proet}$, the canonical map (with the derived tensor product of
[def-weil-derived-tensor])

$$
(j_!K)\otimes^L_\Lambda L\xrightarrow{\ \sim\ }
j_!\bigl(K\otimes^L_\Lambda j^{-1}L\bigr)
$$

is an isomorphism in $D(X_{\Proet},\Lambda)$.

## Proof

The canonical map is the adjoint of the projection morphism for
$j^{-1}$, the functors $j^{-1}$ and $-\otimes^L_\Lambda$
commuting by [def-weil-derived-tensor]. We verify the map by the
tensor–internal-Hom adjunction of
[def-weil-derived-pullback-tensor-hom]. For a test complex $M$
on $X_{\Proet}$,

$$
\operatorname{Hom}\bigl((j_!K)\otimes^L_\Lambda L,M\bigr)
\cong\operatorname{Hom}\bigl(j_!K,R\mathcal Hom_\Lambda(L,M)\bigr)
\cong\operatorname{Hom}\bigl(K,j^{-1}R\mathcal Hom_\Lambda(L,M)\bigr),
$$

the first isomorphism being the tensor–internal-Hom adjunction and
the second the adjunction $j_!\dashv j^{-1}$ of
[lem-cbc-proetale-extension-zero]. Formation of the internal Hom
commutes with inverse image,
$j^{-1}R\mathcal Hom_\Lambda(L,M)\cong R\mathcal Hom_\Lambda(j^{-1}L,j^{-1}M)$, by the same definition; the
last group is therefore
$\operatorname{Hom}\bigl(K\otimes^L_\Lambda j^{-1}L,j^{-1}M\bigr)$,
which by $j_!\dashv j^{-1}$ again is

$$
\operatorname{Hom}\bigl(j_!\bigl(K\otimes^L_\Lambda j^{-1}L\bigr),M\bigr).
$$

The two Hom-functors in $M$ are thus isomorphic, so by Yoneda the
two complexes are canonically isomorphic, and the isomorphism is the
displayed canonical map because it is induced by the units and counits
of the two adjunctions. No constructibility, no stalk computation,
and no conservativity enters: the statement is the projection formula
for the exact left adjoint $j_!$, in the pro-etale site.
