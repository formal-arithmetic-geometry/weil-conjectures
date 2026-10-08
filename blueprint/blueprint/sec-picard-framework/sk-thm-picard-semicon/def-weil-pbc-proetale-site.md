+++
id = "def-weil-pbc-proetale-site"
kind = "definition"
title = "Small pro-etale site"
order = 662
uses = ["def-weil-abstract-derived-category", "def-weil-pbc-scheme-conventions", "def-weil-scheme-morphism-properties", "def-weil-size-convention"]
+++
For a scheme $T$, the *small pro-etale site* $T_{\Proet}$ has as objects the
weakly etale [def-weil-pbc-scheme-conventions] morphisms $U\to T$, and as
covering families the jointly surjective fpqc covering families, i.e.
families $\{U_i\to U\}$ of weakly etale maps such that for every affine open
$V\subset U$, finitely many affine opens $V_j\subset U_{i_j}$ have images
covering $V$.

## Detailed form

Fix a scheme $Y$. Choose Grothendieck universes $\mathcal U\in\mathcal V$ and
a $\mathcal V$-small skeleton, as required by the size convention
[def-weil-size-convention], and form all categories below inside $\mathcal
V$. The site $Y_{\mathrm{proet}}$ has as objects the $\mathcal U$-bounded
weakly etale maps $U\to Y$, where a weakly etale map
[def-weil-scheme-morphism-properties] is flat with flat diagonal. A family
$\{U_i\to U\}_{i\in I}$ is a covering if every arrow is weakly etale and, for
every affine open $V\subset U$, finitely many affine opens $V_j\subset
U_{i_j}$ have images covering $V$.

For a commutative ring $A$, let $A_Y$ be the sheafification of the constant
presheaf $U\mapsto A$ on $Y_{\mathrm{proet}}$. Let
$\Sh(Y_{\mathrm{proet}},A)$ be the abelian category of sheaves of
$A_Y$-modules, and set

$$
 D(Y_{\mathrm{proet}},A)=D\bigl(\Sh(Y_{\mathrm{proet}},A)\bigr),
$$

using the derived category of cochain complexes
[def-weil-abstract-derived-category].
