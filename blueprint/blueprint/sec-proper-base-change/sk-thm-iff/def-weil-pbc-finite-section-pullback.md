+++
id = "def-weil-pbc-finite-section-pullback"
kind = "definition"
title = "Pullback of a section along a finite morphism"
order = 1078
uses = ["def-weil-pbc-inverse-image", "def-weil-pbc-scheme-conventions"]
+++
Let $u:T'\to T$ be finite and $F$ an etale sheaf on $T$. For an etale
$V\to T$ and $s\in F(V)$, define

$$
u_V^\sharp(s)\in(u^{-1}F)(V\times_TT')
$$

to be the image of $s$ under the unit from the presheaf inverse image to its
sheafification.

## Detailed form

For a finite morphism [def-weil-pbc-scheme-conventions] $h:V\to Y$ and
$a\in\Gamma(Y,F)$, define $h^\sharp a\in\Gamma(V,h^{-1}F)$ by the unit of the
inverse-image adjunction [def-weil-pbc-inverse-image].
