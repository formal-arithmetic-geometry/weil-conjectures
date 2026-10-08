+++
id = "lem-exc-field-discrete-modules"
kind = "lemma"
title = "Etale modules on a field and discrete Galois modules"
order = 977
uses = ["def-exc-continuous-cohomology", "def-weil-pbc-etale-sheaves", "def-weil-pbc-etale-site", "prop-weil-pbc-geometric-stalks-exact", "thm-galois-fundamental"]
+++
Let $K$ be a field, fix $K^{\rm sep}$, put
$G=\operatorname{Gal}(K^{\rm sep}/K)$, and let $A$ be
a finite commutative ring. The geometric fibre functor
identifies etale
$A$-module sheaves on $\operatorname{Spec}K$ with
discrete continuous
$A[G]$-modules, as exact abelian categories with their
section functors. Sections correspond to invariants.

## Proof

Finite etale field objects are finite disjoint unions of
finite separable extensions. They form a covering basis
for [def-weil-pbc-etale-site]. By finite Galois theory,
as included in [thm-galois-fundamental], they correspond
to finite continuous $G$-sets. For a module sheaf $F$,
its geometric fibre is

$$
M=\varinjlim_{L/K\ \mathrm{finite\ Galois}} F(\operatorname{Spec}L),
\qquad L\subset K^{\rm sep}.
$$

Field automorphisms give a $G$-action. A section defined
over $L$ is fixed by $\operatorname{Gal}(K^{\rm sep}/L)$,
so this module is discrete continuous in the sense of
[def-exc-continuous-cohomology].

For a finite separable extension $L/K$, put
$H=\operatorname{Gal}(K^{\rm sep}/L)$. The natural map
$F(L)\to M^H$ is injective: equality in the colimit holds
after a finite extension, which is an etale cover, and the
separated sheaf axiom gives equality over $L$.
For surjectivity, represent $m\in M^H$ by a section $s$
over a finite Galois $E/K$ containing $L$.
There are only finitely many cosets of
$\operatorname{Gal}(K^{\rm sep}/E)$ in $H$.
For representatives of these cosets, the equalities
$h\cdot m=m$ hold after finitely many further extensions.
Choose a common finite Galois extension $E'/K$.
The pullback of $s$ to $E'$ is invariant under
$\operatorname{Gal}(E'/L)$: elements fixing $E$
already fix a section pulled back from $E$, and the
chosen representatives give the remaining equalities.
Galois descent for the cover $\operatorname{Spec}E'\to \operatorname{Spec}L$, which is the sheaf equalizer axiom,
therefore descends this section to $F(L)$.

Conversely, from a discrete continuous module $M$ assign
to a finite etale object with finite $G$-set $S$ the
module $\operatorname{Hom}_G(S,M)$. A covering is a
jointly surjective family of finite $G$-sets; compatible
functions on its members glue uniquely. This defines a
module sheaf in [def-weil-pbc-etale-sheaves], and its
geometric fibre is $M$, since each element is fixed by
an open subgroup. The preceding computation of $F(L)$
shows the two constructions are inverse on all basis
objects, including their restriction maps. The fibre
functor is exact by [prop-weil-pbc-geometric-stalks-exact];
thus this is an exact equivalence. At $L=K$ the formula
for sections is exactly $M^G$. Consequently it also
identifies their right derived section functors, since an
exact equivalence takes injective resolutions to injective
resolutions. No finiteness of $M$ is required.
