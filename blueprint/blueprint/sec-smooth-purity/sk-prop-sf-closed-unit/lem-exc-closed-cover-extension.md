+++
id = "lem-exc-closed-cover-extension"
kind = "lemma"
title = "Lifting a covering of a closed fibre"
order = 1854
uses = ["def-exc-closed-site-lift", "def-weil-pbc-proetale-site", "def-weil-pbc-scheme-conventions", "lem-exc-closed-lift-reduction"]
+++
Let $W$ be affine, let $Z_W\subset W$ be closed, and assume $W\setminus Z_W$
is quasi-compact. A finite affine ind-etale covering $\{V_a\to Z_W\}$
extends to a finite pro-etale covering of $W$ whose members over the closed
fibre are $v_W(V_a)$, and whose other members are affine opens in
$W\setminus Z_W$. Their reductions to $Z_W$ are respectively $V_a$ and
empty.

## Proof

Write $W=\operatorname{Spec}B$, $Z_W=V(J)$. Quasi-compactness of the
complement, in the sense of the scheme conventions, selects finitely many
$f_b\in J$ with $W\setminus Z_W=\bigcup_bD(f_b)$. Lift each $V_a$ by
[def-exc-closed-site-lift] over $B$. By [lem-exc-closed-lift-reduction], its
reduction is exactly $V_a$. Hence the images of these lifts cover $Z_W$,
while the $D(f_b)$'s cover its complement. All members are affine and weakly
etale over $W$, and the family is finite and surjective. It is consequently
a covering for the pro-etale topology, with the stated reductions.
