+++
id = "thm-zl-relative-affine-curve-core"
kind = "theorem"
title = "Pure lisse relative affine-curve step"
order = 2844
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-scheme-conventions", "def-weil-punctual-weights", "def-weil-scheme-morphism-properties", "lem-zl-mixed-punctual-cutoff", "lem-zl-relative-curve-mixedness", "lem-zl-relative-curve-punctual"]
+++
Fix the coefficient and weight conventions of
[def-weil-punctual-weights]. Let $h:U_0\to Y_0$ be a
smooth separated morphism
between separated finite-type
$k_0$-schemes, with every nonempty geometric fiber a smooth affine
curve. Let $\mathcal F$ be a
lisse
$\Qlb$-Weil sheaf that is
punctually $\iota$-pure of weight $w$.
Then for every $i$, $R^ih_!\mathcal F$ is $\iota$-mixed of weights
at most $w+i$.

## Proof

By [lem-zl-relative-curve-punctual], all local Frobenius
eigenvalues on $R^ih_!\mathcal F$ have absolute value at most
$q_y^{(w+i)/2}$. The curve-reduction lemma [lem-zl-relative-curve-mixedness]
supplies a finite mixed filtration of this sheaf. Apply
[lem-zl-mixed-punctual-cutoff] with $v=w+i$.
This proves the bound without assuming that unrelated filtrations
of the individual stalks glue to Weil subsheaves.
