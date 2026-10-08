+++
id = "lem-tw-punctual-rescaling"
kind = "lemma"
title = "Punctual purity on a closed fibre"
order = 2836
uses = ["def-weil-finite-field-fiber", "def-weil-punctual-weights", "def-weil-scheme-morphism-properties", "def-weil-weil-sheaf-complex"]
+++
Fix the finite-field datum
$(p,a,q,k_0,k)$, and let $h:X_0\to Y_0$ be a
finite-type morphism
of finite-type $k_0$-schemes.
Let $\mathcal F$ be a
Weil sheaf on $X_0$,
punctually pure of weight $w$.
For a closed point $y\in Y_0$, write
$m=[\kappa(y):k_0]$, so $\kappa(y)\cong\mathbf F_{q^m}$, and set

$$
X_y:=X_0\times_{Y_0}\operatorname{Spec}\kappa(y).
$$

Then the restriction $\mathcal F|_{X_y}$, with its induced Weil
structure, is punctually pure of weight $w$ relative to
$\kappa(y)$.

## Proof

The inclusion $X_y\hookrightarrow X_0$ is a closed immersion.
Thus a closed point $z$ of $X_y$ is the same closed point on
$X_0$, with the same residue field and the same local Frobenius
operator on the restricted stalk.
If $r=[\kappa(z):\kappa(y)]$, the tower of finite residue fields gives

$$
[\kappa(z):k_0]=mr,\qquad q_z=q^{mr}=(q^m)^r .
$$

Consequently an eigenvalue $\alpha$ on that stalk satisfies

$$
|\iota(\alpha)|=q_z^{w/2}=(q^m)^{rw/2},
$$

by [def-weil-punctual-weights] on $X_0$.
This is the same punctual weight condition over $\kappa(y)$.
No identification between the stalk at $z$ and a stalk at $y$
is involved.
