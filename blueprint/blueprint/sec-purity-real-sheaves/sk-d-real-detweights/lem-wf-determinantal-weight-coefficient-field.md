+++
id = "lem-wf-determinantal-weight-coefficient-field"
kind = "lemma"
title = "The determinant weight does not depend on the coefficient field"
order = 2633
uses = ["def-mg-determinant-line", "def-weil-punctual-weights"]
+++
Let $X_0$ be a normal geometrically connected curve over $k_0$, fix
$\iota:\Qlb\xrightarrow{\sim}\mathbf C$, and let $\mathcal V$ be an
irreducible lisse Weil sheaf of rank $r$ on $X_0$ whose
representation is defined over finite extensions
$E\subseteq E'$ of $\mathbf Q_\ell$. If
$\hyperref[def-mg-determinant-line]{\det(\mathcal V)}$, read with
coefficients in $E$, is
punctually $\iota$-pure of weight
$a$, then it is punctually $\iota$-pure of the same weight $a$ when
read with coefficients in $E'$.

## Proof

Punctual $\iota$-purity of [def-weil-punctual-weights] is the
condition that every eigenvalue $\alpha$ of every local Frobenius
satisfy $|\iota(\alpha)|=q_y^{a/2}$. The determinant line of
[def-mg-determinant-line] is the top exterior power of
$\mathcal V$, and its local Frobenius operators are obtained from those
of $\mathcal V$ by extension of scalars along $E\subseteq E'$; the
matrices of these operators, and therefore their eigenvalues in
$\overline{\mathbf Q}_\ell$, are unchanged by that extension. Since
$\iota$ is a fixed isomorphism on $\overline{\mathbf Q}_\ell$, the
displayed condition is the same for the two coefficient fields.
