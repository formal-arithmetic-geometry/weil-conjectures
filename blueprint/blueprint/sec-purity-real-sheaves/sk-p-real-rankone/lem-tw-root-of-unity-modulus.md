+++
id = "lem-tw-root-of-unity-modulus"
kind = "lemma"
title = "Modulus of a root of unity"
order = 2627
uses = ["def-tw-eigenvalue"]
+++
Every root of unity $\zeta\in\overline{\mathbf Q}_\ell^\times$ has
absolute value $|\zeta|=1$ with respect to the absolute value of
[def-tw-eigenvalue]; in particular every root of unity is of weight
$0$. Moreover, for every field isomorphism
$\iota:\overline{\mathbf Q}_\ell\xrightarrow{\sim}\mathbf C$, the
complex number $\iota(\zeta)$ also has modulus one.

## Proof

If $\zeta^m=1$ for some $m\geq1$, then multiplicativity of the
absolute value gives $|\zeta|^m=1$, hence $|\zeta|=1$; the same
argument applies to the complex modulus of $\iota(\zeta)$. Weight zero
is the case $w=0$ of [def-tw-eigenvalue].
