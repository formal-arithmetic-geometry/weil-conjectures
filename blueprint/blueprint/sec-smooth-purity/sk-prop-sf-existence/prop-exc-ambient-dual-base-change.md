+++
id = "prop-exc-ambient-dual-base-change"
kind = "theorem"
title = "Dual base change for the ambient right adjoint is formal"
order = 1813
tags = ["latex:proposition"]
uses = ["cor-sf-ambient-adjoint-discharge", "def-cbc-exchange-map", "def-sf-fullcd-used-class", "def-weil-ambient-exceptional-adjoint", "def-weil-pbc-derived-categories"]
+++
Let

$$
\begin{array}{ccc}
X'&\xrightarrow{\ g'\ }&X\\
f'\downarrow&&\downarrow f\\
Y'&\xrightarrow{\ g\ }&Y
\end{array}
$$

be Cartesian with $f,f'$ separated finite type carrying the ambient
exceptional right adjoint datum of
[def-weil-ambient-exceptional-adjoint], and let $g$ be arbitrary.
Then the right-adjoint mate of the compact-support base-change
isomorphism of [def-cbc-exchange-map],

$$
\beta^{\vee}:\ Rf^{\times}Rg_*\xrightarrow{\ \sim\ }Rg'_*Rf'^{\times},
$$

is an isomorphism. On the blueprint's coefficient class
[def-sf-fullcd-used-class] the datum displayed as the hypothesis is the
theorem [cor-sf-ambient-adjoint-discharge], and the mate is formed
object-wise, so on that class the isomorphism holds without hypothesis; the
datum is retained for the complexes outside it,
[rem-sf-class-adjoint-residue].

## Proof

Compact-support base change is the isomorphism
$Lg^*Rf_!\xrightarrow{\sim}Rf'_!Lg'^*$ of
[def-cbc-exchange-map]. By
[def-weil-ambient-exceptional-adjoint] the functors $Rf_!$ and
$Rf'_!$ have the right adjoints $Rf^{\times}$ and $Rf'^{\times}$;
the right adjoint of the composite $Lg^*Rf_!$ is the composite
$Rf^{\times}Rg_*$ of the right adjoints, and the right adjoint of
$Rf'_!Lg'^*$ is $Rg'_*Rf'^{\times}$. An isomorphism of functors
induces, by uniqueness of right adjoints, a unique isomorphism of their
right adjoints compatible with the units and counits; applied to the
displayed compact-support base change this is $\beta^{\vee}$.
