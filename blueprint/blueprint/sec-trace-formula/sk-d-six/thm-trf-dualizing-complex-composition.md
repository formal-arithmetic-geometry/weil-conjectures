+++
id = "thm-trf-dualizing-complex-composition"
kind = "theorem"
title = "Composition for the dualizing complex"
order = 2270
uses = ["def-trf-admissibility", "def-trf-coefficient-conventions", "def-trf-dualizing-complex", "def-weil-exceptional-inverse-image", "def-weil-finite-field-fiber", "def-weil-scheme-morphism-properties", "prop-functor-package"]
+++
Fix the global finite-field datum
and the coefficient
conventions, $A=A_{E,n}$, put $s=\Spec k$, and let
$d:F\to X$ be a
separated finite-type
morphism with $a_X$ and $a_F=a_X\circ d$
exceptionally admissible. Then there is a
canonical isomorphism

$$
Rd^!\omega_{X,A}\xrightarrow{\ \sim\ }\omega_{F,A},
$$

functorial in $d$, where $\omega_{X,A}$, $\omega_{F,A}$ are the
dualizing complexes of
[def-trf-dualizing-complex] and $Rd^!$ is the
exceptional inverse image of
$d$.

## Proof

The composition and base-change exchange data for the exceptional inverse
image of [def-trf-admissibility], together with the composition law
$R(a_X\circ d)_!\cong Ra_{X!}Rd_!$ of the six-operations package
[prop-functor-package] (item (3)), give the adjoint composition
isomorphism

$$
Rd^!Ra_X^!\xrightarrow{\ \sim\ }R(a_X\circ d)^!=Ra_F^!.
$$

Applying it to the constant complex $A_s$ and using
$\omega_{X,A}=Ra_X^!A_s$, $\omega_{F,A}=Ra_F^!A_s$ of
[def-trf-dualizing-complex] gives the displayed canonical
isomorphism; its compatibility with further compositions is the coherence
of the exchange data of [def-trf-admissibility]. (The types of
$Rd^!$ are those of [def-weil-exceptional-inverse-image].)
