+++
id = "thm-trf-verdier-biduality"
kind = "theorem"
title = "Verdier biduality for the dualizing complex"
order = 2269
uses = ["def-trf-admissibility", "def-trf-coefficient-conventions", "def-trf-dualizing-complex", "def-weil-derived-tensor", "def-weil-exceptional-inverse-image", "def-weil-finite-field-fiber", "def-weil-finite-tor-amplitude", "def-weil-scheme-morphism-properties", "lem-weil-duality-pairing", "thm-fix-general-biduality"]
+++
Fix the global finite-field datum
and the coefficient
conventions, $A=A_{E,n}$, and let $Y$ be a
separated finite-type
$k$-scheme with
exceptionally admissible structure
morphism $a_Y$. For the dualizing
complex $\omega_{Y,A}$ and Verdier dual $D_Y$ of
[def-trf-dualizing-complex], let $M\in D^b_{ctf}(Y,A)$.
Then there is a functorial isomorphism

$$
M\xrightarrow{\ \sim\ }D_YD_YM,
$$

and the evaluation $\operatorname{ev}_M$ of
[def-trf-dualizing-complex] is the map

$$
\operatorname{ev}_M:D_YM\otimes_A^LM\to\omega_{Y,A}.
$$

## Proof

Finite-stage geometric biduality, [thm-fix-general-biduality],
supplies the double-dual isomorphism on the stated constructible
finite-Tor category, with no additional boundary hypothesis.
Its dualizing object is the one in [def-trf-dualizing-complex],
by uniqueness of the exceptional right adjoint.
The double-dual morphism is the adjoint of evaluation
by [lem-weil-duality-pairing], so its evaluation is the map of
[def-trf-dualizing-complex] displayed in the statement.
