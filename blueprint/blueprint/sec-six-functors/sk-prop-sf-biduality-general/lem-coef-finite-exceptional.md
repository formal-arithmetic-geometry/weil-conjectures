+++
id = "lem-coef-finite-exceptional"
kind = "lemma"
title = "Finite exceptional adjoints and coefficient change"
order = 2148
uses = ["cor-coef-finite-verdier", "fix-cor-verdier-exchange", "fix-lem-tensor-adjunction", "lem-fix-compact-support-coefficient-change", "thm-fix-general-biduality", "thm-sf-preservation-class"]
+++
For a separated finite-type $f:X\to Y$, on the finite-Tor
constructible categories one has canonically

$$
Rf_n^!L\cong D_{X,n}f^*D_{Y,n}L.
$$

For $m\geq n$, coefficient reduction gives a canonical isomorphism

$$
(Rf_m^!L)\otimes^L_{A_m}A_n
\cong Rf_n^!(L\otimes^L_{A_m}A_n).
$$

These maps satisfy the quotient cocycle and identify the units and
counits under the compact-support coefficient comparison.

## Proof

Finite exceptional preservation is [thm-sf-preservation-class].
The finite anti-equivalences of [thm-fix-general-biduality],
ordinary pullback–direct-image adjunction, and the formal exchange
[fix-cor-verdier-exchange] give natural adjunction bijections

$$
\begin{aligned}
\operatorname{Hom}_X(K,D_Xf^*D_YL)
&\cong\operatorname{Hom}_X(f^*D_YL,D_XK)\\
&\cong\operatorname{Hom}_Y(D_YL,Rf_*D_XK)\\
&\cong\operatorname{Hom}_Y(D_YL,D_YRf_!K)\\
&\cong\operatorname{Hom}_Y(Rf_!K,L).
\end{aligned}
$$

Here every object is in the finite-Tor constructible domain.
Uniqueness of the right adjoint identifies this functor with the
already constructed $Rf^!$, together with its unit and counit.
The internal-Hom adjunction [fix-lem-tensor-adjunction], followed
by derived global sections, gives the corresponding canonical
isomorphism of derived mapping complexes. This supplies the enriched
adjunction independently of taking degree-zero Hom groups.

Apply the coherent duality comparisons
[cor-coef-finite-verdier] to the two duals in this formula;
coefficient tensor commutes with ordinary pullback. This constructs
the stated coefficient isomorphism and its cocycle. To identify
its adjunction maps, transpose under the displayed bijections.
Every arrow is either evaluation, a tensor associativity map, or
an adjunction counit. The duality comparison preserves evaluation,
and [lem-fix-compact-support-coefficient-change] preserves the
compact-support counit and projection construction. The transposes
are consequently the same compact-support coefficient comparison.
Thus the maps identify the units and counits, before any tower is
reconstructed.
