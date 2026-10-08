+++
id = "rem-sf-yoga"
kind = "remark"
title = "The yoga: which classical theorem is which"
order = 2233
+++
The point of the axiomatization is the following dictionary, each entry of
which is proved, as listed in the right-hand column, from
[def-sf-datum] and [def-sf-orientation] alone.

| classical statement | in the formalism | here |
| --- | --- | --- |
| Verdier duality exchange $D_YRf_!\cong Rf_*D_X$ | (A1) $+$ (A3) | [thm-sf-verdier-exchange] |
| biduality $D_XD_X\cong\operatorname{id}$ | proved in the framework chapter, [thm-fix-general-biduality] | [def-sf-datum] |
| global duality $R\Gamma_c^\vee\cong R\Gamma\mathbb D_X$ | (A1) $+$ (A3) $+$ point | [thm-sf-global-duality] |
| trace–cup pairing perfect | the above $+$ orientation | [thm-sf-identification] |
| trace isomorphism $H_c^{2d}\cong\Lambda(-d)$ ($H^{2d}$ if proper) | the above $+$ connectedness | *The trace isomorphism* |
| Künneth / product formula | (A2) $+$ (A3) $+$ (A4) | [thm-sf-kunneth-relative] |
| dual base change $Rf^!Rg_*\cong Rg'_*Rf'^!$ | (A1) $+$ (A2) | [thm-sf-dual-base-change] |
| duality against pullback $D_XLf^*\cong Rf^!D_Y$ | (A1) $+$ (A3) $+$ (A6) | [cor-sf-duality-pullback] |
| dualizing complex of a product | (A4) $+$ orientation | *The dualizing complex of a product* |
| orientations are stable under products | the above $+$ (A3) | *The orientation is multiplicative* |
| relative trace, and its transitivity | (A1) $+$ (A4) | *The relative trace, and its transitivity* |
| coherence of the Künneth isomorphism | (A2) $+$ (A3) $+$ (A4) | [lem-sf-kunneth-coherence] |
| Poincaré duality for a smooth variety | all of the above | *Poincare duality, framework form* |

Two consequences of the dictionary are worth stating explicitly. First,
none of the formal core uses the orientation, so all duality statements
are theorems about the *dualizing complex* $Ra_X^!\Lambda$ rather than
about a twisted constant sheaf; only after substituting the orientation do
they become statements about $H^i(X,\Lambda)$ with the twist $(-d)$.
Second, the proof cycle recorded in the brief blueprint between the
six-operations package [thm-weil-six-operations] and the duality chapter disappears:
the exchange is a formal consequence of the axioms, not a geometric
theorem, so it may be used in [thm-weil-six-operations] without circularity.
