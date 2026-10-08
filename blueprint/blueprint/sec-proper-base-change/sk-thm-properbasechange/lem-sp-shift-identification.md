+++
id = "lem-sp-shift-identification"
kind = "lemma"
title = "Shift rule for derived functors"
order = 1211
uses = ["def-sp-kinjective-bridge", "def-sp-left-exact-additive", "lem-sp-kinjective-computes"]
+++
Let $v$ be a left exact additive [def-sp-left-exact-additive] functor, let
$K\in\operatorname{Ch}^+(\mathcal A)$ and let $q\in\mathbb Z$. Then the
derived functor commutes with the shift and the cohomology of a shifted
complex is the shifted cohomology:

$$
 \mathcal H^{p+q}\bigl(Rv(\mathcal H^qK[-q])\bigr)
 =\mathcal H^{p}\bigl(Rv(\mathcal H^qK)\bigr)
 =R^pv(\mathcal H^qK).
$$

## Proof

The derived functor of a left exact additive functor
[def-sp-left-exact-additive] on $\operatorname{Ch}^+$ is the functor applied
to a K-injective resolution, by the definition in
[def-sp-kinjective-bridge]. It commutes with the shift by part (3) of
[lem-sp-kinjective-computes], so the cohomology of the shifted complex is the
shifted cohomology, which is the first displayed identity. The second is the
definition $R^pv=\mathcal H^p\circ Rv$ of [def-sp-kinjective-bridge],
together with part (2) of [lem-sp-kinjective-computes] identifying it, on an
object, with the derived functor of [def-sp-left-exact-additive].
