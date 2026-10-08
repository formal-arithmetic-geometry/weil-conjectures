+++
id = "lem-weil-pbc-levelwise-isomorphism-cones"
kind = "lemma"
title = "Levelwise isomorphisms and complete cones"
order = 1253
uses = ["def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-derived-inverse-limit", "prop-weil-pbc-koszul-reconstruction", "prop-weil-pbc-rlim-functoriality"]
+++
A morphism in $D(\operatorname{Tow}_{A}(T))$ whose evaluation at every $n$ is
an isomorphism is itself an isomorphism and remains an isomorphism after
$\Rlim$. If a derived complete object $C$ satisfies $C\otimes_A^LP_n=0$ for
every $n$, then $C=0$. Consequently a morphism between derived complete
objects is an isomorphism once every finite reduction is an isomorphism.

The vanishing criterion is the characterization
$K=\Rlim(K\otimes^L_\Lambda\underline{\Lambda/I^n})$ of Stacks Project, Lemma
61.20.1 (Tag [099M](https://stacks.math.columbia.edu/tag/099M)): the Stacks
entry assumes a Noetherian ring $\Lambda$ and an ideal $I$ and concerns one
object of $D(\mathcal C,\Lambda)$, while the conservativity of the levelwise
evaluations on $\operatorname{Tow}_A(T)$ used here is a property of the tower
category of [def-weil-pbc-adic-coefficient-datum] that 61.20 does not state.
The closure of the derived complete objects under cones, used at the end of
the statement, is clause (1) of Stacks Project, Proposition 61.21.1 (Tag
[099Q](https://stacks.math.columbia.edu/tag/099Q), Section 61.21, Tag
[099P](https://stacks.math.columbia.edu/tag/099P)), which states that the
derived complete sheaves of $\Lambda$-modules form a weak Serre subcategory,
together with clause (5) (an object is derived complete if and only if every
cohomology sheaf is): the Stacks entry assumes a Noetherian ring $\Lambda$
with an ideal $I$ and a site with enough weakly contractible objects, and the
form used here is the tower-category statement over $T_{\Proet}$.

## Proof

The evaluation functors of [def-weil-pbc-derived-inverse-limit] are jointly
conservative on the tower category, and $\Rlim$ is a triangulated functor ([prop-weil-pbc-rlim-functoriality]), so
the first assertion holds. For a derived complete $C$,
[prop-weil-pbc-koszul-reconstruction] identifies $C$ with $\Rlim C_\bullet$,
and the vanishing of every finite reduction kills the tower $C_\bullet$
levelwise, hence $C=0$; the cone of a morphism between derived complete
objects is again derived complete, so the last assertion follows from the
second.
