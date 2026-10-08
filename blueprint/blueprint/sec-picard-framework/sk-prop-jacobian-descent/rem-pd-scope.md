+++
id = "rem-pd-scope"
kind = "remark"
title = "What changed relative to the separably closed case"
order = 869
uses = ["lem-pc-rational-hyp", "lem-pc-rational-points-dense", "rem-sc-jacobian-scope", "thm-pc-picard-representable", "thm-pd-effective-descent", "thm-pd-geometric-pic0", "thm-pd-jacobian-general-field", "thm-pd-spreading-out", "thm-sc-jacobian-representability"]
+++
[thm-pd-jacobian-general-field] is the statement that
[rem-sc-jacobian-scope] of the Jacobian chapter declares to lie outside
the scope of that chapter. The route taken here is the descent route: the
theorem is proved over a separable closure by
[thm-pd-geometric-pic0] and then descended, so that neither
Grothendieck's existence theorem in the presence of a rational point nor a
choice of a base point enters. In particular the hypothesis that $k$ be
separably closed in [thm-pc-picard-representable] and in
[thm-sc-jacobian-representability] is used only to manufacture a
$k$-rational point, as the proof of [thm-pc-picard-representable]
records through [lem-pc-rational-points-dense] and
[lem-pc-rational-hyp]; over an arbitrary ground field the rational point
is unnecessary.

## Proof

The comparison of scopes is immediate from the statements:
[rem-sc-jacobian-scope] asserts that representability over a general
ground field is not proved in that chapter and would require a descent from a
finite separable extension, while
[thm-pd-jacobian-general-field] supplies exactly that descent, with the
two ingredients named in that remark replaced by
[thm-pd-effective-descent] (Stacks Project, Lemma 39.25.3, Tag
[0CCJ](https://stacks.math.columbia.edu/tag/0CCJ)) and
[thm-pd-spreading-out] (Stacks Project, Lemma 32.10.1, Tag
[01ZM](https://stacks.math.columbia.edu/tag/01ZM)). That the separable
closedness of the two cited theorems serves only to produce a rational point
is visible in the proof of [thm-pc-picard-representable], which obtains
$\sigma$ from [lem-pc-rational-points-dense] and then applies
[lem-pc-rational-hyp]; the rational point is what
[thm-pd-geometric-pic0] supplies geometrically and what the descent of
[thm-pd-jacobian-general-field] replaces, the two theorems
[thm-sc-jacobian-representability] and [thm-pd-geometric-pic0] being
the separably closed statement and its geometric consequence.
