+++
id = "lemma-nagata-closed-immersion-descends"
kind = "lemma"
title = "A finite-presentation closed immersion descends at the selected stage"
order = 366
uses = ["def-nagata-closed-immersion-stage", "lemma-nagata-closed-immersion-stage-exists"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

For every $\mu\geq\mu_{\mathrm{cl}}(g)$, the base change $g_\mu$ is a
closed immersion.

## Proof

Project the eventual closed-immersion field of the witness in
[lemma-nagata-closed-immersion-stage-exists] along the index selected in
[def-nagata-closed-immersion-stage].
