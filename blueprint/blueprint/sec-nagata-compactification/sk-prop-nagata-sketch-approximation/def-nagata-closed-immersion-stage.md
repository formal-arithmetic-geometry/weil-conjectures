+++
id = "def-nagata-closed-immersion-stage"
kind = "definition"
title = "Stage at which a finite-presentation map is closed"
order = 365
uses = ["lemma-nagata-closed-immersion-stage-exists"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Let $g_\lambda\colon Z_\lambda\to Y_\lambda$ be of finite presentation
between finite-presentation $S_\lambda$-schemes, and assume its base change
to $S$ is a closed immersion. Define $\mu_{\mathrm{cl}}(g)$ by classical
choice from the witness type supplied by
[lemma-nagata-closed-immersion-stage-exists]. Only the index component
is part of this definition; its eventual property is stated below.
