+++
id = "def-nagata-fixed-base-separated-stage"
kind = "definition"
title = "Selected stage for fixed-base separatedness"
order = 394
uses = ["lemma-nagata-fixed-base-separated-stage-exists"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Under the hypotheses of
[lemma-nagata-fixed-base-separated-stage-exists], choose one witness
and define $\alpha_{\mathrm{sep}}$ to be its index component. Eventual
separatedness is recorded only in the following specification lemma.
