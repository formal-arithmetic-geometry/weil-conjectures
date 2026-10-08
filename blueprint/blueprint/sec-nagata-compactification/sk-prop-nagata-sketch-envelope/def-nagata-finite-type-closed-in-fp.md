+++
id = "def-nagata-finite-type-closed-in-fp"
kind = "definition"
title = "Separated finite-presentation envelope"
order = 396
uses = ["def-nagata-finite-type-fp-model-system", "def-nagata-fixed-base-separated-stage"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Let $S$ be qcqs and let $X\to S$ be separated and of finite type. Form

$$
\mathsf{FP}(X/S)=(A_{X/S},(X_\alpha)_\alpha).
$$

Apply [def-nagata-fixed-base-separated-stage] to this system and
define

$$
\alpha^{X/S}_{\mathrm{sep}}
=\alpha_{\mathrm{sep}},
\qquad
X^{\mathrm{fp}}=X_{\alpha^{X/S}_{\mathrm{sep}}},
\qquad
i^{\mathrm{fp}}_{X/S}
=i_{\alpha^{X/S}_{\mathrm{sep}}}\colon X\hookrightarrow X^{\mathrm{fp}}.
$$

Denote the resulting explicit pair by
$\mathsf{Env}_{\mathrm{fp}}(X/S)=(X^{\mathrm{fp}},i^{\mathrm{fp}}_{X/S})$.
