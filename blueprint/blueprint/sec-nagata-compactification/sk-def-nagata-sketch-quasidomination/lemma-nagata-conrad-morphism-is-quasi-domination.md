+++
id = "lemma-nagata-conrad-morphism-is-quasi-domination"
kind = "lemma"
title = "A morphism on a dense open of a separated target is a quasi-domination of that open (Conrad)"
order = 179
uses = ["def-nagata-conrad-quasi-domination"]
+++
**Status.** Bypassed by the formalized route: quasi-dominations are not
introduced in Lean. The extension statements are proved directly from
scheme-theoretic dominance and separatedness, through
`AlgebraicGeometry.ext_of_isSchemeTheoreticallyDominant_of_isSeparated`.

Let $Y\to S$ be separated and let $f\colon U\to Y$ be any $S$-morphism.
Then $(U,f)$ is a quasi-domination of $U$ over $Y$.

## Proof

Take $X=U$ in [def-nagata-conrad-quasi-domination]. The open
subscheme $U\subseteq U$ is dense, and the closedness condition asks that
$\Gamma_f$ be closed in $U\times_SY$, which is the separatedness of
$Y\to S$.
