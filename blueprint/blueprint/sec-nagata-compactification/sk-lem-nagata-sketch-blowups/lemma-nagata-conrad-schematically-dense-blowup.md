+++
id = "lemma-nagata-conrad-schematically-dense-blowup"
kind = "lemma"
title = "An admissible blow-up making the open scheme-theoretically dense"
order = 176
lean = ["AlgebraicGeometry.IsAdmissible.exists_comp_isSchemeTheoreticallyDominant_preimage", "AlgebraicGeometry.exists_isAdmissible_isSchemeTheoreticallyDominant_preimage"]
uses = ["def-nagata-admissible-blowup", "def-nagata-constructible-closed-support", "def-nagata-dense-compactification", "def-nagata-global-blowup", "def-nagata-qc-open-complement-ideal", "lemma-nagata-admissible-blowup-comp", "lemma-nagata-admissible-blowup-preserves-density", "lemma-nagata-blowup-proper", "lemma-nagata-conrad-dense-in-admissible-blowup", "lemma-nagata-constructible-closed-support", "lemma-nagata-qc-open-complement-ideal", "lemma-nagata-qc-open-complement-ideal-exists", "prop-nagata-global-blowup-cover-independent", "thm-nagata-global-blowup-proper"]
+++
Let $X$ be qcqs and let $U\subseteq X$ be a quasi-compact open. There is a
$U$-admissible blow-up $X_1\to X$ in which $U$ is scheme-theoretically
dense. If $U$ is dense in $X$ and $\widetilde X\to X$ is any $U$-admissible
blow-up, the same applies to $\widetilde X$, and the composite
$X_1\to\widetilde X\to X$ is again a $U$-admissible blow-up of $X$.

## Proof

By [lemma-nagata-qc-open-complement-ideal-exists] there is a finite
type quasi-coherent ideal $\mathcal I_0\subseteq\mathcal O_X$ with
$V(\mathcal I_0)=X\setminus U$. Its blow-up is $U$-admissible, and $U$ is
scheme-theoretically dense in it by the second assertion of
[lemma-nagata-conrad-dense-in-admissible-blowup]. Applying this to
$\widetilde X$ in place of $X$ — legitimate because the preserved open of
a $U$-admissible blow-up is again quasi-compact — and composing,
[lemma-nagata-admissible-blowup-comp] identifies the composite with a
single $U$-admissible blow-up of $X$.
