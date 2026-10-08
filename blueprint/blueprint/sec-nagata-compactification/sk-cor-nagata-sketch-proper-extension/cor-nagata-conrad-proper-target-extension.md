+++
id = "cor-nagata-conrad-proper-target-extension"
kind = "theorem"
title = "Extension of a rational map to a proper target (Conrad)"
order = 225
lean = ["AlgebraicGeometry.exists_admissibleBlowup_extend_section"]
tags = ["latex:corollary"]
uses = ["def-nagata-admissible-blowup", "def-nagata-global-blowup", "lem-weil-pbc-closed-immersion-from-composite", "lemma-nagata-conrad-morphism-is-quasi-domination", "lemma-nagata-conrad-quasi-domination-proper-target", "prop-nagata-global-blowup-cover-independent", "thm-nagata-conrad-elimination"]
+++
Let $S$ be qcqs, let $X$ be a qcqs $S$-scheme, let $U\subseteq X$ be a dense
quasi-compact open subscheme, and let $Y\to S$ be proper and of finite type.
Every $S$-morphism $f\colon U\to Y$ extends to an $S$-morphism
$\widetilde f\colon\widetilde X\to Y$ on some $U$-admissible blow-up
$\widetilde X\to X$.

## Proof

Take $V=U$. By
[lemma-nagata-conrad-morphism-is-quasi-domination], $(U,f)$ is a
quasi-domination of $U$ over $Y$, because a proper morphism is separated.
[thm-nagata-conrad-elimination] gives a $U$-admissible blow-up
$\widetilde X\to X$ and a quasi-domination $(W,\widetilde f)$ of
$\widetilde X$ over $Y$ extending $f$. Since $Y\to S$ is proper,
[lemma-nagata-conrad-quasi-domination-proper-target] forces $W$ to be
all of $\widetilde X$.
