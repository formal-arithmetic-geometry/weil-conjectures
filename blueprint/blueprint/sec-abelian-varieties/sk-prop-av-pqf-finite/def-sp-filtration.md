+++
id = "def-sp-filtration"
kind = "definition"
title = "Filtrations and graded pieces"
order = 507
uses = ["def-sp-abelian"]
+++
Let $\mathcal A$ be an abelian category [def-sp-abelian]. A *decreasing
filtration* $F^\bullet$ of an object $A\in\mathcal A$ is a family of
subobjects $F^nA\subseteq A$ ($n\in\mathbb Z$) with
$A\supseteq\cdots\supseteq F^nA\supseteq F^{n+1}A$; a *filtered object* is a
pair $(A,F)$. The *graded pieces* are
$\operatorname{gr}^nA:=F^nA/F^{n+1}A$. The filtration is *finite and
separated* on $A$ if $F^0A=A$, $F^NA=0$ for some $N$, and $\bigcap_nF^nA=0$.
(*Stacks Project: Definition 12.19.1, Tag
[0121](https://stacks.math.columbia.edu/tag/0121).*)
