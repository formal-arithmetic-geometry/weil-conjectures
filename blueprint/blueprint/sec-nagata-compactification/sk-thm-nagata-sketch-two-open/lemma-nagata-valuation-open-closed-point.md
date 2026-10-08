+++
id = "lemma-nagata-valuation-open-closed-point"
kind = "lemma"
title = "An open containing the closed point of a valuation spectrum is total"
order = 293
lean = ["AlgebraicGeometry.TwoOpenSide.KeyDisjoint.avoids"]
uses = ["def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "def-nagata-two-open-boundary-loci", "def-nagata-two-open-comparison-space", "def-nagata-two-open-graph-extensions", "def-nagata-two-open-intermediate-schemes", "lemma-nagata-key-boundary-disjointness", "lemma-nagata-scheme-image-ideal-qc", "lemma-nagata-valuation-factor-closed"]
+++
Let $A$ be a valuation ring and let $O\subseteq\operatorname{Spec}(A)$ be
open. If the closed point $\mathfrak m_A$ belongs to $O$, then
$O=\operatorname{Spec}(A)$.

## Proof

Choose a basic open $D(a)$ with $\mathfrak m_A\in D(a)\subseteq O$.
Then $a\notin\mathfrak m_A$, hence $a$ is a unit of the local ring $A$ and
$D(a)=\operatorname{Spec}(A)$.
