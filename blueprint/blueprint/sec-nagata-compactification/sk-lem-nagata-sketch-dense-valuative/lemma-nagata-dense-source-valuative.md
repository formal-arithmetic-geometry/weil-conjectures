+++
id = "lemma-nagata-dense-source-valuative"
kind = "lemma"
title = "[stacks-project]"
order = 282
lean = ["AlgebraicGeometry.IsSeparated.of_valuativeCriterion_of_isDominant", "AlgebraicGeometry.UniversallyClosed.of_valuativeCriterion_of_isDominant"]
uses = ["def-nagata-dense-compactification", "def-nagata-dense-valuation-probe", "def-nagata-extended-ideal", "def-nagata-scheme-image-comparison", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "lemma-nagata-composite-valuation-ring", "lemma-nagata-dense-flat-pullback", "lemma-nagata-dense-valuation-probe", "lemma-nagata-scheme-image-ideal-qc", "lemma-nagata-scheme-image-universal", "lemma-nagata-scheme-theoretic-closure-minimal", "lemma-nagata-valuation-ring-extension"]
+++
Let $f\colon X\to S$ be quasi-compact and let
$h\colon U\to X$ be quasi-compact and quasi-separated,
and assume $h(U)$ is dense in $X$. Suppose that for every valuation
ring $A$ with fraction field $K$, every commutative diagram

$$
\operatorname{Spec}(K)\longrightarrow U\longrightarrow X,
\qquad
\operatorname{Spec}(A)\longrightarrow S
$$

has a unique lift $\operatorname{Spec}(A)\to X$. Then $f$ is
universally closed. If $f$ is quasi-separated, it is also separated.
