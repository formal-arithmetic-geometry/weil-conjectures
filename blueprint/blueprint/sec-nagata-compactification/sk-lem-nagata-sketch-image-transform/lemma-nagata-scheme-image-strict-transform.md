+++
id = "lemma-nagata-scheme-image-strict-transform"
kind = "lemma"
title = "[stacks-project]"
order = 233
lean = ["AlgebraicGeometry.Scheme.Hom.ker_lift_admissibleBlowup"]
uses = ["def-nagata-admissible-blowup", "def-nagata-dense-compactification", "def-nagata-global-blowup", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "def-nagata-strict-transform", "lemma-nagata-dense-flat-pullback", "lemma-nagata-scheme-image-ideal-qc", "lemma-nagata-scheme-image-transport-strict-transform", "lemma-nagata-strict-transform-closure-characterization", "lemma-nagata-strict-transform-over-complement", "prop-nagata-global-blowup-cover-independent", "thm-nagata-global-blowup-complement"]
+++
Let $V\to X\times_SY$ be quasi-compact and quasi-separated, and assume its
projection to $X$ factors through an open $U\subseteq X$. Let $Z$ be its
scheme-theoretic image. If $X'\to X$ is a $U$-admissible blow-up, then the scheme-theoretic
image of the lifted map $V\to X'\times_SY$ is the strict transform of $Z$.
More precisely, use the canonical isomorphism
$\varepsilon\colon X'\times_XU\cong U$ from
[thm-nagata-global-blowup-complement]; the lift is the map whose
$X'$-component is obtained from $V\to U$ by
$\varepsilon^{-1}\colon U\to X'\times_XU\to X'$ and whose $Y$-component is
the given projection $V\to Y$.

## Proof

Apply [lemma-nagata-scheme-image-transport-strict-transform] to the
given map $V\to X\times_SY$. Its lifted map is exactly the map specified in
the statement through $\varepsilon^{-1}$, so the resulting image equality is
the claimed identification with the strict transform.
