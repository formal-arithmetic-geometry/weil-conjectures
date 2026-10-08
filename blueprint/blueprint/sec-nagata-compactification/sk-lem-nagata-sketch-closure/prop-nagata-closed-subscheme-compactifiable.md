+++
id = "prop-nagata-closed-subscheme-compactifiable"
kind = "theorem"
title = "The closed-subscheme construction is a compactification"
order = 86
lean = ["AlgebraicGeometry.HasCompactification.of_isClosedImmersion"]
tags = ["latex:proposition"]
uses = ["def-nagata-closed-subscheme-compactification", "def-nagata-compactifiable", "def-nagata-compactification", "lemma-nagata-scheme-image-of-closed-immersion", "lemma-nagata-scheme-image-restrict-open"]
+++
The constructed factorization $\mathsf{Closed}(i,C')$ is a compactification
of $X\to S$.

## Proof

Its ambient scheme $\overline X$ is closed in the proper scheme
$\overline X'$, hence is proper over $S$. By
[lemma-nagata-scheme-image-restrict-open], its pullback to the open
$X'\subseteq\overline X'$ is the scheme-theoretic image of
$i\colon X\hookrightarrow X'$. By
[lemma-nagata-scheme-image-of-closed-immersion], the factor map for
$i$ is an isomorphism, and compatibility with the image inclusion identifies
the pullback image with $X$. Hence

$$
X\cong\overline X\times_{\overline X'}X',
$$

so $X\to\overline X$ is identified with the base change of the
quasi-compact open immersion $X'\to\overline X'$.
