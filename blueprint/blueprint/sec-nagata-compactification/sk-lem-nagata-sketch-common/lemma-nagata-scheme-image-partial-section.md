+++
id = "lemma-nagata-scheme-image-partial-section"
kind = "lemma"
title = "Scheme-theoretic image of a partial section"
order = 238
lean = ["AlgebraicGeometry.isIso_restrict_imageι_comp_fst", "AlgebraicGeometry.isPullback_toImage_partialSection"]
uses = ["def-nagata-extended-ideal", "def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "lem-weil-pbc-closed-immersion-from-composite", "lemma-nagata-dense-flat-pullback", "lemma-nagata-open-immersion-qc-over-separated-target", "lemma-nagata-scheme-image-ideal-qc", "lemma-nagata-scheme-image-of-closed-immersion", "lemma-nagata-scheme-image-restrict-open"]
+++
Let $U\hookrightarrow X$ be a quasi-compact open immersion, let
$Y\to S$ be separated, and let
$U\to X\times_SY$ be a morphism whose first projection is the given open
immersion. If $Z$ is its scheme-theoretic image, then the projection
$Z\to X$ has inverse image $U$ over the open $U\subseteq X$, and this
inverse image maps isomorphically to $U$.

## Proof

By [lemma-nagata-scheme-image-restrict-open], restriction to
$U\times_SY$ commutes with taking the scheme-theoretic image. On this
open target the original map is a section of
$U\times_SY\to U$. That projection is separated, so its section is a
closed immersion. By
[lemma-nagata-scheme-image-of-closed-immersion], its
scheme-theoretic image is canonically its source, compatibly with the
projection to $U$.
