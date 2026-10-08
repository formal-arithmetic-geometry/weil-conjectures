+++
id = "lemma-nagata-strict-transform-over-complement"
kind = "lemma"
title = "Strict transform on the preserved open"
order = 160
lean = ["AlgebraicGeometry.isPullback_strictTransformOpen"]
uses = ["lemma-nagata-strict-transform-closure-characterization", "prop-nagata-strict-transform-closed-fiber-product", "thm-nagata-global-blowup-complement"]
+++
Let $f\colon Y\to X$, let $\mathcal I$ be a finite-type quasi-coherent
ideal, and put $X'=\operatorname{Bl}_{\mathcal I}(X)$. Over
$U=X\setminus V(\mathcal I)$, the strict transform is canonically
$Y\times_XU$, and its map to $Y$ is the ordinary pullback isomorphism.

## Proof

The blow-up is the identity over $U$ by
[thm-nagata-global-blowup-complement]. Under this specified
isomorphism the open whose closure defines the strict transform is all of
$Y\times_XU$. It is already a closed subscheme of itself, so the minimal
closed-subscheme characterization of
[lemma-nagata-strict-transform-closure-characterization] identifies
the restriction with $Y\times_XU$. On charts this is the quotient by the
zero torsion ideal after $a$ is inverted; these identifications agree on
overlaps by the closed chart model in
[prop-nagata-strict-transform-closed-fiber-product]. The projection
equality is the one induced by the fibre-product square.
