+++
id = "lemma-nagata-zmt-quasi-affine-source"
kind = "lemma"
title = "A quasi-finite scheme over a quasi-affine base is quasi-affine"
order = 184
lean = ["AlgebraicGeometry.Scheme.IsQuasiAffine.of_locallyQuasiFinite"]
uses = ["lemma-nagata-zmt-open-immersion-affine-factorization"]
+++
Let $f\colon X\to Y$ be separated, quasi-compact, locally quasi-finite and
locally of finite type, and suppose $Y$ is quasi-affine. Then $X$ is
quasi-affine.

## Proof

Write $f=g\circ j$ with $j\colon X\to W$ an open immersion and $g\colon W\to Y$ affine, using
[lemma-nagata-zmt-open-immersion-affine-factorization]. An affine
morphism to a quasi-affine scheme has quasi-affine source, so $W$ is
quasi-affine. Moreover $X$ is quasi-compact, since $f$ is quasi-compact and
$Y$ is quasi-compact. So $X$ is a quasi-compact locally closed subscheme of
the quasi-affine scheme $W$, and such a subscheme is quasi-affine (Stacks Tag
0BCK).
