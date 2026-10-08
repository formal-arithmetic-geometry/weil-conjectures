+++
id = "lemma-nagata-scheme-theoretic-closure-minimal"
kind = "lemma"
title = "Minimality of the scheme-theoretic closure"
order = 72
lean = ["AlgebraicGeometry.IsClosedImmersion.lift"]
uses = ["def-nagata-scheme-image-factor", "def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "lemma-nagata-scheme-image-ideal-qc", "lemma-nagata-scheme-image-of-closed-immersion", "lemma-nagata-scheme-image-universal"]
+++
The scheme-theoretic closure is the smallest closed subscheme of $Y$
through which $a$ factors: it factors through every such closed subscheme,
and the comparison is unique over $Y$.

## Proof

This is [lemma-nagata-scheme-image-universal] applied to the immersion
$a$, together with
[def-nagata-scheme-theoretic-closure].
