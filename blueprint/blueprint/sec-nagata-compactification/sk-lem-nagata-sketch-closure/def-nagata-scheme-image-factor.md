+++
id = "def-nagata-scheme-image-factor"
kind = "definition"
title = "Canonical factor through a scheme-theoretic image"
order = 68
lean = ["AlgebraicGeometry.Scheme.Hom.toImage"]
uses = ["def-nagata-scheme-theoretic-closure", "def-nagata-scheme-theoretic-image", "lemma-nagata-scheme-image-ideal-qc"]
+++
Define

$$
g^{\mathrm{im}}\colon T\longrightarrow\operatorname{SIm}(g)
$$

to be `Scheme.Hom.toImage g`. Its factorization equality is the
verified theorem `Scheme.Hom.toImage_imageι`.
