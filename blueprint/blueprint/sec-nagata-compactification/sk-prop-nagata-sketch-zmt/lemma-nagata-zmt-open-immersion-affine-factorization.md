+++
id = "lemma-nagata-zmt-open-immersion-affine-factorization"
kind = "lemma"
title = "Zariski's Main Theorem as a factorization"
order = 183
lean = ["AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isAffineHom_of_locallyQuasiFinite"]
+++
Let $f\colon X\to Y$ be separated, quasi-compact, locally quasi-finite and
locally of finite type. Then $f$ factors as

$$
X\xrightarrow{\;j\;}W\xrightarrow{\;g\;}Y,\qquad g\circ j=f,
$$

with $j$ an open immersion and $g$ an affine morphism.

## Proof

This is Grothendieck's form of Zariski's Main Theorem, available in Mathlib
as `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`. Take $W$ to
be the relative normalization of $Y$ in $X$, $j$ the canonical morphism
$X\to W$ and $g$ the structure morphism $W\to Y$. Zariski's Main Theorem
says that $j$ is an open immersion under exactly these hypotheses, and $g$ is
integral, hence affine, by construction of the relative normalization.
