+++
id = "lemma-constructible-immersion-independence"
kind = "lemma"
title = "Independence of the scheme structure"
order = 1169
lean = ["AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.upperStar_of_range_subset", "AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_upperStar_iff_of_range_eq"]
uses = ["def-constructible-finite-locally-constant", "lemma-constructible-iso-invariance", "lemma-constructible-pullback-stratification", "lemma-constructible-universal-homeomorphism-invariance", "prop-constructible-pullback"]
+++
Let $a\colon Z\to X$ and $b\colon Z'\to X$ be immersions with the same
image. Then $a^*\mathcal F$ is finite locally constant if and only if
$b^*\mathcal F$ is.

## Proof

Let $W=Z\times_XZ'$ with projections $p\colon W\to Z$ and $q\colon W\to Z'$.
The projection $p$ is an immersion, as a base change of $b$, and it is
surjective, its image being $a^{-1}(b(Z'))=a^{-1}(a(Z))=Z$. A surjective
immersion is a surjective closed immersion (an immersion is a closed
immersion into an open subscheme, and surjectivity forces that open to be
everything), hence a universal homeomorphism. The same holds for $q$. Now
$p^*a^*\mathcal F\cong q^*b^*\mathcal F$, both being the pullback along
$a\circ p=b\circ q$, so by
[lemma-constructible-universal-homeomorphism-invariance] applied to
$p$ and to $q$, $a^*\mathcal F$ is finite locally constant if and only if
$p^*a^*\mathcal F$ is, if and only if $q^*b^*\mathcal F$ is, if and only if
$b^*\mathcal F$ is.
