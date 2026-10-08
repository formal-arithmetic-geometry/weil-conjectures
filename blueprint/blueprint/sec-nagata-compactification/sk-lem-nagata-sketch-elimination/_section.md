+++
id = "sk-lem-nagata-sketch-elimination"
kind = "section"
title = "Elimination of indeterminacy"
order = 226
uses = ["sk-lem-nagata-sketch-blowups", "sk-thm-nagata-sketch-conrad"]
lean = ["AlgebraicGeometry.exists_admissibleBlowup_isOpenImmersion_strictTransformMap"]
+++
*Lemma (sketch).*

Let $q:Z\to X$ be separated and of finite type, with $X$ qcqs.
If $U\subseteq X$ is quasi-compact open and $q^{-1}(U)\simeq U$,
there is a $U$-admissible blow-up $X'\to X$ for which the strict
transform $Z'\to X'$ is an open immersion; see 081S.

## Proof

First blow up a finite-type ideal supported exactly on $X\setminus U$
so that $U$ becomes scheme-theoretically dense. Apply
[sk-thm-nagata-sketch-conrad] with $V=U$ to the section
$U\to Z$. Refine once more by a product with an ideal cutting out
$X\setminus U$. The strict transform is now exactly the
scheme-theoretic closure of the original section. The extended section
has closed graph $\Gamma_{f'}\simeq W$ containing $U$ schematically
densely, so this closure is $\Gamma_{f'}$. Hence $Z'\simeq W$ is open
in $X'$. This is the Deligne–Conrad route in the diagram; the
flattening route also recorded in the detailed chapter is not needed here.

Uses: [sk-lem-nagata-sketch-blowups], [sk-thm-nagata-sketch-conrad]
