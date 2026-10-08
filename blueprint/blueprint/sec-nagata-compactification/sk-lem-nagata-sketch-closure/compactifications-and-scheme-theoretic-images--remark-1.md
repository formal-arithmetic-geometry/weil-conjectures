+++
id = "compactifications-and-scheme-theoretic-images--remark-1"
kind = "remark"
title = "Formalization route"
order = 66
+++
The formal proof (`Nagata.schemeImageFlatBaseChange`) does not run
the affine kernel computations of
[lemma-nagata-dense-flat-pullback] and
[lemma-nagata-dense-flat-pullback]: it factors the base-changed
morphism through $\operatorname{SIm}(g)\times_YY'$ and applies Mathlib's
`IsSchemeTheoreticallyDominant.of_isPullback`, which encapsulates
those computations. Only quasi-compactness of $g$ is needed, and
[lemma-nagata-scheme-image-restrict-open] is obtained in Lean as the
special case of flat base change along an open immersion, reversing the
order of these two lemmas.
