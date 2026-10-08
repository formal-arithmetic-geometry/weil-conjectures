+++
id = "lemma-nagata-affine-blowup-complement"
kind = "lemma"
title = "Affine complement-of-center isomorphism"
order = 58
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.isIso_blowupMap_restrict_of_ideal_eq_top"]
uses = ["def-nagata-affine-blowup", "def-nagata-affine-blowup-restriction-map", "def-nagata-affine-proj", "def-nagata-global-blowup", "def-nagata-global-blowup-glue-data", "def-nagata-global-blowup-local-model", "def-nagata-global-blowup-overlap-basic-map", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-rees-algebra", "def-nagata-rees-localization-map", "def-nagata-rees-piece", "lemma-nagata-affine-blowup-restrict-cocycle", "lemma-nagata-affine-blowup-top", "lemma-nagata-global-blowup-overlap-basic", "lemma-nagata-localization-ideal-pow", "lemma-nagata-rees-degree-zero", "lemma-nagata-rees-piece-membership", "lemma-nagata-rees-piece-mul", "prop-nagata-affine-blowup-restrict", "prop-nagata-global-blowup-cover-independent", "prop-nagata-rees-graded"]
+++
For $Z=V(I)\subseteq\operatorname{Spec}(A)$, the affine blow-up morphism
restricts to an isomorphism over $\operatorname{Spec}(A)\setminus Z$.

## Proof

The complement is covered by the basic opens $D(a)$, $a\in I$. On $D(a)$
the localized ideal is the unit ideal, so
[prop-nagata-affine-blowup-restrict] and
[lemma-nagata-affine-blowup-top] identify the blow-up with $D(a)$.
The identifications agree on overlaps by
[lemma-nagata-affine-blowup-restrict-cocycle], and hence glue.
