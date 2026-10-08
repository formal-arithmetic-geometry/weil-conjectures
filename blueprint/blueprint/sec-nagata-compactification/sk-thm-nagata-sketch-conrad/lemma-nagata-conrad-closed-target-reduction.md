+++
id = "lemma-nagata-conrad-closed-target-reduction"
kind = "lemma"
title = "Reduction to a closed subscheme of the target"
order = 219
lean = ["AlgebraicGeometry.exists_isAdmissible_extend_partialSection_of_isClosedImmersion"]
uses = ["def-nagata-admissible-blowup", "def-nagata-conrad-quasi-domination", "def-nagata-global-blowup", "prop-nagata-global-blowup-cover-independent"]
+++
Let $i\colon Y'\hookrightarrow Y$ be a closed immersion of $X$-schemes and
suppose the section $f\colon U\to Y$ factors as $f=i\circ f'$ through $Y'$.
If the conclusion of [thm-nagata-conrad-elimination] holds for the data
$(X,U,V,Y'\to X,f')$, then it holds for $(X,U,V,p,f)$, with the same
admissible blow-up and the same open subscheme of it.

## Proof

The extension of $f$ is the extension $g\colon W\to Y'$ of $f'$ followed by
$i$; it is a section of $p$ over $W$ and extends $f$ because $i$ is a
morphism over $X$. The comparison morphism
$Y'\times_XX'\to Y\times_XX'$ is a base change of $i$, hence again a closed
immersion, and the graph of $i\circ g$ is the image of the graph of $g$ under
it. A closed immersion is a closed map, so that image is closed.
