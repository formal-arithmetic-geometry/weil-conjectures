+++
id = "lemma-nagata-ext-scheme-theoretically-dominant-separated"
kind = "lemma"
title = "Morphisms into a separated target agreeing on a scheme-theoretically dominant subscheme"
order = 211
lean = ["AlgebraicGeometry.ext_of_isSchemeTheoreticallyDominant_of_isSeparated", "AlgebraicGeometry.ext_of_isSchemeTheoreticallyDominant_of_isSeparated'"]
uses = ["def-nagata-dense-compactification", "def-nagata-scheme-theoretically-dense-open"]
+++
Let $s\colon Y\to Z$ be separated and let $f,g\colon T\to Y$ satisfy
$s\circ f=s\circ g$. If $\iota\colon W\to T$ is scheme-theoretically
dominant and $f\circ\iota=g\circ\iota$, then $f=g$. In particular two
$Z$-morphisms $T\to Y$ into a separated $Z$-scheme $Y$ that agree on a
scheme-theoretically dense open of $T$ are equal.

No reducedness of $T$ is needed: this is the scheme-theoretic analogue of the
classical statement for a dominant $\iota$ and reduced $T$.

## Proof

Passing to $Z$-schemes, the equalizer $E$ of $f$ and $g$ maps to $T$ by a
closed immersion $e$ because $s$ is separated. As $f\circ\iota=g\circ\iota$,
the morphism $\iota$ factors as $\iota=e\circ l$, so the kernel ideal of $e$
is contained in that of $\iota$, which is trivial by scheme-theoretic
dominance. A closed immersion with trivial kernel is an isomorphism, hence
$e$ is an epimorphism and $f=g$ follows from $f\circ e=g\circ e$.
