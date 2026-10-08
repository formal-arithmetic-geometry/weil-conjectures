+++
id = "lemma-nagata-admissible-blowup-comp"
kind = "lemma"
title = "Composition of admissible blow-ups, [stacks-project]"
order = 162
lean = ["AlgebraicGeometry.IsAdmissible.exists_comp"]
uses = ["def-nagata-admissible-blowup", "def-nagata-composition-of-blowups-comparison", "def-nagata-global-blowup", "lemma-nagata-admissible-blowup-over-open", "lemma-nagata-composition-center-ideal", "lemma-nagata-composition-extended-ideal-equality", "prop-nagata-global-blowup-cover-independent", "thm-nagata-composition-of-blowups"]
+++
Let $X$ be quasi-compact and quasi-separated and let $U\subseteq X$ be
quasi-compact. A composition of two $U$-admissible blow-ups is a
$U$-admissible blow-up. The chosen isomorphism over $U$ is the composite of
the chosen pullback isomorphisms.

## Proof

Apply [thm-nagata-composition-of-blowups]. It writes the composite as
the blow-up of a finite-presentation center $Y\hookrightarrow X$ whose
support is the union of the first center and the image of the second center.
Both sets are disjoint from $U$, because the first blow-up is the identity
over $U$ by [lemma-nagata-admissible-blowup-over-open], and the second
center is disjoint from its inverse image. Thus $Y\cap U=\varnothing$,
equivalently its defining ideal restricts to the unit ideal on $U$, so the
resulting blow-up is $U$-admissible. The isomorphism supplied by the
composition theorem is over $X$. Pulling it back to $U$ identifies the
composite with the composite of the two specified pullback isomorphisms;
the equality follows after composing with the structure maps, where it is
the associativity equality for fibre products.
