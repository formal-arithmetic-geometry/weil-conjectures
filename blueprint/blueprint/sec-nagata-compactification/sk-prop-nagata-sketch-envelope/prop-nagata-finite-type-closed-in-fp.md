+++
id = "prop-nagata-finite-type-closed-in-fp"
kind = "theorem"
title = "Properties of the separated finite-presentation envelope, [stacks-project]"
order = 397
lean = ["AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_isSeparated_locallyOfFinitePresentation"]
tags = ["latex:proposition"]
uses = ["def-nagata-finite-type-closed-in-fp", "def-nagata-finite-type-fp-model-system", "lemma-nagata-finite-type-fp-model-system", "lemma-nagata-fixed-base-separated-eventually", "lemma-nagata-fixed-base-separated-stage-exists"]
+++
The constructed morphism $X^{\mathrm{fp}}\to S$ is separated and of
finite presentation, and the constructed map
$i^{\mathrm{fp}}_{X/S}\colon X\to X^{\mathrm{fp}}$ is a closed immersion
over $S$.

## Proof

A finite-type morphism over a quasi-compact base has quasi-compact source,
and separatedness makes that source quasi-separated, so the model system is
available. Its property lemma makes every term finite presentation and
every structural map $i_\alpha$ a closed immersion. At the explicitly
selected stage $\alpha^{X/S}_{\mathrm{sep}}$, separatedness follows from
[lemma-nagata-fixed-base-separated-eventually]. These are exactly the
three assertions for the named envelope.
