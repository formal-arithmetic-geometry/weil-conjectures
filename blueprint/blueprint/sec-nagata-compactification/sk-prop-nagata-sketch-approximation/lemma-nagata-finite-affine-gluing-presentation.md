+++
id = "lemma-nagata-finite-affine-gluing-presentation"
kind = "lemma"
title = "Properties of the selected finite affine presentation"
order = 333
uses = ["def-nagata-finite-affine-gluing-presentation"]
+++
**Status.** Bypassed by the formalized route: the finite-presentation and
Noetherian descent is done in one step by
`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated`
and `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation`, so
this stage-by-stage bookkeeping is never carried out.

Every overlap in $\mathsf G_S$ is quasi-compact and represented by finitely
many basic affine opens, all gluing identities form finite lists, and
gluing $\mathsf G_S$ recovers $S$.

## Proof

Quasi-compactness gives the finite affine cover. Quasi-separatedness makes
each pairwise intersection quasi-compact, hence finitely affine-covered.
A quasi-compact open in an affine scheme is a finite union of basic opens.
There are finitely many pairs and triples, so all recorded equations form a
finite list. The recovery assertion is the ordinary gluing theorem applied
to the restrictions of the original scheme.
