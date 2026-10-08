+++
id = "prop-nagata-noetherian-inverse-system"
kind = "theorem"
title = "[stacks-project]"
order = 344
lean = ["AlgebraicGeometry.Scheme.nonempty_noetherianApproximation"]
tags = ["latex:proposition"]
uses = ["def-nagata-glued-limit-comparison", "def-nagata-noetherian-inverse-system", "lemma-nagata-affine-finite-type-is-quasi-affine", "lemma-nagata-glue-noetherian-stage", "lemma-nagata-noetherian-inverse-system-affine", "lemma-nagata-valid-refinements-directed"]
+++
Every quasi-compact quasi-separated scheme $S$ admits a Noetherian
approximation. Concretely, the constructed system $\mathsf N(S)$ has affine
transition morphisms, every term is of finite type over $\mathbf Z$, and
$\kappa_S$ identifies $S$ with its inverse limit.

## Proof

Nonemptiness and directedness of the index type, including the transition
identities, are supplied by
[lemma-nagata-valid-refinements-directed]. By
[lemma-nagata-glue-noetherian-stage], every chart of every $S_\lambda$
is the spectrum of a finitely generated $\mathbf Z$-algebra and every
transition is affine. Such rings are Noetherian, so the glued schemes are
Noetherian. On a selected affine chart $\operatorname{Spec}(A)$ of $S$,
the chart rings $A_\lambda$ form a filtered system whose colimit is $A$ by
the finite-subalgebra lemma; the affine inverse-limit calculation therefore
identifies $\varprojlim\operatorname{Spec}(A_\lambda)$ with
$\operatorname{Spec}(A)$. The identifications commute with restriction to
every recorded basic overlap because all transition maps are induced by the
same localization maps in $A$. Since the affine charts and overlaps are
finite, these local inverses glue and are inverse to the comparison
$\kappa_S$ of [def-nagata-glued-limit-comparison]. Hence $\kappa_S$ is
an isomorphism and all asserted properties hold.
