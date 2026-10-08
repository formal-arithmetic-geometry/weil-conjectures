+++
id = "lemma-nagata-finite-presentation-descends"
kind = "lemma"
title = "Property of finite-presentation descent, [stacks-project]"
order = 363
lean = ["AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation"]
uses = ["def-nagata-finite-presentation-descent", "lemma-nagata-affine-finite-type-is-quasi-affine", "lemma-nagata-relative-gluing-axioms-eventually", "lemma-nagata-relative-gluing-datum-descends"]
+++
The constructed
$X^{\mathrm{desc}}_{\lambda_{\mathrm{rel}}}\to S_{\lambda_{\mathrm{rel}}}$ is of finite presentation, and
$\epsilon_X$ is an isomorphism over $S$.

## Proof

Use the affine gluing theorem in the following explicit form: a finite
family of affine schemes $T_a=\operatorname{Spec}(A_a)$, quasi-compact open
subspaces $T_{ab}\subseteq T_a$, and inverse overlap isomorphisms satisfying
the triple cocycle glue to a scheme $T$; the canonical maps $T_a\to T$ are
open immersions covering $T$, and any morphisms of such finite data glue
uniquely. Apply this theorem to
$\mathsf R_{X,\lambda_{\mathrm{rel}}}$, whose hypotheses are exactly
[lemma-nagata-relative-gluing-axioms-eventually]. Each chart algebra
is finitely presented over its Noetherian base chart, hence the resulting
morphism to $S_{\lambda_{\mathrm{rel}}}$ is of finite presentation (finite
affine cover and finite overlap cover preserve finite presentation).

Base change the entire finite diagram along
$S\to S_{\lambda_{\mathrm{rel}}}$. Fibre products preserve affine charts,
localizations, and the recorded overlap isomorphisms, so the base-changed
datum is canonically the original datum $\mathsf R_X$ by
[lemma-nagata-relative-gluing-datum-descends]. The chartwise
comparison isomorphisms agree on overlaps because the inverse and cocycle
equations hold; uniqueness in the gluing theorem therefore produces a
global morphism $\epsilon_X$. Gluing the inverse chartwise maps gives an
inverse to $\epsilon_X$, with both composites checked on the open affine
cover. Thus $\epsilon_X$ is an isomorphism.
