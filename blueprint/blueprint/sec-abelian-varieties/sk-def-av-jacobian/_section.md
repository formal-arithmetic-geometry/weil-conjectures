+++
id = "sk-def-av-jacobian"
kind = "section"
title = "The Jacobian"
lean = ["AlgebraicGeometry.IsJacobian"]
order = 446
uses = ["sec-nagata-compactification", "sk-def-av", "sk-def-av-pic", "sk-def-curve"]
+++
*Definition (sketch).*

Let $C$ be a smooth projective geometrically integral curve over $k$,
of genus $g$. A *Jacobian of $C$* is a pair $(J,\varphi)$
consisting of an abelian variety $J$ over $k$ of dimension $g$
together with an isomorphism of group-valued functors
$\varphi:\Pic^0_{C/k}\xrightarrow{\sim}h_J$ on
$(\mathrm{Sch}/k)$, where $\Pic^0_{C/k}$ is the degree-zero part of
the relative Picard functor; that is, $J$ represents $\Pic^0_{C/k}$ in
the category of abelian varieties of dimension $g$ over $k$. Whether
such a pair exists is a theorem, proved later in [sk-prop-jacobian]
and [sk-prop-jacobian-descent] of [sec-picard-framework], and is
not part of this definition.
