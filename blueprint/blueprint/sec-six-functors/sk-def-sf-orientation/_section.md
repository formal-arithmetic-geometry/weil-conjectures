+++
id = "sk-def-sf-orientation"
kind = "section"
title = "Orientation: an interface record"
order = 2046
lean = ["AlgebraicGeometry.Etale.Orientation", "AlgebraicGeometry.Etale.Orientation.nonempty_iso_dualizingComplex"]
+++
*Definition (sketch).*

An *orientation* for a smooth separated finite-type $f:X\to Y$ of pure
relative dimension $d$ is an isomorphism
$\gamma_{f,\Lambda_Y}:Lf^*\Lambda_Y(d)[2d]\xrightarrow{\sim}Rf^!\Lambda_Y$,
natural in $Y$ and compatible with composition, étale base change, finite
reduction, scalar extension and the pro-étale realization; for $f=a_X$ it
reads $\omega_{X,\Lambda}\cong\Lambda_X(d)[2d]$. In this blueprint the orientation is not an assumption: it is
constructed in this document as [sk-thm-smooth-purity]
(§[sec-smooth-purity]), with the tensor form and the base change for
$R^!$ in [sk-prop-cohsm] and the remaining coefficient stages in
[sk-thm-purity-transport].
