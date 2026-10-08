+++
id = "sk-prop-well-defined"
kind = "section"
title = "P2: the transform is an exact triangulated functor"
order = 2696
lean = ["AlgebraicGeometry.Etale.boundedConstructible_fourierTransform_obj_of_boundedConstructible", "AlgebraicGeometry.Etale.fourierTransformBoundedConstructible"]
uses = ["sk-def-ft", "sk-prop-kernel-lisse"]
+++
*Proposition (sketch).*

For every $K\in\Dbc(V,E)$ one has $\FT_\psi(K)\in\Dbc(V^\vee,E)$, and
$\FT_\psi:\Dbc(V,E)\to\Dbc(V^\vee,E)$ is an exact triangulated functor.
(Blueprint thm:fd-transform-well-defined.)

## Proof

By P1 the kernel is lisse of rank one, hence of finite Tor amplitude, so
$p_1^*K\otimes^L\mathcal K_\psi\in\Dbc(V\times_SV^\vee,E)$. By the
six-operations package prop:functor-package the derived pullback, the
derived tensor product and the compact-support direct image along the
separated finite-type $p_2$ are exact triangulated functors on their
constructible and finite-Tor domains, and they preserve bounded
constructible objects; the shift $[r]$ does too.

Uses: [sk-def-ft], [sk-prop-kernel-lisse]
