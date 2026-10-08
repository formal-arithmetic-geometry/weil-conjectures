+++
id = "lem-wf-tate-twist-compatibility"
kind = "lemma"
title = "Compatibility of the Tate twists"
order = 2572
uses = ["def-weil-pbc-proetale-site", "def-wf-tate-twist", "lem-wf-internal-hom-weil", "lem-wf-tensor-weil"]
+++
For every $m\in\mathbf Z$, the functorial pullback of roots of unity
gives a strict arrow
$\Phi_X^*E(1)\stackrel{\sim}{\to}E(1)$, and the Tate twist functor
$(-)(m)$ of [def-wf-tate-twist] commutes with finite scalar
extension.

## Proof

On $E(1)=\mathbf Z_\ell(1)\otimes_{\mathbf Z_\ell}E$ the pullback of
roots of unity is the limit of the canonical isomorphisms
$\Phi_X^*\mu_{\ell^n}\cong\mu_{\ell^n}$ (the $\ell$-power maps being
$\Phi_X$-equivariant), and the induced arrows for tensor products and
internal Homs give the cases $m>0$ and $m<0$ by
[lem-wf-tensor-weil] and [lem-wf-internal-hom-weil];
functoriality in $m$ and commutativity with finite scalar extension
follow from the same constructions being natural.
