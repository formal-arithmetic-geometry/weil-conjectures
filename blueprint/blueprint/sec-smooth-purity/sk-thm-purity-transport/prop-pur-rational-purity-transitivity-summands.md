+++
id = "prop-pur-rational-purity-transitivity-summands"
kind = "theorem"
title = "Transitivity and summand preservation of rational purity"
order = 2025
tags = ["latex:proposition"]
uses = ["prop-pur-smooth-purity-naturality-cover", "prop-weil-pbc-descent-functors", "prop-weil-pbc-rational-transport", "thm-weil-pbc-idempotent-complete-triangulation"]
+++
The purity isomorphisms of
[thm-pur-rational-and-qbar-purity] are transitive in coefficient
extensions, and preserve idempotent summands (via
[thm-weil-pbc-idempotent-complete-triangulation] and the descent
functors of [prop-weil-pbc-descent-functors]).

## Proof

Two lattices of the same $E$-object are related by inverting a
denominator, and the two purity isomorphisms differ by the
corresponding unit ([prop-weil-pbc-rational-transport]); a finite
extension $E'\supset E$ is flat, and the transport is the tensor with
$E'$, giving the transitivity. The independence from the finite stage
and from the particular presentation is the independence of the descent
functors of [prop-weil-pbc-descent-functors] and the idempotent
completeness of [thm-weil-pbc-idempotent-complete-triangulation]
(the purity isomorphism is natural in the object by [prop-pur-smooth-purity-naturality-cover], hence commutes with
the descent from a finite stage and with the extension of the
coefficient field).
