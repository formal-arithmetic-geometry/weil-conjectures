+++
id = "sk-i-additivity"
kind = "section"
title = "Localization trace additivity"
order = 2351
uses = ["sk-d-curve-pieces", "sk-d-integral", "sk-d-local-term", "sk-d-trace-class"]
lean = ["AlgebraicGeometry.ProEtale.GeometricOperations.traceClass_graph_eq_traceClass_add_traceClass"]
+++
*Proposition (sketch).*

For the curve coefficient pieces, the
trace classes satisfy

$$
\Tr_{(1,\Phi_m)}(\varphi_m)=\Tr_{(1,\Phi_m)}(u^Z)+\Tr_{(1,\Phi_m)}(u^U).
$$

The same holds for the arbitrary coefficient morphisms of [sk-d-weil];
invertibility is not required.

## Proof

The three coefficient morphisms form a morphism of the distinguished
triangle attached to the open–closed decomposition, compatibly with the
two functors $Lc_2^*$ and $Rc_1^!$. Triangle compatibility of the trace
class then gives the identity for the classes themselves, in the group of
maps $A_F\to\omega_F$ on the fixed scheme. Since the fixed scheme is proper
with finitely many clopen components and integration is $A$-linear by
[sk-d-integral], the identity descends to the
local terms component by component. No
invertibility of the coefficient morphisms is used: only exactness and the
formal laws of the trace enter.

Uses: [sk-d-curve-pieces], [sk-d-integral], [sk-d-local-term], [sk-d-trace-class]
