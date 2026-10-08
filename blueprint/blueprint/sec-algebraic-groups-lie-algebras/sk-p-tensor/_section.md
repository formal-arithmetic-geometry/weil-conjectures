+++
id = "sk-p-tensor"
kind = "section"
title = "Tensor-product weights"
order = 2558
uses = ["sk-d-linear", "sk-d-monodromy", "sk-d-weights", "sk-i-restriction", "sk-p-central", "sk-p-readout", "sk-r-linear-library"]
lean = ["Representation.exists_detWeight_eq_add_of_subquotient_tprod"]
+++
*Proposition (sketch).*

Fix a real weight character $\lambda$.
Let $V,E$ be representations of the same
degree datum, with chosen composition series
having simple quotients $V_i,E_j$. Assume these quotients and all
simple constituents of $V\otimes E$ have
finite geometric determinant. For every
constituent $Q$ of $V\otimes E$, some pair $(i,j)$ satisfies

$$
\dw_\lambda(Q)=\dw_\lambda(V_i)+\dw_\lambda(E_j).
$$

## Proof

By the tensor-filtration statement of r:linear-library, $Q$ is a
subquotient of some $V_i\otimes E_j$. Apply [sk-p-central] to the
semisimple representation $V_i\oplus E_j$ and its own monodromy group.
The tensor action and its subquotient $Q$ are rational for this same
group by [sk-i-restriction]. By [sk-p-readout], its central pair
$(N,z)$ acts on the two summands by scalars $c_i,d_j$, with
$\lambda(c_i)=N\dw_\lambda(V_i)$ and
$\lambda(d_j)=N\dw_\lambda(E_j)$. It acts on $Q$ as $c_i d_j$.
Applying [sk-p-readout] again and the multiplicative-to-additive rule
of [sk-d-weights] proves the formula. Neither $V,E$ nor the tensor
product is assumed semisimple.

Uses: [sk-d-linear], [sk-d-monodromy], [sk-d-weights], [sk-i-restriction], [sk-p-central], [sk-p-readout], [sk-r-linear-library]
