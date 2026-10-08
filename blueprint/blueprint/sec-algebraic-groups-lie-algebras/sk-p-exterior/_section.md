+++
id = "sk-p-exterior"
kind = "section"
title = "Exterior-power weights"
order = 2560
uses = ["sk-d-linear", "sk-d-monodromy", "sk-d-weights", "sk-i-restriction", "sk-p-central", "sk-p-linear-filtration", "sk-p-linear-spectra", "sk-p-readout"]
lean = ["Representation.exists_multiset_le_and_detWeight_eq_sum_of_exteriorPower"]
+++
*Proposition (sketch).*

Fix a real weight character $\lambda$.
Let $V\ne0$ be a semisimple representation of a
degree datum, of rank $r$, and let $1\le s\le r$.
Assume its simple summands and all simple constituents of
$\bigwedge^s V$ have finite geometric determinant.
If $a_1,\ldots,a_r$ is its rank-counted weight list, every simple
constituent $Q$ of $\bigwedge^s V$ satisfies

$$
\dw_\lambda(Q)=a_{i_1}+\cdots+a_{i_s}
\quad\text{for some }1\le i_1<\cdots<i_s\le r.
$$

## Proof

Choose a central pair for $V$ by [sk-p-central], and a basis within
each simple summand. By [sk-p-readout], $z$ is diagonal in this basis
with entries $c_i$ satisfying $\lambda(c_i)=Na_i$, where repetitions
follow [sk-d-weights]. Its exterior eigenvalues are the products
$c_{i_1}\cdots c_{i_s}$ by [sk-p-linear-spectra]. By [sk-i-restriction],
$Q$ is rational for the same group, and by [sk-p-readout], $z$ acts
on it as a scalar $c_Q$. By [sk-p-linear-filtration], this is an ambient exterior
eigenvalue, so equals one of those products. Apply [sk-p-readout]
and additivity in [sk-d-weights] to obtain the formula.

Uses: [sk-d-linear], [sk-d-monodromy], [sk-d-weights], [sk-i-restriction], [sk-p-central], [sk-p-linear-filtration], [sk-p-linear-spectra], [sk-p-readout]
