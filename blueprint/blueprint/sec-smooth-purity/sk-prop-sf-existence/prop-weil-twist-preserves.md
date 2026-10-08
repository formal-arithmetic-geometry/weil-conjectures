+++
id = "prop-weil-twist-preserves"
kind = "theorem"
title = "Twists preserve finiteness conditions"
order = 1802
tags = ["latex:proposition"]
uses = ["def-coefficient-twists-detailed", "def-weil-derived-tensor", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-pbc-proetale-site"]
+++
In the notation of
[def-coefficient-twists-detailed], each $\Lambda(m)$ is an
invertible locally
constant rank-one sheaf, and twisting $K\mapsto K(m)$ preserves
bounded constructibility
and the finite Tor amplitude
condition (being the derived tensor product with an invertible sheaf).

## Proof

By [def-coefficient-twists-detailed], $\Lambda(1)_S$ is built from the
pro-etale sheaf $\mu_{\ell^r,S}$, which is locally constant of rank one
with finite stalks, by tensor products and scalar extension, and the
twists $\Lambda(m)$ are tensor powers and internal Homs of
$\Lambda(1)_S$. Hence each $\Lambda(m)$ is an invertible locally
constant rank-one sheaf, and such a sheaf is flat with Tor amplitude
$[0,0]$. For an invertible locally constant rank-one $L$, the spectral
sequence for the derived tensor product of [def-weil-derived-tensor]
collapses to $\mathcal H^r(K\otimes^L_{\Lambda_S}L)\cong \mathcal H^r(K)\otimes_{\Lambda_S}L$: tensoring with the locally constant
rank-one $L$ preserves the finite partitions and locally constant
finite stalks of the constructibility condition of
[def-weil-finite-torsion-constructibility] levelwise, and it
preserves the vanishing interval of the finite Tor amplitude condition of
[def-weil-finite-tor-amplitude], because $L$ is flat and the
tensor products with $L$ and with the dual line are mutually inverse.
The integral and $\Qlb$-twists are obtained from the same statement
levelwise modulo $\varpi_E^n$ and at the common finite stages,
for every coefficient ring.
