+++
id = "lem-exc-residue-tor-test"
kind = "lemma"
title = "Testing finite Tor amplitude at the residue field"
order = 1823
uses = ["def-weil-derived-tensor", "def-weil-finite-tor-amplitude", "def-weil-pbc-constructible-complexes", "def-weil-pbc-derived-categories", "lemma-weil-pbc-geometric-stalk-conservative"]
+++
Let $A=\mathcal O_E/\varpi_E^n$, let $\kappa=A/(\varpi_E)$,
and let $K$ be a bounded complex with
constructible cohomology
on a small etale site. Then $K$ has
Tor amplitude in $[a,b]$
if and only if its
derived tensor product
$K\otimes_A^L\kappa$ has cohomology in $[a,b]$.
The derived category is the ordinary one of
[def-weil-pbc-derived-categories].

## Proof

One direction is the definition in [def-weil-finite-tor-amplitude],
with the constant sheaf $\kappa$ as test module.
For the converse, take any geometric stalk. It is a bounded complex
with finitely generated cohomology over the Artinian local ring $A$.
The elementary minimal-resolution construction gives a bounded-above
complex of finite free modules representing it, with every differential
having entries in the maximal ideal. To obtain this construction, take
finite free covers of successive kernels and cancel any invertible matrix
entry, which splits off a contractible two-term free summand.
After tensoring with $\kappa$, all differentials of this minimal
complex are zero. Hence the assumed vanishing and Nakayama's lemma
force all its terms outside $[a,b]$ to be zero. Each stalk thus has
a finite free representative in this same interval.

For an arbitrary module sheaf $M$, stalks commute with the derived
tensor product of [def-weil-derived-tensor], since they are exact
tensor functors preserving flat resolutions. The stalk of
$K\otimes_A^L M$ is consequently zero outside $[a,b]$.
Conservativity in [lemma-weil-pbc-geometric-stalk-conservative]
proves the required uniform sheafwise Tor bound. This proof applies
to etale stalks; it does not assert their conservativity on the entire
pro-etale topos.
