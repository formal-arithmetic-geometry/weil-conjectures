+++
id = "lem-kun-functor-preserves-hocolim"
kind = "lemma"
title = "Exact coproduct-preserving functors preserve telescopes"
order = 1721
uses = ["def-kun-truncations", "def-weil-pbc-derived-categories"]
+++
Let $\mathcal T,\mathcal T'$ be triangulated categories with
countable coproducts. If an exact functor
$F:\mathcal T\to\mathcal T'$ preserves countable coproducts, then
for every sequence $(E_N)$ the canonical morphism
$\operatorname{hocolim}_NF(E_N)\to F(\operatorname{hocolim}_NE_N)$
is an isomorphism.

## Proof

Apply $F$ to the distinguished triangle of
[def-kun-truncations] defining $\operatorname{hocolim}_NE_N$;
exactness makes the image of the triangle distinguished, and
preservation of countable coproducts identifies it with the
distinguished triangle defining
$\operatorname{hocolim}_NF(E_N)$, which determines the hocolim up to
canonical isomorphism.
