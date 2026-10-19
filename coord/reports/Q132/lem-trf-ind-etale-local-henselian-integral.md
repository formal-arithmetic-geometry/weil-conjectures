## Worker report

The delivery adds `Algebra.IsHenselizationAtPrime`, encoding the local henselization universal property from Stacks Tags 04GN and 04GQ, and states `RingHom.indEtale_local_henselian_integral`. The theorem binds commutative rings `A,D`, a ring map `f`, the henselian-local structure on `D`, ind-etaleness of `f`, a prime `p` identified with the contraction of the maximal ideal, a henselian local `Aₚ`-algebra `H`, and the henselization property `hH`. Its conclusion is the unique local map `h : H →+* D` whose composite with `A → Aₚ → H` is `f`, together with `RingHom.IsIntegral h` (every element of `D` satisfies a monic polynomial over `H`). The proof is `sorry` as required.

The definition renders the universal property clause by clause: `IsLocalHom (algebraMap (Localization.AtPrime p) H)` is locality of the structural map; the quantified `T`, `g`, and `IsLocalHom g` are arbitrary henselian local targets and local maps; `∃! h` gives the unique local extension and the displayed composition equality.

Dependencies used are Mathlib `Localization.AtPrime`, Mathlib/WeilConjectures `HenselianLocalRing`, and upstream `RingHom.IndEtale` from `WeilConjectures.RingTheory.ProEtale.IndEtale`. The new definition is imported by the theorem module.

Edge cases checked: arbitrary prime ideals (including zero and maximal primes), fields as henselian local rings, zero-degree monic polynomials in the integral predicate, and filtered presentations with noninjective transition maps are all permitted by the declarations used. No Noetherian or finiteness hypothesis is added.

Searches: `msearch.py leanfinder "universal property henselization local ring"` found only `HenselianLocalRing` and TFAE results; `msearch.py loogle "HenselianLocalRing IsLocalHom RingHom"` found no match; grep for `IsHenselizationAtPrime` in Mathlib, WeilConjectures, and `lean/Sheaf` found no match. Searches for the theorem's integrality statement likewise found no exact declaration; existing `Algebra.IndEtale` and `HenselianLocalRing` declarations were read and reused.

## Second reading by Q132

The second reading checked the node and both modules. Every source hypothesis is represented: `f`, henselian-local `D`, ind-etale `hind`, the contracted prime `hp`, and henselization property `hH`. The conclusion's factorization equation and integrality clause are explicit, and no Noetherian assumption occurs. The helper definition states exactly the local-map initial property used by the source sentence.

## New nodes

`def-weil-pbc-henselization-at-prime` is a new definition node because no Mathlib, upstream, or project declaration supplies the ordinary henselization universal-property predicate. It is sourced from Stacks Tags 04GN and 04GQ, and its module provides the concrete Prop definition used by the theorem.
