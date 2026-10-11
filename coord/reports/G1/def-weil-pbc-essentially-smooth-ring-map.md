## Worker report

The module defines `Algebra.EssentiallySmooth R D`: there is a smooth commutative
`R`-algebra `P`, a multiplicative subset `S` of `P`, and an `R`-algebra
isomorphism from `D` to its localization at `S`. It contains no proof.

Clause mapping:

- The commutative rings `R` and `D` are `(R : Type u) (D : Type v)` with
  `[CommRing R] [CommRing D]`; the specified ring map is `[Algebra R D]`.
- The smooth commutative `R`-algebra is the existential `P`, `hP : CommRing P`,
  `hRP : Algebra R P`, and `Smooth R P`. `Algebra.Smooth` is the recorded
  declaration of `def-weil-pbc-smooth-ring-map` in
  `Mathlib.RingTheory.Smooth.Basic`.
- The multiplicative subset is `S : Submonoid P`, including one and closed
  under multiplication by the `Submonoid` structure.
- The fraction ring and its `R`-algebra structure are Mathlib's
  `Localization S` and its composite algebra map. Its fraction equality,
  addition, multiplication, and canonical map are the Mathlib localization
  operations. `Nonempty (D ≃ₐ[R] Localization S)` states the isomorphism
  of `R`-algebras without selecting one as definition data.
- Remarks (a) and (b) are expressly labelled consequences in the node,
  outside the definition. They are not silently assumed by the predicate.
  Remark (a) invokes `AlgebraicGeometry.Spec` from
  `Mathlib.AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Etale` from
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`; remark (b) invokes
  `Localization.AtPrime` from
  `Mathlib.RingTheory.Localization.AtPrime.Basic`. No declaration for
  these remarks is asserted or proved in this stage-2 definition module.

Edge cases: `S` can be `{1}`; `P` and `D` may be zero rings; there is no
Noetherian, characteristic, locality, or nonempty-prime assumption. The
universe for `P` is `max u v`, so both the base and target universes fit.

Searches for an existing notion:

- `msearch.py leanfinder` with “commutative R algebra is essentially smooth
  if it is isomorphic to a localization of a smooth R algebra”: eight
  results about smoothness of localizations, none defining this notion.
- `msearch.py loogle` with `Algebra.Smooth,
  Algebra.EssentiallySmooth, IsLocalization`: no hit for
  `Algebra.EssentiallySmooth`.
- `msearch.py grep` in `RingTheory` for
  `EssentiallySmooth|essentiallySmooth|EssSmooth|essentially smooth`:
  no hit.
- `rg` for those names in `WeilConjectures` and `lean/Sheaf`, and
  `grep -rn` for the node id in `WeilConjectures`: no hit.

The Stacks passage is Section 07FF, Lemmas 07FH and 07FI of
`smoothing.tex`; the model for the wording is Algebra, Definition 00QM.
The repository's `literature/stacks-project` is absent on this machine, so
the available copy at `/home/ubuntu/c1-stacks-review` was read.

## Second reading by G1

Independent comparison with the node and its Stacks source:

- Object `R`, a commutative ring: `(R : Type u) [CommRing R]`. Object `D`, a
  commutative `R`-algebra and specified map `R → D`: `(D : Type v)
  [CommRing D] [Algebra R D]`. Exact; neither field nor locality is required.
- Object `P`, a smooth commutative `R`-algebra: `∃ (P : Type (max u v))
  (hP : CommRing P)`, `∃ (hRP : Algebra R P)`, and `Smooth R P`, with the
  instances installed by the two `letI` binders. Exact. The recorded dependency
  `Algebra.Smooth` in `Mathlib.RingTheory.Smooth.Basic` is finite presentation
  plus formal smoothness; the latter gives projective Kähler differentials and
  vanishing first cotangent homology, matching the smoothness node.
- Object `S`, a multiplicative subset of `P`: `S : Submonoid P` includes `1`
  and is closed under multiplication. Exact. Mathlib's `Localization S` supplies
  the node's fractions, equality, operations and canonical algebra map.
- Conclusion `D ≅ S⁻¹P` as `R`-algebras: `Nonempty (D ≃ₐ[R] Localization S)`.
  Exact. `Nonempty` keeps the isomorphism existential; no choice is part of the
  data of the predicate. The conjunct and existential binders have the node's
  order: first smooth `P`, then `S`, then the isomorphism.
- Remark (a), smooth maps and consequently étale maps are essentially smooth:
  marked in the node as a consequence, not a condition of the definition. It is
  described in the declaration docstring, not imposed by the Lean predicate.
  The dependency nodes record `AlgebraicGeometry.Spec` and
  `AlgebraicGeometry.Etale`; their affine scheme notions are not substituted for
  the ring-map predicate here.
- Remark (b), a local `D` admits the same `P` localized at the contracted
  prime: likewise a consequence, described in the docstring rather than an
  extra conjunct. The localization-at-prime dependency records Mathlib's
  `Localization.AtPrime`; the defining clause uses arbitrary `Localization S`.

Edge cases: `{1}` is an allowed `S`, including an empty set of additional
denominators; a zero ring is allowed for `R`, `P`, or `D` by `CommRing`, subject
to the algebra maps and isomorphism. There is no nonzero, nonempty-spectrum,
Noetherian, characteristic, finite index, positive `n`, or local hypothesis.
`P : Type (max u v)` accommodates the universes of both `R` and `D`; a smooth
algebra is finitely presented, so its carrier can be represented in this
universe. The Stacks uses in 07FH and 07FI assume a characteristic-`p` field
and local Artinian rings for their *lemmas*, not for this general definition.

Independent searches: `msearch.py leanfinder` for "localization of a smooth
algebra at arbitrary multiplicative set" found localization smoothness lemmas,
no predicate for the node; `msearch.py loogle` for `Algebra.Smooth,
IsLocalization, Algebra.EssFiniteType` found no match; `msearch.py grep` for
`essentially smooth|EssentiallySmooth|EssSmooth|localization of a smooth`
found no match. `rg` for equivalent words in Mathlib's RingTheory,
`WeilConjectures`, and the project's `lean/Sheaf` found no existing definition.

Mismatch repaired: the original declaration docstring stated only the defining
clause, omitting the node's well-formedness step and both remark proofs. I
expanded it with those steps and their dependencies. No signature or defining
term changed; the node's `lean.statement` remains verbatim equal to the file's
signature. No other mismatch found.
