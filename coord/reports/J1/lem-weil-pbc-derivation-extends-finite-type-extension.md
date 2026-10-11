## Reviewer fix (R-dft0942, stage 2)

The delivered statement rendered the derivations as `D : R →+ R` with a separate Leibniz
hypothesis and `D' : R' →+ R'` with a Leibniz clause; the project's form for derivations
(H1 6e84ab55e `Derivation.exists_completion_and_unique_localization`, M1 450ec7334) is
Mathlib `Derivation ℤ R R`, one definition per notion (H4/H12). Fixed to
`D : Derivation ℤ R R` and `∃ D' : Derivation ℤ R' R'`. "R' of finite type over R" is now
`Algebra.FiniteType R R'` (was the equivalent `RingHom.FiniteType (algebraMap R R')`), and
"g is a nonzerodivisor in R'" is `algebraMap R R' g ∈ nonZeroDivisors R'` (was the
equivalent `IsRegular`). The docstring now carries the node's proof in words. Other
clauses (inclusion `hinj`, canonical map `IsLocalization.Away.map` bijective, conclusion
`D' (algebraMap r) = algebraMap (g ^ N * D r)`) unchanged.

## Worker report

The module states `RingTheory.derivation_extends_finite_type_extension` from Stacks
Tag 07PE. It binds commutative rings `R` and `R'`, an `R`-algebra structure,
finite type (`RingHom.FiniteType (algebraMap R R')`), injectivity of the inclusion,
a regular element `g` in `R'`, and bijectivity of the canonical localization map
`IsLocalization.Away.map`. The derivation `D` is an additive homomorphism `R →+ R`
with the Leibniz clause `hleibniz`. The conclusion gives `N : ℕ`, an additive map
`D' : R' →+ R'`, its Leibniz rule, and `D'(algebraMap r) = algebraMap (g^N * D r)`.

The dependency declaration is the Mathlib notion `RingHom.FiniteType`; no project
module is needed for the statement dependency. The localization map is Mathlib's
`IsLocalization.Away.map`.

Edge cases checked: `N = 0` is allowed; the finite generating set may be empty;
`g` is required regular in `R'`, which covers injectivity into the localization;
the inclusion is explicitly injective; arbitrary universe levels are bound.

Searches made: `msearch.py leanfinder` and `loogle` for derivation extension and
localization (no matching theorem); grep of Mathlib `RingTheory/Derivation` and
`RingTheory/Localization` (only localization and Kähler differential utilities,
no extension theorem); grep of `WeilConjectures` and `lean/Sheaf` (no matching
statement). The existing dependency node records Mathlib `RingHom.FiniteType`.
No statement dispute or node fault.

## Earlier second reading (a previous round; superseded)

The theorem signature matches each clause of the node: finite type, ring inclusion,
regular `g`, canonical localization bijection, additive Leibniz derivation, and the
existence of a power-scaled extension. The algebra-map expressions render the
inclusion and identify `g^N D(r)` in `R'` without adding hypotheses.

## Second reading by J1

I read the node statement, its Stacks source place (More on Algebra, Tag 07PE,
the final statement and the paragraph “Proof of the final statement”), and the
Lean declaration item by item.

* The objects `R`, `R'`, their commutative-ring structures, and the inclusion
  `R ⊆ R'` are rendered by `(R : Type u) (R' : Type v)`, `[CommRing R]`,
  `[CommRing R']`, `[Algebra R R']`, and
  `hinj : Function.Injective (algebraMap R R')`.  The universes are unrestricted.
* “Finite type over `R`” is exactly the dependency notion
  `hfinite : RingHom.FiniteType (algebraMap R R')` (Mathlib's finite-type ring
  hom), so the finite-generation hypothesis is present with no extra finiteness
  or Noetherian assumptions.
* The element `g ∈ R` and the source's regularity hypothesis in `R'` are
  `g : R` and `hreg : IsRegular ((algebraMap R R') g)`.  This is the required
  nonzerodivisor condition and does not require `g ≠ 0` separately.
* The source equality of localizations is rendered by bijectivity of the
  canonical map
  `IsLocalization.Away.map (Localization.Away g)
  (Localization.Away ((algebraMap R R') g)) (algebraMap R R') g`.
  Its domain and codomain are precisely the localizations at `g` and its image;
  no stronger isomorphism or chosen inverse is assumed.
* `D : R →+ R` and `hleibniz` render an additive derivation with exactly the
  source's Leibniz equation.  The conclusion's `∃ N : ℕ`, additive map
  `D' : R' →+ R'`, Leibniz equation on all `a b : R'`, and restriction equation
  `D'(algebraMap R R' r) = algebraMap R R' (g ^ N * D r)` all occur in the same
  quantifier order and with the same exponents.

No mismatch was found and no Lean or node change was needed.  Edge cases checked
are `N = 0`, an empty finite generating set, `g = 0` when allowed by regularity
(which rules it out in a nonzero target), zero rings, and arbitrary universe
levels.  The localization map remains the canonical map in each case.

I searched the project and source repository with `rg` for the theorem and its
declaration name, and searched Mathlib's derivation/localization files for an
extension theorem; no existing declaration states this result.  The recorded
Mathlib dependency `RingHom.FiniteType` was checked in
`Mathlib/RingTheory/FiniteType.lean` and matches exactly.  The module compiles
cleanly with `scompile.py`; its statement is copied verbatim into the node's
`lean.statement` record.
