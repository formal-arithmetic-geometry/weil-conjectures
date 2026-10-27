## Worker report

The module `Sheaf.RingTheory.QuasiExcellentLocalization` states
`isQuasiExcellent_localizedModule`, with its whole proof postponed by `sorry`.
It constructs no new notion. Only the item's `lean` field changes; there are no
new nodes, dependency repairs, or statement corrections.

The statement matches the node clause by clause:

| Node clause | Lean rendering |
| --- | --- |
| A commutative ring R | `(R : Type u) [CommRing R]`, with explicit `universe u` |
| R is quasi-excellent | `(hR : IsQuasiExcellent R)` |
| T is a multiplicative subset, containing 1 and closed under multiplication | `(T : Submonoid R)`; its `one_mem` and `mul_mem` fields are precisely these conditions |
| T⁻¹R is the localization of the R-module R | `LocalizedModule T R`, the dependency's actual recorded declaration |
| Its usual commutative ring structure, product rr'/ss' and unit 1/1 | The existing inferred `CommRing (LocalizedModule T R)`; `LocalizedModule.mk_mul_mk` gives the product formula, and the Ore localization unit is the fraction 1/1 |
| The localized ring is quasi-excellent | `IsQuasiExcellent (LocalizedModule T R)` |
| Allow T = {1} | No condition beyond `Submonoid R`; its bottom submonoid is allowed |
| Allow 0 in T | No `0 ∉ T` or nontriviality binder |
| No finite generation, universal catenarity, or ground field | None of these assumptions occurs; the hypothesis is `IsQuasiExcellent`, not `IsExcellent` |

The full signatures and docstrings of the two statement dependencies were read:

- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`,
  `IsQuasiExcellent (R : Type u) [CommRing R] : Prop`. Its body is
  `IsNoetherianRing R ∧ IsGRing R ∧` openness of the regular locus of every finite
  type R-algebra. This is the precise quasi-excellent portion of the dependency,
  whose primary record also lists `IsExcellent` and all supporting declarations.
- `def-weil-pbc-module-localization`:
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule`. Its full
  signature takes `{R : Type u} [CommSemiring R] (S : Submonoid R) (M : Type v)
  [AddCommMonoid M] [Module R M]` and returns `Type (max u v)`. Here M is R with
  its canonical self-module structure. `LocalizedModule.mk_eq` is exactly the
  fraction relation in the node. Basic.lean lines 155--268 supply the product,
  product formula and commutative ring instance; this is the usual ring, not an
  arbitrary structure chosen as an extra hypothesis. `Localization S` and
  `LocalizedModule S R` both reduce to `OreLocalization S R`.

The proof plan's dependency records and source declarations were also read and
are imported for stage 3:

- `lem-weil-pbc-localization-noetherian`:
  `Mathlib.RingTheory.Localization.Submodule`, `IsLocalization.isNoetherianRing`.
- `lem-weil-pbc-localization-prime-residue-field-iso`:
  `WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso`,
  `IsLocalization.prime_localRing_residueField_iso`.
- `lem-weil-pbc-adic-completion-ring-equiv`:
  `WeilConjectures.RingTheory.AdicCompletionRingEquiv`,
  `AdicCompletion.exists_ringEquiv`.
- `def-weil-pbc-g-ring`: `WeilConjectures.RingTheory.GRing`, `IsGRing`,
  `RingHom.IsRegular` and `Algebra.IsGeometricallyRegular`.
- `lem-weil-pbc-regular-ring-map-ring-equiv`:
  `WeilConjectures.RingTheory.RegularRingEquiv`,
  `RingHom.IsRegular.of_ringEquiv`.
- `def-weil-pbc-essentially-finite-type-algebra`:
  `Mathlib.RingTheory.EssentialFiniteness`, `Algebra.EssFiniteType`.
- `lem-weil-pbc-essentially-finite-type-composition`:
  `Mathlib.RingTheory.RingHom.EssFiniteType`, `RingHom.EssFiniteType.comp`.
- `lem-weil-pbc-localization-spectrum-embedding`:
  `Mathlib.RingTheory.Spectrum.Prime.Topology`,
  `PrimeSpectrum.localization_comap_isEmbedding` and
  `PrimeSpectrum.localization_comap_range`.
- `lem-trf-regular-local-ring-isomorphism`:
  `Mathlib.RingTheory.RegularLocalRing.Defs`, `IsRegularLocalRing.of_ringEquiv`.

The declaration docstring carries all five proof steps, including the
Noetherian, local-completion G-ring and J-2 arguments, with the exact DAG ids.
The underlying source was checked in
`literature/stacks-project/more-algebra.tex`, the definitions of excellent rings
and `lemma-finite-type-over-excellent` (Tags 07QT and 07QU). The latter explicitly
states arbitrary localization of finite type algebras; the present node is its
identity-algebra specialization, and the source explicitly omits the localization
proof that this node expands.

Edge cases checked before writing:

- T = {1}: all binders accept this submonoid and the localized ring is R.
- 0 in T, including T = R: `LocalizedModule.subsingleton` proves the quotient
  collapses. Zero commutative rings are accepted; Noetherianity remains true and
  the prime-indexed G-ring condition is empty. A unital algebra over the zero
  ring is zero, so its regular locus is empty and open, as required by J-2.
- R itself the zero ring: no `Nontrivial R` is introduced.
- Arbitrary, potentially infinitely generated T: no finiteness binder occurs.
- Arbitrary characteristic and arbitrary universe u: no field or characteristic
  restriction. The localization lives in the same universe u as R.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "Every localization of a quasi excellent commutative
  ring is quasi excellent"`: 8 hits, including `LocalizationPreserves`,
  `RingHom.EssFiniteType.holdsForLocalization` and quasi-finite localization
  lemmas. None states preservation of quasi-excellence.
- `msearch.py ... leansearch "Localization of a quasi excellent ring is quasi
  excellent"`: 8 hits, including `IsLocalization.isNoetherianRing`, quasi-finite,
  formally unramified, Artinian, and formally smooth localization results. None
  supplies both G-ring and J-2 preservation.
- `msearch.py ... loogle '"QuasiExcellent"'`: 0 hits.
- `msearch.py ... grep 'QuasiExcellent|quasi.excellent|quasiExcellent' RingTheory`:
  0 Mathlib hits.
- `rg -n 'QuasiExcellent|quasi.excellent|quasiExcellent'` on the project's
  `lean/WeilConjectures` and `lean/Sheaf`: the former only has a prose mention;
  the latter has `IsQuasiExcellent`, Nagata and completion results, and
  geometric consumers, but no theorem for arbitrary localization.
- `grep -rn 'lem-per-quasi-excellent-localization' lean/WeilConjectures`:
  no hits.
- `rg -n 'isQuasiExcellent_localizedModule|IsQuasiExcellent.localization'` on
  Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no collision.
- `rg` of the localized-module source for ring structures found the existing
  `LocalizedModule.instCommRing`, so no ring construction helper is needed.

Validation: the prescribed `scompile.py NO lem-per-quasi-excellent-localization`
compiled the file in sandbox mode (2.3 seconds) and library mode (1.3 seconds)
with exit 0 and no errors or unexpected warnings. No local or global Lake build
was run. No statement is disputed and no node fault was found.

## Second reading by NO

A separate rereading pass by the same dispatcher-started worker compared the
actual node and the final module; this is not represented as an independent
agent review. The maintainer supplies the independent review under the brief.

The signature has exactly one commutative ring R, its quasi-excellence proof,
and a submonoid T. In particular it does not accidentally require excellence
or injectivity of the localization map. Its conclusion uses the dependency's
`LocalizedModule T R` rather than a freely chosen ring or an unrelated module.
The existing ring instance was read at its definition and product formula,
confirming the stated multiplication and unit. Each affirmative mathematical
clause and each explicitly allowed edge case is matched in the table above.
No mismatch or change was found. All variables and universes are explicitly
bound, and the only proof is the required whole-theorem `sorry`.
