## Worker report

The module `Sheaf.RingTheory.ClosedFibrePolynomialPresentation` states
`Algebra.EssFiniteType.exists_polynomial_maximal_localization_quotient` with `sorry`.
It introduces no definitions and proves nothing. Its module and theorem docstrings cite
Stacks Tag 0AUG, `lemma-localization-at-closed-point-special-fibre`; the theorem docstring
contains all seven DAG proof steps and their dependencies.

I read the node, every statement dependency and its recorded declarations, all proof
steps, and the source in `literature/stacks-project/algebra.tex`, at the indicated label.
The Q116 ledger entry is the stage-1 split, not an existing Lean statement: the current
node has no `lean` record. There is no repair note or return for this item.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Commutative rings R and S: `(R : Type u) (S : Type v) [CommRing R] [CommRing S]`.
  The two universes are independent and explicit.
- The given homomorphism R → S: `[Algebra R S]`, with structure map `algebraMap R S`.
  Every homomorphism of commutative rings determines precisely such an algebra structure;
  there is no restriction on this map.
- Essentially finite type: `[Algebra.EssFiniteType R S]`, the declaration supplied by
  `def-weil-pbc-essentially-finite-type-algebra`'s Mathlib match. Its docstring and
  `essFiniteType_iff_exists_subalgebra` identify it with a localization of a finite type
  algebra, exactly as the dependency says.
- Both rings local: `[IsLocalRing R] [IsLocalRing S]`. There is no `IsLocalHom` binder.
- The maximal ideal of R: `IsLocalRing.maximalIdeal R`.
- Some nonnegative finite number of variables: `∃ (n : ℕ)`, indexed by `Fin n`.
  `MvPolynomial (Fin n) R` is the polynomial ring in exactly n variables; indexing from
  zero instead of one is a renaming.
- A maximal ideal of that polynomial ring: `m : MaximalSpectrum (MvPolynomial (Fin n) R)`;
  `m.asIdeal` is its ideal and `m.isMaximal` its maximality certificate. Maximality implies
  primality, so the canonical localization is well typed.
- Lying over the base maximal ideal: the equation
  `m.asIdeal.comap (algebraMap R (MvPolynomial (Fin n) R)) = IsLocalRing.maximalIdeal R`.
  This is equality of contractions, not merely containment.
- The polynomial local ring: `Localization.AtPrime m.asIdeal`.
- A quotient of that very ring: `∃ I : Ideal (Localization.AtPrime m.asIdeal)`, followed
  by `Localization.AtPrime m.asIdeal ⧸ I`.
- A multiplicative subset of that quotient containing one: `T : Submonoid
  (Localization.AtPrime m.asIdeal ⧸ I)`. `Submonoid` provides closure and one, without
  any extra disjointness or finite-generation condition.
- S is its localization: `Nonempty (Localization T ≃ₐ[R] S)`.
  `Localization T` is the actual ring of fractions, and the equivalence preserves the
  original R-algebra structure. Nonempty here expresses existence of an isomorphism
  between two specified rings; it does not choose undefined data or a canonical map.
  Reversing this equivalence gives the source's wording S ≅ T⁻¹D.

Dependency declarations used:

- `def-weil-pbc-essentially-finite-type-algebra`: `Algebra.EssFiniteType`,
  `Mathlib.RingTheory.EssentialFiniteness` (definition and full signature read).
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`,
  `Mathlib.Algebra.MvPolynomial.Basic`. I also read `MvPolynomial.aeval` in
  `Mathlib.Algebra.MvPolynomial.Eval` and `MvPolynomial.algHom_ext` in Basic; the
  statement needs only the ring itself, while the proof uses its universal property.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`. I read also the recorded
  `Ideal.ResidueField` and `Ideal.Fiber` declarations and docstrings in their Mathlib
  modules; the conclusion needs only the localization clause.
- Standard Mathlib notions `IsLocalRing`, `IsLocalRing.maximalIdeal`,
  `MaximalSpectrum`, `Ideal.comap`, ideal quotient, `Submonoid`, `Localization` and
  `AlgEquiv` render the elementary ring terminology without a private copy.

The module publicly imports the statement dependency modules, and ordinary imports
supply the stated proof dependencies: `Mathlib.RingTheory.FiniteType` for
`RingHom.FiniteType`/`Algebra.FiniteType`, `Mathlib.RingTheory.Ideal.Maximal` for
`Ideal.exists_le_maximal`, `Mathlib.RingTheory.Valuation.ValuationRing` for
`ValuationRing`, `Mathlib.RingTheory.Valuation.LocalSubring` for
`LocalSubring.exists_le_valuationSubring`, and
`WeilConjectures.Mathlib.RingTheory.Valuation.LocalSubring` for
`ValuationSubring.exists_comap_eq`. I read the two valuation-domination/extension
signatures in their recorded source modules.

Edge cases checked before writing:

- n = 0 is allowed (`Fin 0`); there is no positivity hypothesis. The zero-variable
  polynomial ring is R up to its standard algebra equivalence. The proof's chart-change
  case cannot occur with no coordinates.
- Field bases and field targets are allowed by `IsLocalRing`. Their maximal ideals can
  be zero; the equation of contractions remains meaningful.
- The nonlocal map from a DVR to its fraction field is not excluded: such local rings
  need not have a local structure map. No contraction condition is imposed on the
  original R → S map.
- The zero ring is excluded exactly by the node's definition of a local ring as having
  exactly one maximal ideal. Mathlib `IsLocalRing` includes nontriviality, which matches.
- T may contain zero as a submonoid in general. In this conclusion the equivalence with
  the nonzero local ring S automatically prevents the localization from being zero;
  there is no added hypothesis about T. Likewise I is not assumed proper in advance.
- Different sizes of R and S are allowed. The constructed quotient/localization lives
  in the size of R, but an equivalence to S is a proposition valid across both universes.

Searches for an existing statement (all msearch calls used the prescribed wrapper;
actual query records and digests are in `searches.jsonl` in the sandbox):

- LeanFinder: “An essentially finite type local algebra over a local ring is a
  localization of a quotient of a polynomial ring localized at a maximal ideal over
  the base maximal ideal”. Eight hits, including `Algebra.EssFiniteType.isLocalization`
  and `Algebra.essFiniteType_iff_exists_subalgebra`. They give presentations at a
  multiplicative set, not a maximal polynomial ideal above the base maximal ideal.
- Loogle: `Algebra.EssFiniteType, IsLocalRing`. Eight hits, all on formally unramified
  algebras/residue fields; none is the node's unrestricted statement.
- Mathlib grep: `EssFiniteType|closed.fib[er]+|closed.point`, in RingTheory.
  Twenty-five displayed hits concern essential finiteness, closed points or smooth
  algebras; none gives this presentation theorem.
- LeanSearch: “Local essentially finite type algebra is localization of a quotient at
  a closed point of the special fibre”. Eight hits on essential finiteness/localization
  and quasi-finiteness, with no full match.
- `rg` on `WeilConjectures` for `EssFiniteType`, closed fibre with polynomial, and the
  item identifier: no whole-item declaration. I opened
  `AlgebraicGeometry.exists_flat_polynomial_presentation` in
  `WeilConjectures/Compactification/ValuativeCriterion.lean`: it presents a field-valued
  point by a flat polynomial algebra on an arbitrary variable set, not this statement.
- `rg` on `lean/Sheaf` for closed-fibre polynomial, essential finiteness, and localized
  quotients: related polynomial local fibre and Popescu modules, but no statement of
  Tag 0AUG. `LocalizedFiniteQuotientCharts` was read and concerns finite algebra charts,
  not an arbitrary essentially finite type local algebra over a local base.
- Duplicate-name grep for `exists_polynomial_maximal_localization_quotient` in
  `dag/lean_names_upstream.json`, Mathlib, `WeilConjectures`, and `lean/Sheaf`: no hit.

Validation: `scompile.py NB lem-per-closed-fibre-polynomial-presentation` on the sole
module returned exit code 0, with no warnings or errors, compiling both its sandbox
check and its library name separately (1.5 s and 1.9 s). All universes and variables
are explicitly bound. The node copy changes only `lean`; no statement correction,
new node, or dependency repair was required. No statement dispute was found.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
