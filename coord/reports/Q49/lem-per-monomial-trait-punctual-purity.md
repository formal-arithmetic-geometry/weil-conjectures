## Worker report

The module `Sheaf.AlgebraicGeometry.MonomialTraitPunctualPurity` defines the
coordinate-ring abbreviation `AlgebraicGeometry.Etale.monomialTraitRing` and
states `AlgebraicGeometry.Etale.monomial_trait_punctual_purity` with proof `sorry`.
It imports and uses the landed punctual-purity definition instead of defining
another class family or another purity predicate.

The hypotheses and conclusions correspond clause by clause as follows:

- The trait is `R : Type u` with `[CommRing R] [IsNoetherianRing R]
  [IsLocalRing R] [IsDomain R]`, `hdim : ringKrullDim R = 1`, and a principal
  maximal ideal `hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}`. The element
  `π : R` is the specified uniformizer.
- The prime is `ℓ : ℕ` with `hℓ : ℓ.Prime`; its invertibility in the trait is
  `hunit : IsUnit (ℓ : R)`.
- The number of variables is `n : ℕ` with `hn : 1 ≤ n`. The exponents are
  `e : Fin n → ℕ`, and `he : ∃ i, e i ≠ 0` excludes exactly the all-zero tuple.
- The ring is `MvPolynomial (Fin n) R ⧸ Ideal.span
  {(∏ i : Fin n, MvPolynomial.X i ^ e i) - MvPolynomial.C π}`. The abbreviation
  supplies real quotient-ring data, including zero exponents.
- Noetherianity is `∃ (_hN : IsNoetherian (Spec (.of (monomialTraitRing R π n e)))), …`.
- Regularity is `IsRegularScheme (Spec (.of (monomialTraitRing R π n e)))`.
- Punctual purity is `IsPunctuallyPure ℓ hℓ
  (Spec (.of (monomialTraitRing R π n e)))`, the declaration owned by
  `def-per-punctual-purity`. Its `IsPunctuallyPureAt` uses the actual local
  stalk, finite Krull dimension, residue-field closed immersion, and canonical
  Kummer class map, whose invertibility is tested at every point. This is the
  meaning introduced in the item's first paragraph, ILO XVI 3.2.1--3.2.2.

The statement dependency declarations used are:

- `def-per-punctual-purity`: `AlgebraicGeometry.Etale.IsPunctuallyPure` from
  `Sheaf.AlgebraicGeometry.PunctualPurity`, including its published canonical
  `regularImmersionClasses` and `punctualPurityClassMap`.
- `def-weil-regular-scheme`: `AlgebraicGeometry.IsRegularScheme` from
  `Sheaf.AlgebraicGeometry.IsRegularScheme`.
- `def-weil-pbc-derived-categories`: `AlgebraicGeometry.Etale.DerivedCategoryModule`
  from `WeilConjectures.AlgebraicGeometry.DerivedCategories`, used by the
  published purity interface.
- `def-asd-finite-etale-tate-twist`: `AlgebraicGeometry.Scheme.finiteEtaleTateTwist`
  from `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`, used by that interface.
- `lem-per-regular-immersion-class-calculus`:
  `AlgebraicGeometry.Etale.regular_immersion_class_calculus` and
  `RegularImmersionClassFamily` from
  `Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus`, imported through
  `PunctualPurity` and used there to obtain the uniquely normalized class.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` from
  `Mathlib.AlgebraicGeometry.ResidueField`, used in the published predicate.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` from
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim` from
  `Mathlib.RingTheory.KrullDimension.Basic`.

The edge cases checked are `n = 1`, an exponent equal to one, zero exponents
mixed with positive exponents, exponents divisible by ℓ, and exponents divisible
by the positive residue characteristic. The all-zero tuple is excluded by `he`;
`n = 0` is excluded by `hn` as in the source. No completeness, henselianity,
excellence, or additional characteristic assumption occurs. Universe `u` is
explicit; every variable is bound with `autoImplicit false`. The shared purity
predicate tests all points, including the generic point and points with
codimension zero.

The retained initial searches in `searches.jsonl` include LeanFinder
(`Regular monomial hypersurface over a discrete valuation ring is cohomologically
punctually pure`), Loogle (`IsDiscreteValuationRing, IsRegularScheme`), Mathlib
grep (`PunctuallyPure|punctualPurity|Gysin`), LeanSearch (`Etale cohomological
purity monomial hypersurface over a trait`), and project/source searches for
the item and its declarations. They found no existing monomial purity theorem.
The repair reread the current `def-per-punctual-purity` record and the complete
`lean/Sheaf/AlgebraicGeometry/PunctualPurity.lean` module. That landed definition
supersedes the initial search's absence of a shared purity predicate. Mathlib's
existing spectrum, residue field and Krull dimension are retained.

No `STATEMENT-DISPUTED` flag or source-statement correction is needed. The
natural-language statement is unchanged; only its existing definition dependency
is added to `stmt_deps`.

## Repair of the returned delivery

H4/H12: added `def-per-punctual-purity` to `stmt_deps`; replaced the direct
class-calculus import with `public import Sheaf.AlgebraicGeometry.PunctualPurity`;
deleted `punctualPurityClasses`, `IsPunctualPurityPair`, and
`IsCohomologicallyPunctuallyPure`. The third clause now uses exactly
`IsPunctuallyPure ℓ hℓ (Spec (.of (monomialTraitRing R π n e)))`.
The node's `lean.declarations` lists only the coordinate ring and theorem, and
its signature is copied verbatim from the repaired module.

H13: removed `EtaleFiniteTwistPullback.lean` and the
`lem-asd-etale-finite-twist-pullback.json` copy from the packet. The delivery
contains no dependency-module republication and no change to that node. The
published side override supplies the canonical finite-twist interface.

Before editing, the saved packet passed `deliver2.py --no-push` at temporary
commit `206f033851`. Its mechanical acceptance did not resolve the review's
mathematical duplication finding; the repairs above were therefore required.
All non-`lean` item fields were refreshed from the current shared node before
adding the single authorized `stmt_deps` entry. No repository Git commands or
writes to shared sources were used.

## Second reading by Q49

I reread the current item statement, the repaired module, and the complete
landed `PunctualPurity` interface. The trait hypotheses, prime and invertibility,
nonempty variable range, arbitrary nonnegative exponent tuple with a nonzero
entry, and displayed quotient are unchanged. The conclusion still has exactly
Noetherianity, regularity, and punctual purity. The last clause now uses the same
canonical Kummer class and purity predicate as the purity proof dependencies;
the three duplicate declarations have been removed. No new assumptions or
restrictions were introduced. The theorem retains its complete six-step proof
docstring and its sole expected `sorry`. I checked the packet inventory: one
item module, its node, this report, and the retained local search log; neither
returned finite-twist dependency file remains.
