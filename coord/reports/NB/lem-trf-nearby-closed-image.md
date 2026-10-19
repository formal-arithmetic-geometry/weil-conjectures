## Worker report

The module `Sheaf.Paper.NearbyClosedImage` states `AlgebraicGeometry.Orgogozo.nearbyClosedImage`.
It uses the project encoding of (D^b_c(X_{\mathrm{Et}},\Lambda)): `hKb` is boundedness of
`K` and `hKc` supplies a constructible finite-value étale module sheaf for every cohomology
sheaf. The Noetherian base is `[IsNoetherian S]`; properness and the closed factor are the
instances `[IsProper f]` and `[IsClosedImmersion i]`, with `fF` and `hfac` expressing the
factorization. `HasInvertibleExponent Λ S` is the invertible integer annihilator hypothesis.
The first conjunct quantifies every `r : ℤ` and maps
`UniversalTruncatedComparison fF Λ ⟨K,hKb⟩ r` to the corresponding property for `f`.
The second conjunct maps `IsPsiGood fF Λ K` to `IsPsiGood f Λ K`.
The proof is intentionally `sorry` at stage 2, and its docstring records the closed-image
tube argument from Orgogozo Lemma 3.2.2.

Dependencies used are `Sheaf.Paper.OrgogozoInductionData` for
`UniversalTruncatedComparison`, `Sheaf.Paper.OrientedNearbyCycles` through that module for
`EtaleDerived` and `IsPsiGood`, `Sheaf.Paper.OrgogozoGoodModification` for the established
constructible cohomology witness `orgogozoModuleSections`,
`Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` for constructibility,
`WeilConjectures.AlgebraicGeometry.InvertibleExponent` for `HasInvertibleExponent`, and
Mathlib's `IsNoetherian`, `IsProper`, and `IsClosedImmersion`.

Edge cases checked: the quantifier includes every integer `r`; empty schemes and zero
complexes are permitted by the quantified types; no reducedness, finite-type, or nonempty
hypothesis was added; the factorization map is explicit and nilpotent closed subschemes are
allowed by `IsClosedImmersion`.

Searches made: `msearch.py leanfinder` for universal nearby-cycle closed-image comparison
(no exact match); `msearch.py loogle` for nearby-cycle names (only unrelated `Units.ofNearby`/
`Units.val_ofNearby`); `msearch.py grep` for the nearby/closed-image patterns
(no matches); `rg` in `WeilConjectures/` and `lean/Sheaf/` for `nearbyClosedImage` and related
names (no existing declaration). Existing dependency declarations were opened and their full
signatures read. No statement fault or `STATEMENT-DISPUTED` flag.

## Second reading by NB

The node and file were read side by side. `[IsNoetherian S]`, proper `f`, closed immersion
`i`, factorization `fF ≫ i = f`, finite commutative `Λ` with invertible exponent, and the
constructible bounded complex data all appear explicitly. The first conclusion preserves the
node's universal integer `r` and implication between the two `P_r` predicates; the second is
the full Ψ-goodness implication. No clause is omitted or strengthened.

## Reviewer fix (maintainer second reader, 2026-10-18)

- `hKc` named `orgogozoModuleSections` from `Sheaf.Paper.OrgogozoGoodModification`, the module of
  lem-trf-orgogozo-good-modification, which has this item in its `proof_deps`. That import would
  close an import cycle when the parent's module imports this one for its proof (stages/2 §3
  rule 7). The same canonical construction is now written out in `hKc` (definitionally equal to
  the parent's hypothesis; checked by compiling an application of the theorem to the parent's
  `hKc`), and the import is dropped. No mathematical change.
- Added `public import Sheaf.Paper.OrientedNearbyCycles` (stmt_dep module used directly) and the
  `import` lines of the stated proof dependencies (OrientedPointCohomology,
  OrientedProductPointsConservative, CohomologyPullbackCanonicalArrows,
  StrictHenselizationClosedLift, ModuleSheavesColimitsForgetful, HasPullback).
- The theorem docstring now carries the node's eight proof steps (H8).
- Compiled with tools/nt_compile.py: clean (sorry only).
