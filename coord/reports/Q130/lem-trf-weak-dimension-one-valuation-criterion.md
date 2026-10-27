## Worker report

The module `Sheaf.RingTheory.WeakDimensionOneValuationCriterion` states the two clauses of
`lem-trf-weak-dimension-one-valuation-criterion`; both named theorem proofs are `sorry`.
No definitions, extra nodes, dependency repairs, or statement corrections are needed.
Source read: `literature/stacks-project/more-algebra.tex`, Tag 092S,
`lemma-weak-dimension-at-most-1`, the five equivalent conditions and its entire proof;
Tag 092D, `definition-weak-dimension`. The first theorem renders (1) iff (5), with the
explicit free-surjection resolution from (4) implies (1). The second theorem renders
the node's final local assertion, as established in the same source proof.

Hypothesis and clause correspondence:

- A commutative ring is `(R : Type u) [CommRing R]`. The general statement assumes
  neither `Nontrivial R`, `IsDomain R`, nor `IsLocalRing R`.
- Every R-module is `∀ M : ModuleCat.{max u v} R`. Mathlib's bundled modules carry
  their additive group and R-module structures; this includes arbitrary modules,
  without a finiteness condition. The independently declared `v` allows arbitrary
  module size, and `max u v` always contains the ring universe. Any smaller carrier
  can be lifted; this is the usual universe convention for quantifying over modules.
- The flat modules F0,F1 are `∃ F₀ F₁ : ModuleCat.{max u v} R,
  Module.Flat R F₀ ∧ Module.Flat R F₁ ∧ ...`. The free surjection and its kernel
  can be constructed in this same universe.
- The maps are `a : F₁ →ₗ[R] F₀` and `b : F₀ →ₗ[R] M`.
  `Function.Injective a`, `Function.Surjective b`, and
  `LinearMap.range a = LinearMap.ker b` are exactly the three requested properties.
  No split-exactness or finite-generation condition is imposed.
- The equivalence connective is `↔`, in both directions.
- Every prime ideal is `∀ (p : Ideal R) [p.IsPrime]`. Its localization is precisely
  the recorded `Localization.AtPrime p`.
- Being a valuation DOMAIN is
  `∃ h : IsDomain (Localization.AtPrime p), @ValuationRing (Localization.AtPrime p) _ h`.
  The domain is a conclusion, not an assumed instance on the original ring or on
  its localizations. `ValuationRing` takes an `IsDomain` input, so the explicit
  existential is necessary. The fraction-field criterion is exactly equivalent
  by `ValuationRing.iff_isInteger_or_isInteger` / `ValuationRing.TFAE`.
- The final nonzero local clause is the second declaration
  `Ring.flat_resolution_length_one_iff_valuation_of_isLocalRing`, with
  `[IsLocalRing R]` (which extends `Nontrivial R` in Mathlib), the identical
  resolution condition, and conclusion
  `∃ h : IsDomain R, @ValuationRing R _ h`. Neither theorem assumes a Noetherian
  property or any dimension bound on the ring.

Statement dependencies, signatures and docstrings read:

- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`
  and `Module.Flat` (its definition and tensor-injectivity characterization in
  `Mathlib.RingTheory.Flat.Basic`). The module imports the recorded module publicly
  and uses its recorded `Module.Flat` declaration, rather than introducing a synonym.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
- `def-trf-valuation-ring`: the Mathlib match is
  `Mathlib.RingTheory.Valuation.ValuationRing`, `ValuationRing` and
  `ValuationRing.TFAE`; its domain parameter and fraction-field equivalence were read.
  This dependency has no `lean` record and needs none: its Mathlib match is usable.

The proof dependencies with recorded declarations are imported as ordinary imports:
`WeilConjectures.Mathlib.RingTheory.Flat.Equalizer`
(`Module.Flat.of_exact_of_flat_of_flat_right`),
`Mathlib.Algebra.Module.LocalizedModule.Submodule` (`Submodule.localized'gi`),
`Mathlib.RingTheory.Flat.Stability` (`Module.Flat.baseChange`),
`Mathlib.RingTheory.LocalRing.Module` (`Module.free_of_flat_of_isLocalRing`),
`Mathlib.Algebra.Module.LocalizedModule.Exact` (`LocalizedModule.map_exact`),
`Mathlib.RingTheory.Flat.TorsionFree`
(`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`),
`Mathlib.RingTheory.Flat.Localization` (`Module.flat_iff_of_isLocalization` and
`Module.flat_of_isLocalized_maximal`), and `Mathlib.RingTheory.Flat.Tensor`
(`Module.Flat.iff_lift_lsmul_comp_subtype_injective`).
`Module.Flat.of_projective` and `Module.Flat.of_free` come from the already public
flatness import. Every proof dependency is thus available; the theorem docstrings
carry the node's pullback, localization, rank-one, tensor-square, free-surjection,
and local-case arguments, with their node references.

Edge cases checked mathematically before writing:

- Zero ring: no prime ideals; every unital module is zero, so the resolution property
  holds. Only the local consequence excludes this case.
- Zero module: choose zero F0 and F1; the exactness requirements permit this.
- Field: all modules are free, so take F1 = 0, F0 = M, b = identity; its only prime
  localization is itself, a valuation domain.
- Product of fields: prime localizations are fields, while the original ring need
  not be a domain; hence the general theorem must not assume `IsDomain R`.
- Nonreduced local ring such as k[ε]/(ε²): the valuation-domain conclusion fails,
  as does the resolution condition. `PreValuationRing` alone would have been too weak.
- Nondiscrete and non-Noetherian valuation domains are included, as are infinitely
  generated modules and ideals. There are no discrete-valuation assumptions.
- All universes are explicitly declared; `autoImplicit` is disabled. No notation,
  private definition, local instance, `let` binder, or `show ... from` occurs.

Searches actually run:

- `msearch.py ... leanfinder "Every module over a commutative ring has a flat
  resolution of length at most one if and only if all prime localizations are
  valuation domains"`: eight hits, including the torsion/flatness theorem for
  domains with maximal valuation localizations, localization descent, local
  freeness, and Dedekind flatness. None is this ring-wide equivalence or its
  resolution formulation.
- `msearch.py ... loogle "ValuationRing, Module.Flat"`: one hit,
  `Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal`;
  it assumes the ring is a domain and concerns one module, so is not an exact match.
- `msearch.py ... grep "WeakDimensionLEOne|flat.?[Rr]esolution|valuation.*resolution"`:
  one unrelated hit in `Mathlib/Algebra/Homology/LeftResolution/Basic.lean`.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `WeakDimensionLEOne`, `flatResolution`,
  `flat_resolution_iff`, and valuation/flat-resolution combinations: upstream
  `WeilConjectures.RingTheory.ProEtale.WeakDimension` defines
  `Ring.WeakDimensionLEOne` by finitely generated ideal flatness, and proves
  `flat_submodule`, `flat_ideal`, and product/weakly-etale stability statements.
  Its source was read: it does not give the requested equivalence or the explicit
  length-one resolution criterion. There is no second definition of that notion
  here: the requested resolution condition is written out directly in the theorem.
  Other flat-resolution hits concern complexes or sheaves, not this statement.
- `grep -rn "lem-trf-weak-dimension-one-valuation-criterion" lean/WeilConjectures`:
  no hits. The source-module/node searches found no existing declaration of this item.

No statement dispute or node fault was found.

## Second reading by Q130

A second pass by the same dispatched worker, with the node and completed module
open, checked the above correspondence. No independent agent was started, as the
launcher explicitly forbids starting other agents; the maintainer supplies the
independent delivery review. This pass checked that the first theorem concludes
domainhood rather than assuming it, that all primes are quantified over (not just
maximal primes), that image equals kernel rather than only the composite being
zero, and that the local consequence is separately recorded in `lean.declarations`.
The local theorem repeats exactly the first resolution condition, including its
universe. Both proofs are postponed, and their docstrings include the relevant
natural-language proof. The compile linter found a redundant explicit `[Nontrivial R]` binder beside
`[IsLocalRing R]`; it was removed after reading `IsLocalRing` in
`Mathlib.RingTheory.LocalRing.Defs`, which extends `Nontrivial R`. This preserves
the nonzero local hypothesis and removes the warning. No statement correction
was required.
