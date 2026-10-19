## What changed

Proved `AlgebraicGeometry.Scheme.residueLisseConstantComparison_exists` using the
sheafification adjunction, local bijectivity of the finite coefficient scalar map,
and sheafification hom-extensionality. Existing public signatures and definitions
are unchanged.

Replaced the proof of `AlgebraicGeometry.Scheme.residue_lisse_perfect_lift` by a
compiling reduction to two component results. The proof chooses bounded
finite-projective representatives of the residue witnesses and explicitly uses the
exact constant functor's localization factors. It obtains the uniform finite-level
structure, applies finite-system realization, and uses the unit-compatible Koszul
reconstruction theorem to identify M with its quotient-system derived limit.
The final isomorphism uses the exact slice functor and its comparison with the
representative-based restriction in the existing statement; perfectness is proved
from the actual bounded finite-projective complex returned by realization.

The new modules are `Sheaf.Paper.FinitePerfectQuotientModels` and
`Sheaf.Paper.FinitePerfectAdicRealization`. Their statements use the actual finite
coefficient sheaves and the existing derived changes of rings. The former records
uniform bounds but allows separate finite-level covers and models. The latter
identifies the derived limit of the specified quotient tower, and assumes no
completeness of its original object. Neither asserts the original lifting theorem
under another name. The original completion hypothesis is used only in the proved
combining argument.

Also proved coefficient compatibility from constant-section normalization, exact
further slice restriction, and the entire finite-level induction. The induction
retains the original residue cover, enlarges a possibly empty interval to
[min a b,b], proves the zero case on every smaller chart, and applies the separate
one-step filtration statement. Experimental scalar-equivalence helpers that the
final proof does not invoke are retained only in scratch work.

## Proved and sorry left

The item originally had two holes. Its comparison theorem is proved outright;
its main theorem is decomposed, with complete Lean proofs combining the one-step
propagation lemma, natural-number induction, and finite-system effectivity. The item now has zero `sorry` tokens. Two holes are added:

- `AlgebraicGeometry.Scheme.residuePerfect_quotient_models_succ`, in
  `Sheaf.Paper.FinitePerfectQuotientModels`, node
  `lem-weil-pbc-residue-perfect-finite-quotient-models`.
- `AlgebraicGeometry.Scheme.finitePerfectModels_adic_realization`, in
  `Sheaf.Paper.FinitePerfectAdicRealization`, node
  `lem-weil-pbc-finite-perfect-adic-realization`.

The following additional declarations are proved without new holes:
`finitePerfectModels_normalized_compatible` and
`residuePerfect_finite_quotient_models`, together with their private slice and
coefficient compatibility helpers.

Both remaining holes are named public theorems with exactly `by sorry`, complete proof descriptions,
and source nodes. No definition or private declaration has a hole. This is one
proof and one decomposition: two original holes closed, two component holes added,
net zero by that count. It is not claimed to be a full proof of the lifting result.

## No longer needed

The main proof does not use the discrete-constant/completed-coefficient equivalence;
it uses the normalized Koszul quotient-completion unit directly. Consequently its
old direct dependency `lem-weil-pbc-constant-completion-equivalence` is removed.
The other long-plan inputs are now dependencies of the two component nodes rather
than direct dependencies of the combining proof. They are not claimed as globally
pruned modules. The old top-level `tool_uses` entries have been removed from the main node because
that argument has moved to the component nodes: `lem-pc-kflat-resolution`,
`lem-sf-derived-homology-long-exact`, `lem-weil-pbc-constant-sheaf-geometric-stalk`,
`lem-weil-proetale-countable-products-exact`,
`lem-weil-proetale-weakly-etale-localization`, `pqf-lem-locnoeth-lft`, and
`prop-weil-pbc-geometric-stalks-exact`.

Removed these direct proof imports from the item (the relevant ones remain imported
by the component modules or their dependencies):

- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.RingTheory.Ideal.Quotient.Defs`
- `Mathlib.RingTheory.Ideal.Quotient.PowTransition`
- `Mathlib.RingTheory.Noetherian.Defs`
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`
- `Sheaf.Algebra.Homology.KFlatCoefficientUniverse`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`
- `Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Paper.AdicCoefficientDatum`
- `Sheaf.Paper.CompatibleFiniteDerivedTrivializations`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.ConstantModuleSectionProperties`
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
- `Sheaf.Paper.NilpotentReductionLissity`
- `Sheaf.Paper.ProEtaleConstructibleSheaf`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.RingTheory.RlimPerfectComplete`
- `WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact`
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`

Experimental tower comparisons were removed from the item because the final
combining proof does not use them. The needed consecutive quotient and scalar
projection equations are proved generically in the first new module and are
explicitly supplied to both component results. No existing
library module is withdrawn. No global module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The original six-step plan is mathematically sound, but its declared finite-reduction
and complete-lifting interfaces use different coefficient and site presentations.
`adic_constructible_finite_reductions` and `adicResidueLissePerfectLift` use
coefficient-sized small site models, large coefficient rings, and another completion
notion. They cannot directly consume this item's actual quotient-reduction and
intrinsic-completeness hypotheses. The new statements isolate finite-level
propagation and finite-system effectivity in this presentation; the two remaining
proofs must supply that mathematics, not assume any extra hypotheses on M.

Checked the intended edge cases: I=0; I=A (the finite levels are zero, and adic
completeness forces A to be zero in the realization statement); the empty scheme;
and non-complete M with all quotient reductions zero. In the last case the
realization statement concerns the zero derived limit and does not falsely assert
that M is zero. No quotient A/I^(n+1) is assumed perfect over A/I^(n+2).

## New nodes

`lem-weil-pbc-residue-perfect-finite-quotient-models` states the one-step
ideal-filtration, etale-origin and finite-Tor local-model result from Stacks
Tags 09C2 and 094I. The all-level corollary is proved from it by induction.
It takes no completeness hypothesis and makes no simultaneous-trivialization or
completed-realization assertion. Its Lean file also records the actual constant
complex construction and finite-level model property. Four Mathlib searches (including LeanSearch) found
no direct match.

`lem-weil-pbc-finite-perfect-adic-realization` realizes the finite-system effectivity
argument of Stacks Tag 09C6 using the algebraic reconstruction of Tag 09AW,
compatible finite derived trivializations, and the Roos limit computation. It has
no residue-only hypothesis and identifies the specified derived limit, not M.
The new node records its normalization, stalk, empty-cover and idempotent-summand
arguments. Four Mathlib searches (including LeanSearch) found no direct match.

The required unit-route import `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`
is retained. No existing definition or statement changed and no consumer adaptation is required.
`coord/changes/residue-lisse-local-universe-instance.md` records the new private
local instance command required for proof elaboration. Its local scope leaves all
importers unchanged; downstream analysis reports zero users of the private name. The independent delivery reader must check
the two new statements and their separation from the original theorem.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
