## Worker report

The module `Sheaf.Paper.IntegralPullbackResolutionMatching` states
`WeilConjectures.integralPullbackResolutionMatching`, with proof `sorry`.
It is the specified counit identity in the derived category of whole strict
completed-coefficient towers. The item statement and proof plan are unchanged;
its statement dependencies gain only the new definition node described below.

Hypothesis and clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The valuation ring,
  chosen uniformizer and positive quotients are the recorded Padic coefficient
  constructions used by the imported completed-ring and quotient-system functors.
  Lean's index `n : ℕ` denotes the paper's exponent `n + 1`, including exponent 1.
- The schemes are `{V W Z : Scheme.{u}}`, the composable morphisms are
  `(h : Z ⟶ W) (k : W ⟶ V)`, with `[IsIso h] [IsIso k]`.
  The hypotheses `hV`, `hW`, `hZ` say ell is a unit in every respective stalk.
  The data-only helper `integralResolutionMatchingResidueInvertible` maps those
  same units through `Scheme.residue`; this supplies the existing eta API's
  `Invertible` residue-field instances without asking for additional hypotheses.
- `(N : sfIntegralConstructibleCategory l E V)` means exactly the recorded
  derived completeness, constructibility of every positive reduction, and one
  common bounded cohomological interval. No perfectness or Tor bound is added.
- `D : IntegralComparisonSystem.{u} l` is the normalized comparison data of
  the named realization dependency, not a new comparison or assumed equation.
  Its existence is the already recorded `integralPullbackComparisonRealization`.
  Its pullback models are normalized on every simultaneous K-flat presentation.
- `M` is written explicitly as `(integralDerivedPullback l E k).obj N.obj`.
  `integralResolutionMatchingTower l E D k N` is the whole quotient diagram
  `(integralComparisonDerivedSequencePullback l E k).obj
  (((D.coefficient E).system V).reduction.obj N.obj)`.
  The models' simultaneous representative normalization identifies this with
  the strict quotient tower used to construct M, with its actual transitions.
- The identification M with Rlim C is precisely
  `((D.coefficient E).pullback k).realization.hom.app N.obj`.
  Its image under the constant-tower functor is explicitly on the right side,
  before the original counit. Thus it is not silently treated as definitional equality.
- `h^*C` is `integralComparisonDerivedSequencePullback l E h` applied to that
  same diagram. `coefficientSequenceDerivedRestriction` retains the entire
  diagram over completed coefficients, with its horizontal maps and homotopies.
- Both epsilons are `integralComparisonTowerCounit` evaluated at the respective
  restricted diagrams. This is the constant-tower/total-limit derived-adjunction
  counit. `integralComparisonTowerCounit_computes` fixes its ordinary-limit-cone
  value on K-injective towers; naturality transports it through a resolution.
  No arbitrary cone or counit is supplied as a parameter to the theorem.
- Kappa is exactly `AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived
  l E h hZ hW M`; it uses the recorded chosen representative and its separate
  flat-term K-flat resolution. Eta is the existing `integralComparisonEta`,
  re-expressed by `integralResolutionMatchingEta` with the stalk hypotheses.
- The left side is `Delta.map (kappa ≫ eta.hom) ≫ epsilon_hstarC`.
  The right side is the diagonal/inverse-image identification, followed by
  the inverse image of `Delta.map (M_to_RlimC) ≫ epsilon_C`, followed by the
  whole-system tensor unit. In mathematical order this is exactly
  `epsilon_hstarC ∘ Delta(eta ∘ kappa) = u_C ∘ H(epsilon_C)`, under the stated
  identification of M. Lean's `≫` reads composition from left to right.
- `integralDerivedTowerInverseImageUnit` is the localized termwise sheafified
  x tensor 1 map. Its underlying unique section formula is stated in the
  new node's module. The asserted equality has codomain in
  `coefficientSequenceRestrictedDerived l E Z`: no evaluation, reduction,
  total-limit realization, cohomology functor or faithful-functor shortcut is
  applied to the equality. This renders the final "before realization or reduction" clause.

Dependency declarations read and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` publicly retains
  `Padic.coefficientExtensionRing`, its integer ring, ideals and transitions.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`
  and `ProEt.topology`. The morphism-properties dependency is explicitly a
  convention node, not a declaration; `Scheme`, `IsIso`, and the stalk unit
  hypotheses express the properties this item actually uses.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` publicly retains
  `completedIntegralCoefficientSheafUnrestricted` and the actual projections;
  `integralConstantToCompletionOfUniverses` is its constant-scalar map.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices` publicly retains
  `integralDerivedPullback`, `integralOperationsLevelPullback`, and their
  chosen K-flat/Roos construction; its slice extension is not substituted
  for the global construction here.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`: `IsDerivedLimit`
  and `IsDerivedLimitTriangle`. The strict-total-limit functor is the more
  specific recorded model, not an arbitrary object satisfying that property.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `ringedStrictTowerHomotopyLimitIndependentCoefficients`; its K-injective
  normalization underlies the existing counit interface.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`:
  `inverseImagePullbackComparisonDerived`; publicly retains
  `inverseImageIntegralModules`, `inverseImageIntegralDerived` and the
  section-normalized finite comparison.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `integralTowerGeneralPullbackComposition` and the unit-preserving finite model.
- `Sheaf.Paper.IntegralPullbackComparisonRealization`: `IntegralComparisonSystem`,
  `integralComparisonEta`, and `integralPullbackComparisonRealization`.
  Its imported `IntegralComparisonRealizationModels` supplies
  `integralComparisonConstantTower`, `integralComparisonTowerCounit`, the
  K-injective computation formula, and `IntegralComparisonPullbackModel`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, used by the counit normalization.

The published proof-dependency modules are also imported as plain imports,
including the cone-counit realization, strict Roos comparison, general derived
adjunction, diagram-site realization, countable-product exactness, K-flat,
change-of-rings, and levelwise-abelian interfaces. No import cycle was introduced.
The theorem docstring carries all seven DAG proof steps, distinguishing C, B,
and C_h and cancellation of the separate resolution q.

Edge cases checked before writing: identity h or k is allowed and uses the same
normalizations; empty schemes make the stalk conditions vacuous as intended;
the zero object N is permitted; exponent 1 is retained; no coefficient extension
or uniformizer is changed and no finite Tor-amplitude condition appears. The
helper module permits independent scheme and coefficient universes t and u,
with the existing small site at object universe t+1 and morphism universe t.
The item uses the comparison system's common universe u, exactly as its recorded
interface; this is a common ambient universe, not a new equality of site object
and morphism universes. The equation is in the full derived tower category,
so no claim of componentwise faithfulness is needed.

Searches for the item:

- `msearch.py ... leanfinder "Counit identity for the inverse image pullback
  comparison on a strict quotient tower"`: eight generic chosen-pullback and
  Grothendieck-category counit hits; none is this completed-coefficient identity.
- `msearch.py ... loogle "CategoryTheory.Adjunction.counit"`: twelve generic
  adjunction definitions and identities; no strict quotient-tower statement.
- `msearch.py ... grep "inverseImage.*(Tower|Sequence)|counit.*(pullback|Pullback)"
  CategoryTheory`: eight generic chosen-pullback/shift/sieve hits only.
- `rg` for the item id and proposed declaration names in upstream WeilConjectures,
  shared lean/Sheaf and dag/lean_names_upstream.json found no existing declaration.
  The generic inverse-image search located the recorded single-module functor
  and the chosen-resolution reduction product, which are reused.

No statement correction, disputed assertion, or dependency-record repair is needed.
All definitions contain actual data; the only postponed proofs are the main
identity and the new definition node's uniqueness/existence characterization.

## New nodes

`def-trf-integral-tower-inverse-image-unit` supplies the missing whole-system
extension of the finite unit. Its module is
`Sheaf.Paper.IntegralTowerInverseImageUnit`. It defines H on actual completed
module towers by ordinary whiskering, derives that exact functor, and constructs
the canonical diagonal interchange using Mathlib `Functor.compConstIso` and
exact-derived composition isomorphisms. Its `integralTowerInverseImageUnit_existsUnique`
states the unique ordinary natural isomorphism with its full section formula:
use the sequence-pullback adjunction unit at the postcomposed site object,
then restrict along `proEtaleIsoCommaArrow`. The map is the finite x tensor 1
map at every index, after the recorded completed-coefficient restriction.
The uniqueness characterization determines actual data, including the inverse;
`integralTowerInverseImageUnit` takes that uniquely specified isomorphism, and
`integralDerivedTowerInverseImageUnit` localizes it. No arbitrary transformation,
Nonempty-only comparison, or new site/pullback/counit is introduced.

Source: Stacks sites-modules.tex, Tags 03D6 and 03CZ and the module pullback
adjunction, on the sequence site used for Tag 0941; the blueprint Global powers
paragraph needs naturality of exactly these canonical inverse-image identifications.
The new node cites the existing sequence-site, whole-system pullback, and
realization-model nodes, rather than duplicating those notions.

New-notion searches: LeanSearch for the tensor unit on quotient coefficient
sheaves returned the generic Mathlib module-pullback adjunction and unit results.
LeanFinder for the whole-tower unit returned eight ordinary tensor quotient and
presentation results. Mathlib grep returned ten generic pullback-adjunction hits.
Upstream and shared Lean grep found no whole-system H/unit declaration.
`tools/blueprint_refs.py search "tower inverse image unit"` and
`... search "whole quotient towers"` returned zero matches; the broad DAG grep
located the current item's requirement and the realization-model node, neither
of which supplies this unit. The exact query/result summaries are recorded in
the new node's mathlib_searches. Its existence/uniqueness theorem is the node's
stated characterization, with a complete natural-language construction proof.

## Self-review

A separate second pass by this worker opened both Lean modules and both node
records. The dispatcher explicitly prohibits starting another agent; the
maintainer supplies the independent review after delivery.

The second pass checked every binder above against the item text and traced
both sides' endpoints. It caught the need to display M's realization isomorphism
on the right and the diagonal/inverse-image identification before H(epsilon),
both of which are explicit in the final statement. It also checked that the
new unit's input sections are those of the recorded coefficient restriction,
its output sections are restricted from the actual sequence-pullback unit,
and its natural isomorphism is characterized at every positive exponent and
site object. The new node's mathematical functor-composition order was made
explicit with circle notation. Stalk invertibility is translated to residue
invertibility using the actual residue homomorphism, not supplied twice as
independent hypotheses. The main theorem assumes neither the desired counit
identity nor cone-counit compatibility as a parameter. It applies kappa to M,
not to the original N or to C. No statement clause was dropped or strengthened.

Validation: `scompile.py Q01 lem-trf-integral-pullback-resolution-matching`
compiled both delivered modules separately in dependency order, including the
library-path checks. All passed with no errors or non-sorry warnings; the final
library checks took 4.1 seconds and 3.8 seconds respectively, below 60 seconds.

Delivery metadata: server preflight exposed one additional published blueprint
ancestor, `lem-trf-rational-global-frobenius-powers`, absent in the read-only
checkout. The new node via chain was aligned with the server-reported chain.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
