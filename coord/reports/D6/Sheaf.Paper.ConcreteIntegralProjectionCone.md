## What changed

Completed the five-step Lean argument, continuing the sandbox attempt that restored the assigned
quarantined module, for
`WeilConjectures.ConcreteIntegralProjection.concreteIntegralProjectionCone` without changing its
statement. `coneTransition` keeps its original body, the two-summand cone map of the
unrestricted transitions (reviewer correction: the delivered body transported the intrinsic
transition through the signed cone isomorphisms, which made the last conjunct nearly
definitional while `coneNaturality` was never used). The unrestricted transitions equal the
intrinsic ones by their pure-tensor uniqueness characterizations (`transition_eq`), and
`coneNaturality` then proves the signed-cone transition equations. The chain-map model uses Mathlib right fractions followed by an actual
flat-term K-flat resolution. The cone tensor identity follows from Mathlib's signed cone
comparison and the proved generic naturality equation on its two summands. The two cone
definitions are irreducible, with explicit equations used in the proof. The ordinary proper/open
coefficient square is isolated as the genuine coefficient-change lemma
`compactSupportProjectionCoefficientChange`.

The ordinary inner tensor and invertibility of its completion unit are proved as
`WeilConjectures.ordinaryProjectionInnerConstructible`, with exactly the qcqs finite-type
hypotheses of the item. The unclaimed `IntegralReductionTowerUnrestricted` abbreviates its
duplicate scalar witness by `scalarReductionExistence`; both bodies are identical universal
constructions with the same standard localizations. This addresses repeated witness unfolding in
the 60-second compile limit. `unrestrictedIntegralComplexFunctor` keeps its original body
(reviewer correction: rewriting it as the composite of the recorded scalar functors broke the
direct importers `IntegralOperationsWellDefined` and `CompletedTensorFiniteShift`). `finiteArrow` now explicitly writes its identical
endpoints, so projecting them does not traverse the large curried projection functor. The change
record lists all textual users; no consumer statement is changed.

## Proved and sorry left

Closed the original hole
`WeilConjectures.ConcreteIntegralProjection.concreteIntegralProjectionCone` with a complete
proof from the recorded dependencies, the proved ordinary-inner lemma, and the
coefficient-change theorem below. Its theorem has no remaining `sorry`. One genuine portion
remains as a public whole-proof `sorry` declaration:

* `WeilConjectures.PurCompactSupport.compactSupportProjectionCoefficientChange`,
  node `lem-pur-compact-support-projection-coefficient-change`: the ordinary
  proper/open coefficient-change identity, containing no completion, Tor or cone claim.

The new theorem `WeilConjectures.ordinaryProjectionInnerConstructible` is fully proved, by
applying the already proved ordinary pullback and representative-normalized tensor helpers
through a private `import all SfProEtaleProjectionFormula`.

Accounting: one original hole closed (1 of 1), one hole added, zero holes left in the item, one
left in the delivery. This is a decomposition, with no net decrease in holes. The lower theorem
is only the coefficient-change identity, with no completion, constructibility, Tor, cone or
transition conclusion.

## No longer needed

The chain-map representative does not use `Sheaf.Paper.KFlatMapFactorization`
(`lem-pur-kflat-map-factorization`): Mathlib right fractions and a resolution of the roof's
source already give a map into a chosen flat-term K-flat target. Cone K-flatness reuses the
proved coefficient-independent cone-closure lemma from
`DerivedChangeOfRingsIndependentCoefficients` through a private `import all`. Its proof tensors
the signed cone and uses the triangulated subcategory of acyclic complexes. The generic
total-tensor triangulation theorem is unnecessary. Removed private imports
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`,
`Sheaf.Paper.PrincipalKoszulStrictReplacement`,
`Sheaf.Paper.RoosIntrinsicCompletenessEquivalence`,
`Sheaf.Paper.SfDerivedCompleteLegacyComparison`, `Sheaf.Paper.KFlatMapFactorization`,
`Sheaf.Algebra.Homology.KFlatHomotopyTriangulated`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Sheaf.Paper.IntegralCompactSupportPrescribedReductions`, and
`Sheaf.Paper.BasicOperationsCoefficientReduction`. The qcqs compact-support realization and its
finite-comparison theorem provide exactly the compact-support constructibility and canonical
comparisons needed here. The dimension lemma is used only in the proof of ordinary pullback
constructibility. The original `lem-coef-integral-compact-support` and
`lem-fix-operation-reduction` are replaced as direct proof dependencies by these qcqs interfaces
and the ordinary coefficient square, respectively. Their lower mathematics may still be needed
by those nodes; this delivery does not withdraw any source declaration or shared module. Removed
obsolete direct `tool_uses` entries `lem-kun-dimension-finite-type`,
`lem-coef-integral-compact-support`, `lem-fix-operation-reduction`,
`lem-pur-kflat-map-factorization`, and `lem-sfb-kflat-homotopy-triangulated`, without adding
approvals. The definitions of triangulated categories and complete integral objects remain in
the statement closure; they are not separate proof obligations here.

## Where the brief, the DAG or earlier work was wrong

Repair of returned head `4323f3c7baf` (reviewer C-4323f): that review answered FIX, with
corrected files for `ConcreteIntegralProjectionCone.lean`, `IntegralReductionTowerUnrestricted.lean`,
two change records, the item node and this report; the landing then failed only because a
change-record override was named `D6-cone-transition-normalization.md` instead of
`D6-cone-transition-normalization.change.md`. Head `27f527a01d86` re-delivered the unfixed files;
the reviewer re-applied the C-4323f corrections (see `## Reviewer corrections`), with override
names ending in `.change.md`.

The earlier sandbox attempt restored the quarantined item; the current shared source also
contains it. Its theorem statement and node attachment are preserved. The previous attempt used
an auxiliary intrinsic/legacy completeness conversion. It is unnecessary: the tensor-domain
proof supplies invertibility of the actual unit directly. Additional instance exclusions are
local to this file. Some alternative projection-domain interfaces required structural
separatedness of X and Y. The assigned theorem has no such assumptions. The new inner-tensor
statement uses the existing proof that only needs the qcqs finite-type domain; no held module is
adapted.

The stated operation-reduction conjunction supplies adjunction mate equations but has no literal
ordinary proper/open tensor square with these normalized comparison maps. The new lemma records
exactly that missing portion of step 3, without assuming projection invertibility or
equality-detection by finite reduction.

## New nodes

`lem-pur-compact-support-projection-coefficient-change`, in
`Sheaf.Paper.CompactSupportProjectionCoefficientChange`, records the ordinary proper/open
coefficient square. Its proof in words is the counit mate computation and the open-unit
normalization, checked on flat K-flat representatives. Zero inputs, empty schemes, identity
coefficient maps and nonflat quotient maps satisfy the same calculation; no faithfulness of
reduction is used.

`lem-sf-ordinary-projection-inner-constructible`, in
`Sheaf.Paper.OrdinaryProjectionInnerConstructible`, records the ordinary inner tensor on the
actual qcqs domain. It reuses the existing proved private helpers for ordinary pullback, finite
dimension and the constructible tensor completion comparison. Identity morphisms, empty schemes
and zero inputs satisfy the statement.

Change records: `coord/changes/D6-cone-transition-normalization.md` and
`coord/changes/D6-unrestricted-reduction-witness.md` and
`coord/changes/D6-finite-arrow-endpoints.md`,
`coord/changes/D6-cone-comparison-endpoints.md`,
`coord/changes/D6-target-unit-endpoints.md`.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer corrections (2026-10-26)

* `coneTransition`: original body restored (explicit type and `[irreducible]` kept);
  `intrinsicConeTransition_eq` now proved by `transition_eq` and `coneNaturality`.
* `unrestrictedIntegralComplexFunctor`: original body restored; the change record
  `D6-unrestricted-reduction-witness.md` now covers only the existence witness and the functor.
* Node `lem-sf-concrete-integral-projection-cone`, last proof step text adjusted accordingly.
* Re-applied on head `27f527a01d86`, which had re-delivered the unfixed `4323f3c7baf` files.
