## What changed

Replaced the proof of `AlgebraicGeometry.ProEtale.CondensedRing.qcqs_proper_constructible_closed_baseChange` by finite Postnikov induction from the degree-zero constructible-sheaf exchange. The main declaration, coefficient predicate, public imports, universes and hypotheses are unchanged. The proof constructs the shift-compatible isomorphism locus of the actual ambient mate and applies the proved `DerivedCategory.prop_of_bounded`. The returned delivery duplicated an existing private theorem. This repair removes
`constantModelConstructible_iso`, adds
`import all Sheaf.Paper.IndConstructibleFilteredColimits`, and applies its existing
proved `AlgebraicGeometry.ProEtale.constructible_iso`. Both qcqs and affine-local
branches are already covered there. The imported module itself is unchanged. The
abstract private helper `isIso_of_bounded_cohomology` retains the finite Postnikov
assembly while preventing expansion of concrete coefficient pullbacks.

Added `Sheaf.Paper.ProperConstructibleClosedExchangeHeart` for the degree-zero subargument. It has no Tor hypothesis, no auxiliary base S or map q, and retains exactly the six coefficient topologies. Its documented closed-test argument uses the existing proper w-contractible rigidity theorem for every coefficient family, avoiding separate scalar/completion arguments. Updated both nodes to describe this route. This is a decomposition, not a completed proof of proper base change.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ProEtale.CondensedRing.qcqs_proper_constructible_closed_baseChange` by a complete bounded-complex assembly from the named degree-zero theorem. The private `isIso_of_bounded_cohomology` is proved. Isomorphism closure now uses
`AlgebraicGeometry.ProEtale.constructible_iso` directly; the rejected duplicate was
removed. The repair adds no theorem holes beyond the one retained split below.

Added one hole: `AlgebraicGeometry.ProEtale.CondensedRing.proper_constructible_closed_exchange_heart`, node `lem-sfb-proper-constructible-closed-exchange-heart`. No other sorry is retained or added in the delivered files. Counts: one original hole replaced by one strictly degree-zero subproblem; net holes closed minus added is zero. The finite Postnikov induction is discharged; the sheaf closed-test calculation remains.

The latter needs normalized identification of derived evaluation in `properClosedFibreDerivedRestriction` with `sectionsOver`, compatibility with the common Jacobson closed-point fibre, and affine-open descent for the actual mate. Existing declarations provide the geometric rigidity and normalized test exchange separately, but do not directly state that composite comparison. The new theorem records the complete argument and all these dependencies, rather than assuming that arbitrary endpoint isomorphisms identify the maps.

## No longer needed

The rejected private `constantModelConstructible_iso` is no longer needed and was
removed. No existing source-library declaration is changed. The private import of
`Sheaf.Paper.IndConstructibleFilteredColimits` supplies the existing proved theorem.

The following private imports were removed from the item:

- `Sheaf.Paper.KFlatScalarComparisonNormalization`
- `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence`
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`
- `Sheaf.Paper.FiniteLevelProEtaleBaseChange`
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
- `Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Sheaf.Algebra.Homology.RoosConeCalculus`
- `Sheaf.Paper.DerivedNakayamaFirstReduction`
- `Sheaf.CategoryTheory.PastedMatesCounitNormalization`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift`
- `Sheaf.CategoryTheory.ExactDerivedComposition`
- `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`
- `Sheaf.CategoryTheory.ModuleObjects.LiftExact`
- `Sheaf.AlgebraicGeometry.QcqsProperLocalizingCoproducts`
- `Sheaf.CategoryTheory.Triangulated.LocalizingIsoLocus`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedCounit`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Mathlib.CategoryTheory.Shift.CommShift`
- `Mathlib.CategoryTheory.Adjunction.Limits`
- `Mathlib.Topology.Constructible`

The coefficient-specific proof dependencies below are no longer used by the chosen route (this is a claim about this proof, not deletion of their declarations or a claim that other target branches no longer use them):

- `lem-sfb-finite-coefficient-derived-exchange-identification`
- `pqf-lem-proper-basic`
- `thm-weil-pbc-finite-level-proetale`
- `lem-sfb-qcqs-integral-finite-model-completeness`
- `lem-sfb-integral-ambient-tower-comparison`
- `lem-sfb-integral-quotient-exchange-comparison`
- `det-pe-derived-nakayama-first-reduction`
- `lem-derived-exact-equivalence-squares`
- `lem-sfb-scalar-geometric-exchange-rectangle`
- `lem-sfb-qcqs-rational-integral-localizing-generators`
- `lem-sfb-qcqs-proper-integral-rational-scalar-comparison`
- `lem-sfb-qcqs-proper-localizing-coproducts`
- `lem-weil-pbc-left-adjoint-preserves-colimits`
- `det-sf-determination-localizing`
- `lem-weil-pbc-exact-functor-complex-cohomology`

The old direct dependencies retained only by the degree-zero subproblem are:

- `lem-sfb-qcqs-closed-pullback-finite-model-completion`
- `lem-weil-pbc-proper-fp-permanence`
- `lem-sfb-internal-module-operations-transport`
- `lem-sfb-nonaffine-closed-test-exchange-identification`
- `lem-sfb-proper-wcontractible-closed-fibre-rigidity`
- `lem-pur-scheme-constructible-preimage`
- `lem-sfb-scalar-matrix-inverse-image`

The existing `tool_uses` list is filtered in place, preserving its order, to approvals still used by the item's new statement/proof dependencies. Obsolete approvals correspond to the removed imports and coefficient-specific route listed above. No source-library declaration or module is removed or changed.

## Where the brief, the DAG or earlier work was wrong

The return at a3fc4a84688 correctly identified the duplicate isomorphism-closure
theorem. Lean's `import all` makes the existing private theorem available in this
proof, so no visibility change or consumer adaptation is needed.

The Lean docstring still described the superseded six-step scalar-extension argument, whereas the current node already used closed lifted tests for the all-continuous algebraic closure. The rigidity theorem's actual coefficient disjunction covers all six families, so that same argument applies uniformly. The finite Tor condition is unused in the finite Postnikov passage.

The current DAG's phrase “functorial restriction identifies their composite” hides a real interface obligation: its rigidity statement derives evaluation in the module category, while the test restriction uses exact pullback followed by derived sections. Their canonical comparison and composition normalization must be proved; the availability of separate isomorphic endpoints does not supply it. The new degree-zero node makes this obligation explicit. No existing statement or definition was weakened.

The unit's closed-complement proper-base-change route is retained. The new node also names generic ringed slice localization and ringed open descent, with internal-module transport, as normalization tools; their use is below the unit level. These may require maintainer tool approvals because they belong to other units. No approval list was extended by this delivery.

## New nodes

`lem-sfb-proper-constructible-closed-exchange-heart` states the sheaf-in-degree-zero part of the proper closed exchange argument, without finite Tor amplitude. The parent combines it using the existing canonical shifts and proved finite Postnikov induction. Empty source or closed subscheme, the zero finite coefficient ring, and the zero ring in the lifted tests are allowed. In the common-closed-point calculation, if I lies in Jac(B), then Jac(B/I)=Jac(B)/I, so the two quotients agree even for the zero ring; this algebraic calculation was checked separately in Lean during development. No definitions or existing statements changed. The static proof-context changes are
documented in `coord/changes/n1-closed-base-change-proof-context.md`; no consumer
adaptation is required.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
