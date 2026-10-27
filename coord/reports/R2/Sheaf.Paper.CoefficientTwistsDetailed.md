## What changed

Proved `WeilConjectures.integralCoefficientTwist_constructible` using the existing
rank-one signed-power interface, the completed-line derived reduction and completeness
theorem, preservation of rank one by scalar extension, finite-line models, and the
constructible-single support theorem. The uniform cohomological interval is [0,0], also
on the empty scheme and at zero and negative exponents.

Proved `WeilConjectures.twistScalarMaps_identity` from the existing unique-family theorem.
The actual completed coefficient inclusion and constant integer map are identities;
the identity semilinear family satisfies all four published normalization clauses.
Uniqueness identifies it with the chosen canonical family.

Proved `WeilConjectures.twistScalarMaps_composition` from the same unique-family
theorem. Quotient induction proves composition of the actual coefficient maps. The
composite semilinear family satisfies all four normalization clauses, so uniqueness
identifies it with the direct family.

Proof elaboration prioritizes the existing integral-tower derived-category instance.
The composite semilinear family uses Mathlib scalar restriction and its composition
isomorphism. This reuses the abstract linearity proof instead of reconstructing it over
the completed coefficient rings. The normalization argument uses explicit equalities
on positive tensors and negative evaluations instead of expanding the entire family.
The composition statement explicitly applies identity functions on the native target
carriers. These definitionally equal annotations prevent comparison of the same carrier
with two different restricted module structures. The isolated statement's kernel check
dropped from about 19 seconds to 2.2 seconds. The instance preference is local; no public
attribute changes.

Only proof imports were added. Existing binders, mathematical statements, definitions,
and public imports are unchanged; the composition type has only explicit identities.
The signed integral-line node records the shorter proof from general line results. A separate DAG-only correction removes the spurious dependence of the generic
finite-line tensor theorem on the Tate-twist definition, with the exact statement
unchanged and all five direct citers audited.

Change records: `coord/changes/R2-generic-finite-line-dependency.md` and
`coord/changes/R2-scalar-composition-carriers.md`.

## Proved and sorry left

Closed three of nine original holes:

- `WeilConjectures.integralCoefficientTwist_constructible`
  (lem-pur-signed-integral-coefficient-twist-constructible).
- `WeilConjectures.twistScalarMaps_identity`
  (def-coefficient-twists-detailed).
- `WeilConjectures.twistScalarMaps_composition`
  (def-coefficient-twists-detailed).

Added zero holes; no statements were split off. Six original holes remain unchanged,
all in the existing coefficient-twist construction (def-coefficient-twists-detailed):

- `WeilConjectures.integralComplexTwist_constructible`.
- `WeilConjectures.twistScalarMaps_existsUnique`.
- `WeilConjectures.twistLineScalarIso_existsUnique`.
- `WeilConjectures.twistSheafScalarComparison_existsUnique`.
- `WeilConjectures.rationalTwistScalarComparison_unit`.
- `WeilConjectures.coefficientTwistStageComparison_coherent`.

This is a partial proof delivery, not a decomposition. The full module compiled cleanly
with lcompile in 53.2 seconds, within the 60-second limit. The delivery tool also records
its compilation and preflight checks.

## No longer needed

No import or module was removed or withdrawn. The integral coefficient-line proof no
longer directly repeats the root-local-model and integral-local-model constructions,
identifies its reductions with separately built finite Tate lines, or reconstructs a
surjective-tower Roos triangle. These steps are provided by the general completed-line
and finite-line interfaces. The root-local-model modules and surjective-tower theorem
remain needed transitively by those interfaces and the first-line rank theorem, so no
global pruning of those modules is claimed.

The replaced direct proof dependencies are:

- `lem-pur-twist-root-local-models` (`Sheaf.Paper.PurTwistRootLocalModels`):
  the existing first-line rank theorem supplies the local-freeness input.
- `lem-pur-twist-integral-local-models` (`Sheaf.Paper.PurTwistIntegralLocalModels`):
  the general completed-line theorem supplies reduction and completeness.
- `lem-weil-proetale-surjective-tower-derived-limit`
  (`Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit`):
  completeness is reused through the completed-line interface.
- `def-weil-integral-derived-reduction`
  (`Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`):
  the general completed-line theorem already states the required reduction formula.
- `def-weil-proetale-constructible-sheaf`
  (`Sheaf.Paper.ProEtaleFixedModuleConstructible`):
  the finite-line models and constructible-single theorem provide its required properties.
- `def-weil-derived-complete-integral-detailed` (`Sheaf.Paper.SfIntegralConstructible`):
  the complete predicate remains the unchanged statement; its proof is supplied by
  the general completed-line theorem.

These nodes remain used by the reused interfaces or existing statements. No whole
module is claimed to be pruned from the target closure.

The generic finite-line node no longer needs def-coefficient-twists-detailed in its
statement dependencies, proof dependencies, or proof step. It uses the existing generic
sheaf-module and tensor definitions instead. This removes a false bookkeeping cycle
without deleting any mathematical unit or proof step.

## Where the brief, the DAG or earlier work was wrong

The generic finite-line tensor node had a paper-specific dependency not present in its
statement or compiled Lean imports. Adding the genuine existing completed-line and
finite-line dependencies to the integral coefficient-line node would otherwise create a
DAG cycle through the intrinsic twist interface. The correction and complete citer audit
are in its statement_change record and the change record cited above. No Lean statement
was false or changed.

The direct general-line argument suffices for integral coefficient-line membership:
constructibility of the finite scalar reductions needs only rank one over the finite
constant coefficient ring. An explicit comparison with the independently constructed
finite Tate lines is unnecessary for this assertion.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
