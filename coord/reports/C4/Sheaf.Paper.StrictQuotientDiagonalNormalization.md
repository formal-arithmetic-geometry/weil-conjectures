## What changed

Constructed the ordinary strict quotient ring map, exact diagonal, normalized tower
realization, scalar insertion and tensor comparison. Proved the diagonal preserves
flat-term K-flat complexes using the geometric projection and the normalized identity
scalar model. Factored the ordinary presentation data into a public module to avoid
an import cycle. The two ring constructors keep their original bodies as named
definitions so the derived proof can avoid expanding sequence-site data. The representative
natural transformation has an explicit component formula for its four-square composite. Its inserted complex-composition isomorphisms
are identity on every degree.

The derived restriction and reduction are saved as model fields with defining equalities
to the original composites. The ordinary construction fills these fields by those actual
functors. Their equality transports preserve the canonical representative comparison.

The proof treats the exact derived constant functor together with its cochain
factorization as a private record. The generic normalization proof takes this actual
comparison data as a parameter; the public theorem specializes it to the original
canonical functor. This avoids repeating its localization construction throughout
the proof and adds no assumption to the public statement. The existing quotient
presentation is also an explicit parameter of the comparison and unit proofs;
the original theorem specializes it to the published quotient presentation.

A generic witness assembler combines the ordinary presentation and derived comparison
witnesses with the eleven proved clauses. It avoids repeating the full site-specific
statement in additional helper declarations; all mathematical proofs remain in the
assigned module. The completion-unit calculation is generalized over the ordinary
unit and its defining equation, then specialized using the existing
`ordinaryUnit_spec` API.

The derived argument uses flat K-flat representatives and K-injective resolutions,
the universal quotient-tower comparison, and the constant/limit adjunction. It preserves
the assigned theorem's complete statement, including its completion-unit equation.

Definition/interface record:
`coord/changes/strict-quotient-diagonal-presentation-module.md`.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.ConstantCompletion.strictQuotientDiagonalNormalization`: 1 of 1.
No holes were added or split off. The constant-sequence equivalence, ordinary flat
presentation and complete representative API are proved with zero holes.

The consumer's existing hole in
`CategoryTheory.AdicSites.PerfectQuotientExchange.perfectQuotientExchangeNormalization`
is unchanged. No other delivery declaration contains `sorry`.

Validation: the complete five-module packet compiled through `lcompile.py --all`
on the project server, with every file below the 60-second limit. The assigned
normalization compiled in 55.6 seconds; the adapted consumer compiled in 25.0 seconds.

## No longer needed

The proof does not use the proof of `constant_completion_equivalence`, a completed
pullback adjunction, a diagram-site realization of the ringed category, or a separate
fraction decomposition. The constant-completion and diagram-site definitions remain public imports.
The unused `Sheaf.Paper.CompletedPullbackAdjunction` import is removed; no
source-library declaration is removed.

The direct proof imports removed from the original item are:
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
`Mathlib.Algebra.Homology.DerivedCategory.Fractions`,
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`,
`Mathlib.CategoryTheory.Localization.CalculusOfFractions`,
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`, and
`Mathlib.Algebra.Homology.BifunctorShift`.
The new proof also avoids a direct import of
`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction` by proving the small
presheaf tensor-restriction formula locally. Some imports remain transitively available;
none is claimed globally withdrawn.

The following old direct proof dependencies are unnecessary for the new argument:
`lem-pc-left-localization-fraction-representation`,
`lem-pc-quasi-isomorphisms-multiplicative-system`,
`lem-weil-pbc-kinjective-hom-derived`, and
`lem-weil-tower-category-levelwise-abelian`. The scalar-restriction API supplies
conservativity, the constant/limit adjunction supplies normalization, and localization
supplies descent. These were removed from the active tool approvals where present.

The obsolete top-level approvals also drop
`lem-sp-completed-pullback-adjunction`,
`lem-weil-pbc-constant-completion-equivalence`,
`lem-weil-pbc-diagram-site-realization`, and
`lem-weil-pbc-exact-functor-derived-factorization`. Their public data and definitions
remain available; the new argument does not invoke their theorem statements.

Other old direct dependencies are now statement dependencies or are used through
proved imported APIs: the sheaf/module/K-flat definitions, diagram-site definitions,
sheafification, exact derived factorization and constant-completion data. This delivery claims no global withdrawal of those nodes or modules.

## Where the brief, the DAG or earlier work was wrong

The original node combined an ordinary normalized tensor construction with derived
comparison and limit normalization. They are proved using the existing scalar,
sheafification, localization and resolution interfaces; direct derived-tensor or
fraction calculations are unnecessary. No statement is disputed or weakened.

## New nodes

`def-pur-strict-quotient-diagonal-presentation` owns the moved presentation data and its
representative API. The structure retains all section equations and fields.

`lem-pur-constant-sequence-module-equivalence` constructs the normalized equivalence
between modules over a constant sequence ring and ordinary towers.

`lem-pur-strict-quotient-ordinary-flat-presentation` constructs the ordinary presentation
and proves its diagonal flatness and K-flatness; it assumes no derived comparison or
completion-unit assertion.

## Forced adaptations

`Sheaf.Paper.PerfectQuotientExchangeNormalization` is unclaimed. Its original source
was compiled against the changed dependencies and failed at line 135:2 in
`reductionComparison` and line 145:2 in `restrictionComparison`. Both reported `error: Application type mismatch: The argument`. In the first,
`(extend d.ringMap).map (d.diagonal.mapDerivedCategoryFactors.hom.app P)`
was expected to start at `d.reductionD.obj ((Q (T.ring A)).obj P)`. In the second,
`d.towers.functor.mapDerivedCategory.map` applied to the restriction factorization
was expected to start at
`d.restrictionD.obj ((Q (strictQuotientRing T.topology A I)).obj P)`.
The underlying mismatches have the same cause: the old first factor starts at the canonical composite functor,
whereas the declared source now uses the saved model functor. No other original
consumer error was reported.

The only changes to that consumer are the following two inserted body lines:

- New line 135: `d.reductionDIso.hom.app ((Q (T.ring A)).obj P) ≫`
- New line 146:
  `d.restrictionDIso.hom.app ((Q (strictQuotientRing T.topology A I)).obj P) ≫`

These equality-isomorphism components transport from the saved models to their
canonical composites before applying the unchanged original factors. All existing
consumer signatures, visibility and other lines are preserved. The assigned theorem's
statement was also checked against the original source and is byte-for-byte unchanged.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
