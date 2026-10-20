## What changed

Proved `AlgebraicGeometry.Etale.baseChange_towardsSpecField` with its statement unchanged.
The proof establishes degree zero over every ground field by perfect closure and reduction,
then uses cumulative degree induction, the declared failure theorem, and normal generic-fibre
vanishing. Explicit Cartesian transport identifies its chosen witness with the canonical model.
Canonical cyclic module structures and the coefficient comparison handle sheaves killed by n.
Filtered-colimit preservation and the canonical torsion-kernel comparison handle general torsion.
Six new supporting modules are fully proved. All added imports in the item are proof imports.
All seven delivered Lean files compiled together. The required delivery dry run passed
(preflight commit f9b70a58b0, CODEX). It reported axiom-probe timeouts for the abelian
higher-direct-image, constant-square transport, and degree-zero support modules; its
message says these probes are retried at merge. No independent axiom-closure claim is made.
No existing definition or statement changed; no consumer adaptation or change record is needed.
The unit `sk-prop-sf-kunneth-ordinary` has no realized statement or proof steps to bypass.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Etale.baseChange_towardsSpecField`.
Added 0 holes and split off 0 unfinished theorems. The delivery has zero `sorry` occurrences.
The six supporting public theorems are also proved:

- `AlgebraicGeometry.Etale.isZero_constantHigherDirectImage_of_isomorphic_square` (`lem-kun-constant-higher-direct-image-square-iso`).
- `AlgebraicGeometry.Etale.exists_moduleLift_of_nsmul_eq_zero` (`lem-kun-n-torsion-module-lift`).
- `AlgebraicGeometry.Etale.preservesColimitsOfShape_abelianHigherDirectImage` (`lem-kun-abelian-higher-direct-image-filtered-colimit`).
- `AlgebraicGeometry.Etale.unboundedCumulativeFieldBaseChange_zero` (`lem-kun-field-degree-zero`).
- `AlgebraicGeometry.Etale.isIso_exactExchange_colimit` (`lem-kun-abelian-exchange-filtered-colimit`).
- `AlgebraicGeometry.Etale.isIso_exchange_of_isIso_torsion_pieces` (`lem-kun-torsion-exchange-filtered-passage`).

The proof uses declared dependencies with their existing proof status; it does not claim
that their transitive axioms have all been discharged. In particular the cumulative failure,
normal vanishing, and unbounded coefficient/degree-zero comparison declarations are inputs.
Edge cases checked in the constructions: empty schemes, negative cohomological degrees,
n=1 (the zero cyclic module), and n=0 for the general canonical module-lift lemma.
The target only uses positive n invertible in the original field.

## No longer needed

Removed the following direct proof imports from the item:

- `Sheaf.Paper.KunBcMapOnCohomology`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`.
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageColimits`.
- `Sheaf.AlgebraicGeometry.DerivedSquareIsoPasting`.
- `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`.
- `Sheaf.AlgebraicGeometry.StalkFaithfulDerived`.
- `WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism`.
- `Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance`.
- `Sheaf.AlgebraicGeometry.UnboundedCumulativeUniversalBaseChangeProperty`.
- `Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField`.
- `Sheaf.AlgebraicGeometry.AbelianDegreeZeroFlatBaseChange`.
- `Sheaf.AlgebraicGeometry.FieldExtensionExchange`.
- `Sheaf.AlgebraicGeometry.InvertibleOrdersColimit`.

The algebraic-closure higher-exchange and conservative stalk descent route is unnecessary:
`lem-kun-0f1c`, `lem-weil-pbc-algebraic-extension-embeds-algebraically-closed`,
`lem-weil-pbc-derived-square-iso-pasting`, `lem-weil-pbc-mate-pasting`,
`lem-weil-pbc-derived-inverse-image-composition`,
`lem-kun-stalk-faithful-derived`, and `lem-kun-sep-closure-conservative` are not used here.
Only degree-zero descent is required, and purely inseparable perfect closure gives equivalences.
Affine-X localization (`lem-kun-bc-base-change`) is also unnecessary: the induction and the
normal vanishing declaration already apply to arbitrary finite-type X.
`lem-kun-bc-map-on-cohomology` is unnecessary: the proof works directly with the specified
exact exchange and its homology. `lem-kun-0eys` is replaced by the already proved module
flat degree-zero theorem `sbc-lem-degree-zero-flat-base-change`.
`def-weil-pbc-hypercohomology-filtrations` and `lem-kun-zn-sheaf-invertible-orders` are not
needed: natural-number cumulative induction and direct construction of cyclic coefficients suffice.
Several removed imports remain needed transitively by the new support modules: reduction,
geometric reducedness, filtered-colimit preservation, torsion colimits, exactness, and
universal-homeomorphism invariance. Their direct imports were removed, not their mathematical use.
The node proof dependencies now record the actual route. No global unreachability claim is made.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The declared normal vanishing and cumulative failure results
hold over an arbitrary field, so passage to an algebraic closure in higher degrees is avoidable.
The reduction theorem returns the Mathlib universal-topological-homeomorphism predicate;
the exchange API uses the project's integral/radicial/surjective class. Its surjective closed
immersion clauses supply that class directly, avoiding an unformalized converse equivalence.
The proof keeps the prescribed unit route; only the below-unit reductions are shortened.
Generic tools from other units are the existing flat degree-zero theorem, exactness and
colimit preservation, topological invariance, and coefficient comparison. Their use is needed
for the respective categorical comparisons; no tool approval fields were added.

## New nodes

`lem-kun-constant-higher-direct-image-square-iso`: Constant higher direct images in isomorphic Cartesian presentations. Module `Sheaf.AlgebraicGeometry.ConstantHigherDirectImageSquareIso`; fully proved.

`lem-kun-n-torsion-module-lift`: Canonical cyclic module coefficients on a sheaf killed by n. Module `Sheaf.AlgebraicGeometry.NTorsionModuleLift`; fully proved.

`lem-kun-abelian-higher-direct-image-filtered-colimit`: Filtered colimits of abelian higher direct images. Module `Sheaf.AlgebraicGeometry.AbelianHigherDirectImageFilteredColimit`; fully proved.

`lem-kun-field-degree-zero`: Universal cumulative degree-zero exchange over a field. Module `Sheaf.AlgebraicGeometry.DegreeZeroFieldBaseChange`; fully proved.

`lem-kun-abelian-exchange-filtered-colimit`: Exact derived exchange commutes with a filtered colimit of sheaves. Module `Sheaf.AlgebraicGeometry.AbelianExchangeFilteredColimit`; fully proved.

`lem-kun-torsion-exchange-filtered-passage`: Exchange reduces to the canonical invertible-order torsion kernels. Module `Sheaf.AlgebraicGeometry.TorsionExchangeFilteredPassage`; fully proved.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
