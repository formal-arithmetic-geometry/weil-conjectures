## What changed

Filled ten original theorem holes in `Sheaf.Paper.ConstantGeometricStalkUnit`.
Finite multiplication is the canonical pullback-of-unit map under the unit-preserving
left-adjoint comparison. A proved generator formula and coefficient naturality give
its quotient square. Linearity extends the integral unit normalization from one to all
sections. The strict unit and canonical Weil unit choose from the identical
uniqueness proposition, so their comparison is a definitional equality.
Finite point sections use bijectivity of sheafification at the final algebraically
closed point; completed sections reuse the existing proved completion calculation.
The section reductions follow from sheafification naturality and the actual limit lift.
The semilinear return calculation applies to every specified embedding. Rational unit
coordinates descend through the published fully faithful size lift, with uniqueness.
The rational operator identity follows from the existing integral identity and the
stated rational scalar square by cancellation and faithfulness.

Only this module and its proof-plan node change. Public signatures, definitions,
public imports, and the unit route stay unchanged. The scalar-square theorem is moved
before its use. Added a private proof import of all
`Sheaf.Paper.PointSectionsScalarExtension` to reuse its proved completed-section helper,
and a proof import of
`WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology` for the cohomology of
E concentrated in degree zero.
New private helpers are fully proved; no new public declarations or holes are added.
The private import's auxiliary derived-category instances are disabled in this module
to retain the published localization and category instances.

Validation: the complete module compiled cleanly through the prescribed remote
compiler in 43.0 seconds, below the 60-second delivery limit. The integral
Weil-unit comparison avoids repeated elaboration of the large normalization predicate.

## Proved and sorry left

Closed 10 of the 16 original holes, all in namespace
`WeilConjectures.ConstantGeometricStalkUnit`:

- `finiteUnitHom_isIso`
- `integralUnit_canonicalWeil`
- `finiteUnit_reduction`
- `integralUnit_projection`
- `section_isIso`
- `section_reductions`
- `embeddingPoint_compatible`
- `embeddingPoint_return`
- `rationalStalkUnit_existsUnique`
- `rationalOperator_unit`

Six original holes remain, all attached to
`lem-zl-constant-geometric-stalk-unit` with their existing source and proof docstrings:

- `integralChainUnit_existsUnique`
- `integralChainUnit_isIso`
- `finiteUnit_canonicalWeil`
- `finiteOperator_unit`
- `integralOperator_unit`
- `rationalOperator_scalar`

Holes added: zero. Split-off statements: zero. This is a partial proof delivery,
not a claim that the entire constant-stalk theorem is closed.

## No longer needed

Removed the following unused direct proof imports:

- `Sheaf.FieldTheory.UniqueSubfieldOfClosure`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.SixFunctors.FrobeniusPointTransportNatural`
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.ConstantCoefficientScalarNormalization`
- `Mathlib.CategoryTheory.Limits.HasLimits`
- `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`
- `Sheaf.Paper.IntegralPullbackComparisonRealization`
- `Sheaf.Paper.IntegralPointTransportTowerPowers`

The continuous-function section presentation in
`lem-pur-proetale-finite-constant-sections` is no longer a direct proof dependency of
this node: final-object sheafification computes the specified finite section map.
Removed its obsolete top-level tool-use approval; the other approvals retain their order.
No modules or declarations are withdrawn. Dependencies of the six remaining holes
stay recorded in the proof plan; this does not claim that these modules are globally
unreachable from other targets.

## Where the brief, the DAG or earlier work was wrong

No false statements or required definition repairs were found. The finite-section
argument has a shorter existing proof via `lem-trf-point-sheafification-final`.
This is a proved source-library point-site lemma used as a generic tool; no node of
the trace-to-determinant unit is bypassed. The completed-section calculation already
exists in `PointSectionsScalarExtension`; its private helper is reused with the
actual coefficient map and carrier lift. Both dependencies are recorded in the node.

The local `literature/blueprint/latest` symlink points to `main-20261026`, whose
requested trace-to-determinant files were unavailable in this read-only mirror.
The supplied reviewed expansion, DAG proof, unit record, and existing Lean proofs
were read; no older blueprint snapshot was substituted.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
