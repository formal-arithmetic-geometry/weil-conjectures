## What changed

The original theorem is assembled from local lattice comparison and intrinsic-fibre
exactness/zero detection. The intrinsic point functor is exactly the original `omega`;
its comparison is the identity. No target statement or existing definition changes.

The original definitions move verbatim to the publicly re-exported
`Sheaf.Paper.AdicNormalizedFibreData`, avoiding cycles. The new `LocalLattices` record
packages only the local calculation, and `GeometricPoint` indexes the exact family.
The module-location change record is `coord/changes/b9-normalized-fibre-data.md`.
No adopted `WeilConjectures` module is edited.

Three separate mathematical arguments are proved: finite freeness of normalized stalk
limits, faithful exact H⁰ realization of the heart, and detection by exact families of
abelian functors. The lattice finite-dimensionality consequences are also proved.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre.
adic_normalized_fibre_exactness` (one original hole). This is a decomposition, not a
complete proof of the geometric theorem: two geometric holes are added.

The new holes, each a whole public theorem with source and full proof in words, are:

- `AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre.
  intrinsic_local_lattice_comparison`, node `lem-per-intrinsic-local-lattice-comparison`.
- `AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre.
  intrinsic_constructible_fibre_exactness`, node
  `lem-per-intrinsic-constructible-fibre-exactness`.

No other delivered theorem or definition contains `sorry`. In particular these are proved:
`Padic.normalized_tower_finite_free`, `Padic.towerLimitEquivSections`,
`Padic.normalized_tower_limit_finite_free`, `CategoryTheory.exact_family_detection`,
`NormalizedFibre.realize_faithful`, `NormalizedFibre.realize_short_exact`,
`NormalizedFibre.lattice_fiber_finite_free`, `NormalizedFibre.lattice_rationalFiber_finite`
and `NormalizedFibre.intrinsic_fiber_finite` (the last uses the explicit LocalLattices input).

The algebra argument includes rank zero: lift a p-annihilated quotient element, cancel p
in the DVR, move to the previous tower component, and conclude every component is zero.
Units times uniformizer powers give torsion-freeness. The finite-module limit theorem and
Mathlib PID freeness finish. The categorical argument permits an empty index family:
its zero-detection hypothesis then forces the source category to be zero.

## No longer needed

The node `det-lem-coefficient-heart-closure` is no longer needed by this proof route:
abelianness of the existing heart and the proved faithful exact realization supply the
formal image/kernel/cokernel argument. Its module is not withdrawn, since other consumers
may still need it. All other original geometric dependencies remain in the two retained
geometric arguments, or are used in the proved algebra.

No module is withdrawn. DAG parents and the blueprint unit route still need the original
statement. The original main proof no longer directly imports:
`Sheaf.Paper.PbcRationalCategory`, `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
`Sheaf.Paper.CoefficientHeartClosure`, `Sheaf.Paper.CoefficientHeartCommonStratification`,
`Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`,
`Sheaf.Paper.LisseCompletedSystemComparison`,
`Sheaf.NumberTheory.Padics.AdicLimitFiniteModules`,
`Sheaf.Paper.EtaleLocalMonodromyRealization`,
`Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`,
`Sheaf.CategoryTheory.SiteInverseImageTensor`,
`Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal`,
`Sheaf.AlgebraicGeometry.CondensedConstructibleSerre`,
`WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant`,
`Sheaf.Paper.PointProEtaleSectionsExact`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`.

The algebra imports AdicLimitFiniteModules and ExtensionIntegersDvr through its genuine
proof dependencies. The geometric comparison and intrinsic exactness/zero detection
retain the original relevant DAG dependencies. Removing direct main-file imports does
not claim those geometric dependencies are globally unused. The main formal detection
argument uses abelianness of the heart and faithful exact realization; it does not require
a separate ambient constructible kernel/cokernel closure lemma. No upstream declaration
is removed or replaced by a hole.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is sound, but its interfaces are not immediate applications in the
original coefficient presentation. `CompletedLisse.Base.E` is in `Type (u+1)` while the
intrinsic definitions take E in `Type u`; its completed and continuous coefficient rings
also use a different presentation. The etale-local lattice theorem is stated for E in
`Type`, rather than the universe-polymorphic coefficient used here, and presents slice
restriction rather than canonical balanced module inverse image. These require actual
universe and coefficient transports, not unfolding or changing the original statement.
The two geometric theorems isolate those source results and their transports, without
claiming the existing stated declarations are an obstacle simply because they have holes.

The finite-free limit argument is absent from the existing finite-module theorem: its
finite generation conclusion is used, and torsion-freeness is proved separately here.

## New nodes

`def-per-adic-normalized-fibre-data` retains every moved declaration attachment and the
two new record types; it asserts no existence.

`lem-per-normalized-tower-finite-free` proves finite freeness of actual normalized free
module towers and compares compatible sections with the categorical limit.

`lem-per-exact-family-detection` proves the joint detection argument for arbitrary
abelian categories and exact additive functors.

`lem-per-normalized-heart-realization` proves faithful exact H⁰ realization using the
single embedding, t-bounds and distinguished triangles.

`lem-per-normalized-lattice-finite-free` applies the algebra to the actual lattice stalk
tower and transfers finite dimensionality across a local normalization.

`lem-per-intrinsic-local-lattice-comparison` isolates BS 6.8.4's local lattice existence,
pullback-compatible normalization and integral/fractional map naturality. It asserts no
finite dimensionality, exactness or detection.

`lem-per-intrinsic-constructible-fibre-exactness` isolates BS 6.8.5/6.8.7's exactness and
zero detection for the intrinsic functor. The local splitting and monodromy/stratum
arguments are retained, including the affine refinement before separated comparison.
It asserts neither lattice normalization nor the other detection claims.

The two retained geometric results are strictly parts of the argument; the compiled
assembly performs finite dimensionality and all further detection in Lean.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
