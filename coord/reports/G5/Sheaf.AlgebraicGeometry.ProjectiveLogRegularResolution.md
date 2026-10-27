## What changed

Replaced the sole sorry in `AlgebraicGeometry.exists_projective_log_regular_resolution`
with a compiling assembly proof. Its signature and public imports are unchanged.

The proof derives torsion-free characteristic groups from sharp saturation, chooses the
existing monoidal resolution tower, and uses the existing finite-tower log calculus to
obtain its actual composites. A proved private helper turns `IsIdentity` into equality of
log morphisms, including every relative-test section map. Terminal log etaleness gives
log smoothness; ILO VI 1.8 gives log regularity. The existing free-characteristic criterion
(ILO VI 1.7) gives regularity, after converting ULift/Finsupp free monoids to finite tuples.
A further proved helper derives integrality from the dense-open isomorphism and regular
stalks. The mixed log-composition clause proves the final universal log-smooth assertion.

Two new modules isolate the remaining geometry for a **fixed supplied tower**:
`SaturatedLogTowerProjectivity` and `SaturatedLogTowerDenseOpen`. Neither constructs a
resolution tower, imposes terminal freeness, or concludes terminal regularity. They are
strictly smaller pieces of the original argument. No definitions, instances, attributes,
existing signatures, other existing modules, or target statements changed.

Validation: both new statement modules compiled in 3.7--4.0 seconds; the final item
compiled without warnings in 4.2 seconds through lcompile.py. The existing theorem's
source signature was compared byte for byte. Length zero, empty schemes (in the general
helper statements), unit centers, trivial characteristic, rank zero, and the identity
composite were checked against the statements and proofs in words.

## Proved and sorry left

Original holes: 1. Removed the original hole in
`AlgebraicGeometry.exists_projective_log_regular_resolution`
(node `lem-per-log-regular-projective-log-resolution`). The item module now has zero holes.
This is a decomposition, not a claim of a sorry-free resolution proof: the assembly uses
existing stated dependencies and the two new geometric subproblems below.

Added holes: 2, each a named public theorem with proof exactly `:= by sorry`:

- `AlgebraicGeometry.saturatedLogTower_isHProjective`,
  node `lem-per-saturated-log-tower-projectivity`,
  module `Sheaf.AlgebraicGeometry.SaturatedLogTowerProjectivity`.
- `AlgebraicGeometry.saturatedLogTower_denseOpen`,
  node `lem-per-saturated-log-tower-dense-open`,
  module `Sheaf.AlgebraicGeometry.SaturatedLogTowerDenseOpen`.

The packet closes 1 upper hole and adds 2 lower holes (net -1 by raw hole count).
Existing imported theorems retain their own outstanding proofs; none was edited.

## No longer needed

No module is withdrawn, and no global module pruning is claimed. The old direct proof
imports below were removed from the item:

- `Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension`.
- `Sheaf.TraceFormula.ProjQcOpenTwistAmple`.
- `Sheaf.AlgebraicGeometry.AmpleRestrictClosedImmersion`.
- `Sheaf.AlgebraicGeometry.CoherentLogIdealChartConstruction`.
- `WeilConjectures.Blowup.FiniteDegree.Algebra`.
- `WeilConjectures.Blowup.Proper`.
- `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale`.
- `Sheaf.AlgebraicGeometry.ProperMorphismFpqcDescent`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `Sheaf.AlgebraicGeometry.PolarizedFineLogEtaleDescent`.
- `Sheaf.AlgebraicGeometry.ProperRelativeAmpleProjectiveBundle`.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleComposition`.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective`.
- `Sheaf.AlgebraicGeometry.LogRegularCompletedChart`.
- `WeilConjectures.RingTheory.StrictHenselizationNoetherian`.
- `WeilConjectures.RingTheory.StrictHenselizationRegular`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `WeilConjectures.RingTheory.StrictHenselizationDimension`.

The projectivity-related tools (affine Proj scalar extension, shrinking an immersion,
ample twists and closed restriction, coherent log ideal charts, ordinary blowup charts
and properness, fpqc properness descent, canonical log-ideal polarization and polarized
descent, relative ampleness descent, bundle projectivity, composition and H-projectivity)
remain dependencies of the new projectivity node's proof plan. Their removal as direct
Lean imports is not a claim that this geometric work is unnecessary.

Original step 7's completed-chart/formal-chart verification and original step 8's separate
strict-henselization proof are replaced at the item by the existing general
`lem-sfb-log-smooth-preserves-log-regularity` and
`lem-trf-free-characteristic-regular-boundary`. These are generic tools (ILO VI 1.8
and 1.7), not replacements of a Fourier unit step. The latter's normal-crossings
conclusion is not used. Their proofs still reach several of the same local-algebra
nodes, so those nodes are not globally pruned. The original generic-point dimension and
triviality-locus argument remains in the dense-open node. The node records distinguish
these remaining plans from the Lean assembly proved here.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan rederived two regularity facts already
stated in more general form. Reusing them gives a shorter assembly while retaining the
monoidal tower and chart/polarization approach. This route uses no normalized-blowup
identification or excluded regularization theorem.

The two newly used off-unit tools are
`lem-sfb-log-smooth-preserves-log-regularity` (log smooth over log regular implies log
regular) and `lem-trf-free-characteristic-regular-boundary` (free characteristics imply
regularity). The maintainer should review these as generic tool uses; their statements
are exactly ILO VI 1.8 and VI 1.7, read in the supplied source. No top-level maintainer
`tool_uses` approval was added. The item's existing historical blueprint provenance and
the fixed unit realization are preserved. The latest ancestor proof no longer spells out
the Q108 re-admitted geometric construction, as the existing item already records.

## New nodes

`lem-per-saturated-log-tower-projectivity` packages original steps 1 and 3--6 for an
arbitrary fixed tower over a quasi-compact fs scheme immersing in finite projective space
over an affine base. It drops integralness, log regularity, excellent/Noetherian base and
terminal freeness, and concludes only projectivity of that supplied composite. Its proof
in words uses toric ordinary blowup base change, finite saturation, canonical tautological
polarization, descent and projective-bundle composition. The source and all existing
proof-dependency declarations are recorded. Blueprint-wide searches found no duplicate.

`lem-per-saturated-log-tower-dense-open` packages the birational part of original steps
9--10 for any fixed tower with log regular endpoints, without integralness, regularity,
terminal freeness or projectivity. It proves only the dense-open isomorphism commuting
with the supplied composite. The docstring and node give the generic-point rank-zero
argument, unit reflection on saturated fraction charts, the universal property over the
triviality locus, and finite iteration. Integrality is proved separately in the item.
Blueprint-wide searches found no duplicate. No change record is needed: only the item's
proof, its proof-route fields, and new modules/nodes were changed.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
