## What changed

Proved `AlgebraicGeometry.ProEtale.AdmissibleScalarRealization.admissible_scalar_realization_exact`
from the existing flatness and coefficient interfaces and one new, separate compact-adic
coefficient comparison. All original public definitions and the theorem signature are unchanged.
The item contains the complete finite/discrete argument, exact scalar realization on every
module, all field cases, the arithmetic hypotheses for both integral cases, transport of
completed-constant flatness across the canonical scalar isomorphism, and flatness on slices.

The shorter route uses the existing PID constant-to-continuous flatness theorem on the point.
It treats the actual continuous algebraic-closure coefficient ring without restricting sections
to a finite subextension. The finite case includes the zero ring and does not use the redundant
annihilating-exponent hypothesis. The completed integral argument covers every generator of the
recorded maximal ideal. Reconstructed section actions are kept behind their proved APIs; the
large flatness transport needs 800000 elaboration heartbeats and compiles within 60 seconds.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.AdmissibleScalarRealization.admissible_scalar_realization_exact`.
The item itself has zero remaining `sorry` occurrences. Added one hole in
`AlgebraicGeometry.ProEtale.compact_adic_continuous_identification`, node
`lem-sfb-compact-adic-continuous-identification`, in the new module
`Sheaf.Paper.CompactAdicContinuousIdentification`.

This is a decomposition: one original hole closed, one strictly smaller and reusable
coefficient-identification hole added, net zero. The new result contains no exactness,
Noetherianity, extension flatness, localized flatness, finite-discrete case or field case.
It is formulated for arbitrary compact Hausdorff principal-adic domains with finite quotients,
rather than repackaging the original six-case theorem. Its docstring and node give the
construction, normalization, and uniqueness proof, including the continuity of division by a
nonzero uniformizer power on its compact image.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization`,
`Sheaf.CategoryTheory.FiniteTypeConstantExact`, `Mathlib.LinearAlgebra.Basis.VectorSpace`,
and `Mathlib.Algebra.Module.Projective`.

The item's proof no longer needs the declared nodes
`lem-weil-pbc-finite-type-constant-exact` (exactness follows directly by exact functor composition),
`lem-sf-module-object-ordinary-coefficient-equivalence` (finite constants are compared directly),
`lem-weil-pbc-completed-constant-sheaf-reduction` (use the narrower proved
`flat_presented_completion` interface),
`lem-weil-pbc-vector-space-projective` and `def-weil-pbc-projective-module` (the PID flatness route
also covers fields), and `lem-sfb-coefficient-sections-localization` (restrict the local
relations criterion directly). `lem-weil-pbc-pid-noetherian-normal` is not needed as a separate
proof dependency: Mathlib infers Noetherianity from the PID structure. The existing public
import of CompletedConstantSheafReduction stays because its definitions occur in the public
interface; no source declaration or module is withdrawn. No unit statement or realized unit
step is bypassed. The retained finite-normalization dependency supplies the canonical scalar
map and private reconstruction API. The obsolete top-level tool approvals removed from the
item node are `lem-weil-pbc-finite-type-constant-exact`,
`lem-sf-module-object-ordinary-coefficient-equivalence`,
`lem-weil-pbc-completed-constant-sheaf-reduction`, and
`lem-sfb-coefficient-sections-localization`, in their original relative order. The new lemma
module removes the unused proof imports ContinuousRingUniverseRealization and
ContinuousCoefficientModuleEncoding after its proved sectionwise support was isolated.

## Where the brief, the DAG or earlier work was wrong

The planned integral-limit invocation does not directly have the signature required here.
It uses a RingCat tower of ULift quotients, while this item uses CommRingCat quotients of ULift
scalars and quantifies over every uniformizer. Its normalization is on all profinite test
functions; this item asks uniqueness from constant-scalar normalization alone. The latter
requires an argument modulo every uniformizer power, not only the limit universal property.
The new node supplies precisely this missing coefficient argument. The uniqueness proof uses
open residue fibres and continuous division on the compact image of multiplication by a
nonzero power. Empty objects are handled by sheaf locality, not by choosing a point.

The recorded absolute-value topology is not definitionally the spectral-norm topology.
The application explicitly transports along the existing proved topology equality.
No statement has been weakened, no definition changed, and no arbitrary object is selected
from an unproved mere-existence theorem.

## New nodes

`lem-sfb-compact-adic-continuous-identification` supplies the normalized coefficient comparison
for compact Hausdorff principal-adic domains with finite positive quotients. Both Z_l and O_E
are checked against its hypotheses in Lean. Its private support proves local constancy of
quotient maps, unique lifting of compatible residues by compactness, continuity from the
residue coordinates, total disconnectedness, transport of the adic basis to ULift, and the
sectionwise universal property of the continuous residue cone, and continuous division by a
nonzero uniformizer power for functions with constant residue. A proved sheaf-local
extensionality helper then shows that ring-sheaf maps agreeing on constants agree everywhere
when their target kills the selected uniformizer power. The continuous-function presentation
also has a constructed isomorphism with the completed constant quotient tower. The remaining public hole
is the normalized categorical comparison, including uniqueness from constant scalars. Its source is the integral comparison's finite
constant, representability, and ring-operation argument, with the scalar uniqueness argument
written out. Mathlib searches used LeanSearch, Loogle, LeanFinder and source grep; none supplied
this sheaf comparison. The command-scope change record is
`coord/changes/Q2-admissible-scalar-proof-scope.md`; no existing definition or signature changes.

The proof import of ProEtaleIntegralCoefficientLimit is retained to preserve the unit route.
The generic comparison supplies the stronger scalar-normalized interface used here. The four
private instance declarations are local instances, so their registration is scoped to this file.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
