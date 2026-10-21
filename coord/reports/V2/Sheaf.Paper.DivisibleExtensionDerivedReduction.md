## What changed

Proved the five remaining theorems of Sheaf.Paper.DivisibleExtensionDerivedReduction.
Constructed the ordinary sheaf tensor/restriction adjunction and obtained its
normalized derived adjunction using the existing resolving-class compatibility
interfaces. Constructed actual residue actions on torsion sheaves. Compared the
multiplication triangles with the quotient and rotated Kummer triangles, then
lifted the normalized pure-object isomorphisms into the residue derived category.
The coefficient unit is computed on its K-flat single complex.

For inverse image, exact preservation of multiplication cokernels gives the
ordinary comparison. A derived adjunction mate is invertible by multiplication
short exact sequences and resolutions. This proves the full universal-counit
representative formula, without assuming preservation of K-flatness. Its mate
unit equation proves both normalized identification squares and the boundary
square. The generic comparison and naturality arguments are separate, fully
proved lemmas; neither is a renaming of the item.

The public theorem signatures and mathematical data are preserved. Presentation
and Identifications are now abbreviations for general records with exactly their previous ten and
four fields and equations, respectively. Profiling identified the specialized
record as expensive for the kernel to check; the general records are checked at abstract category types. The ordinary
morphism-naturality proof is also a private general lemma in the same file,
with the sheaf theorem obtained by specialization.
Explicit annotations on the chosen adjunctions and private proved APIs avoid
unfolding large constructions. A change record documents these proof interfaces.
No consumer or adopted source-library module is modified.

Validation: both new theorem modules and the item compile, with the item taking
53.3 seconds in the combined check and no compiler warning. Unmodified
GeoCartierExponentIndependence (the external declaration user) and
GeoCartierCycleClass also compile against the changed item. The unmodified
CartierReductionSiteComparison times out at 60 seconds both with the sandbox
outputs and against the original published build, so this independent consumer
limit is not a record-change failure. That file only imports the item and does
not reference its declarations. DiagonalTowerSystem likewise only imports the
item and times out both with the sandbox outputs and against the original
published build. Neither original consumer is included in this packet.

Return repair (head 544d9853b): added both omitted declaration users,
Sheaf.AlgebraicGeometry.ResidueKummerDerivedUnit and
Sheaf.AlgebraicGeometry.ResidueQuotientDerivedUnit, to the change record
`## Users` table. Their split presentations use the unchanged ten fields,
and their Kummer/quotient normalization arguments use the same derived
adjunction and identification equations. Refreshed the current downstream
scan (148 transitive importers), listed all six current direct importers, and
recorded CartierReductionData, which now carries the previous site-comparison
import. No consumer source needs adaptation. The combined server check compiled the
three delivered modules and unchanged copies of both missing users with no
warnings: CokernelAdjointExchange 7.5s, NormalizedScalarBoundaryNaturality 8.8s,
DivisibleExtensionDerivedReduction 40.6s, ResidueQuotientDerivedUnit 34.3s and
ResidueKummerDerivedUnit 8.9s. The temporary consumer copies were removed
from the packet after this check.

## Proved and sorry left

Closed the five original holes:

- SheafOfModules.sheafDerivedScalarAdjunction_exists
- SheafOfModules.DivisibleReduction.presentation_exists
- SheafOfModules.DivisibleReduction.divisible_extension_derived_reduction
- SheafOfModules.DivisibleReduction.coefficientIso_existsUnique
- SheafOfModules.DivisibleReduction.inverse_image_natural

Added zero holes. No sorry remains in any delivered Lean module. The two new
generic theorems are proved. Existing imported statements remain their own items;
this delivery uses their recorded interfaces rather than reproving them.

## No longer needed

Removed proof-dependency imports that the actual proof does not use:

- Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
- Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
- Sheaf.Algebra.Homology.KFlat
- Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
- Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
- Sheaf.Algebra.Homology.KFlatIndependentCoefficients
- Sheaf.CategoryTheory.RingedSiteModules

The normalized resolving-class derivation replaces the planned use of
lem-pc-derived-adjoint-functors, lem-pc-pre-derived-adjoint-functors-general and
lem-weil-pbc-exact-functor-derived-functor. A direct tensor Hom equivalence replaces
lem-weil-pbc-ringed-topoi-module-adjunction in this item's proof. Exact cokernel
exchange replaces lem-weil-pbc-ringed-topoi-derived-tensor-pullback in the
inverse-image step. No diagram K-flat replacement is needed. The node's proof
and proof_deps now follow these arguments. The remaining type/flatness modules
above are supplied through public statement dependencies; removing their direct
proof imports does not assert that their mathematics is globally unused.

No adopted source declaration or module is withdrawn. No whole module is claimed
globally pruned; these dependencies may remain needed by other parents. The
Cartier unit and its own realized steps are retained.

## Where the brief, the DAG or earlier work was wrong

The old inverse-image plan required preservation of K-flat resolutions. The
statement supplies exact additive lifts and a restriction square, which suffice
by a more direct argument: preservation of multiplication short exact sequences
shows the target counit computes on the image of a flat-term source resolution.
The derived mate comparison then follows. The public statement is unchanged.

No mathematical counterexample or disputed statement was found. The cases n=1,
zero objects, split extensions and zero torsion/quotient are covered by the same
cokernel and adjunction arguments. The generic exchange theorem also handles n=0
whenever its explicitly required resolving/monicity assumptions hold.

## New nodes

- def-sfb-normalized-reduction-identifications: the four-field general normalized
  identification record, in the item module.
- def-sfb-scalar-reduction-presentation: the general record underlying Presentation,
  in the item module; exactly the previous fields and equations.

- lem-sfb-derived-cokernel-adjoint-exchange: exact exchange for derived cokernel
  adjunctions, in Sheaf.CategoryTheory.DerivedCategory.CokernelAdjointExchange.
- lem-sfb-normalized-scalar-boundary-naturality: normalized quotient, Kummer and
  boundary squares, in
  Sheaf.CategoryTheory.DerivedCategory.NormalizedScalarBoundaryNaturality.

The two lemmas are fully proved and lie strictly within the inverse-image part
of the item. The definition records contain actual data fields, with no choices
or holes.

Change record: coord/changes/divisible-extension-derived-reduction-normalized-apis.md.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
