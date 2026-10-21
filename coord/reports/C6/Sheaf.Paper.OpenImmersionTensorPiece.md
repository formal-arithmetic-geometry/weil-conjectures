## What changed

Proved `SheafOfModules.openTensorProjection_exists` in
`Sheaf.Paper.OpenImmersionTensorPiece`. The open adjunction has invertible unit. The ordinary
extension-tensor formula, K-flat resolution, and preservation of totalization show that the
derived tensor of an extended object is again extended. The counit on that tensor is therefore
invertible. The adjunction transpose defining the normalized projection is a composite of
isomorphisms. Its naturality follows from naturality of the unit and the supplied comparison.
All auxiliary lemmas are private and proved in this module. The added monoidal namespace
opening is documented in
`coord/changes/open-immersion-tensor-piece-proof-namespace.md`; preflight requested that
record for its conservative command-scope check.

Added proof imports for the adjoint triple, ordinary ringed-slice tensor formula,
independent-coefficient K-flat resolution, tensor exactness comparison, tensor mapping cones,
total-complex preservation and the acyclicity API. Updated the projection-existence node's
proof route and the existence node's explanation. Existing public signatures, definitions,
public imports and the unit route are unchanged. No other module is adapted.

## Proved and sorry left

Closed the sole hole: `SheafOfModules.openTensorProjection_exists`.
The module has zero remaining `sorry`s. Added zero holes and split off zero statements.
`openImmersionTensor_exists` and `openImmersionTensor_iso` retain their complete assembly and
uniqueness proofs. The module compiles on the project server within the single-file limit.
`#print axioms` for `openTensorProjection_exists` and `openImmersionTensor_iso` reports
exactly `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.

## No longer needed

The direct proof route no longer needs:

- `def-weil-pbc-strict-perfect-coefficient-package` for invertibility: support works for any
  derived coefficient. Its module `Sheaf.Paper.StrictPerfectPackageOnSite` remains a public
  statement dependency defining the coefficient subcategory.
- `lem-pc-bounded-above-flat-kflat-site` and its module
  `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`: use a general K-flat resolution instead.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` as a proof dependency: the supplied
  comparison is already a natural isomorphism. Its module
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` is not used directly.
  The related public import `Sheaf.Paper.ProEtaleCanonicalTensorPullback` stays for the
  existing statements.
- `lem-weil-pbc-site-derived-tensor-descent` and its module
  `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`: use the tensor model's representative
  comparison and the mapping-cone criterion directly.

No existing public import is removed, and no module is withdrawn. These are removals of
this node's direct proof dependencies; other consumers can still need the listed modules.

## Where the brief, the DAG or earlier work was wrong

The planned finite-free retract argument, bounded totalization and explicit descent are
unnecessary here. The ordinary extension-tensor theorem already holds for all modules;
extension preserves arbitrary sums. Its lift to total complexes and the open adjunction
therefore give support for all derived coefficients, with no boundedness argument.
The stated projection direction and normalization are preserved exactly. No statement error
or definition repair was needed.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
