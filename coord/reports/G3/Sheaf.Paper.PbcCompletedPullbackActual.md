## What changed

Proved ten original theorems of `Sheaf.Paper.PbcCompletedPullbackActual`, without
changing any public statement, definition, or public import. The actual module
adjunction composes the existing canonical inverse-image adjunction with the
normalized scalar-extension adjunction. Its unit is checked on sections, and
unit extensionality proves uniqueness.

The ordinary derived-pair existence and universality proofs use the already
specified `completedOrdinaryPullback_exists` and canonical right derived pair.
The left composite is checked on a K-flat resolving class; the comparison with
a universal resolving-class construction is an isomorphism on every object.
The right composite uses K-injective derivability. Pullback shifts are obtained
from the right Kan extension, with uniqueness proved degree by degree. Direct
image shifts use the K-injective equivalence and are uniquely detected on
K-injective representatives. Completeness of completed pullback follows from
the reflector's full-subcategory codomain.

Three proved private helpers supply shift-structure extensionality, Kan shift
uniqueness, and compatibility of the canonical right-derived unit with shifts.
The last follows the existing equivalence-and-resolution argument in
`WeilConjectures.AlgebraicGeometry.PinnedDerivedAdjunctionShifts`.

Added proof-only imports of the canonical pro-etale module-unit comparison,
normalized scalar-extension/restriction adjunction, coherent right Kan shifts,
and independent-coefficient K-flat resolutions. The first two use `import all`
to access their already proved private normalized adjunction constructions.
The assigned file compiles through `lcompile.py` (23.9 seconds after pruning).

## Proved and sorry left

Closed 10 of the 13 original holes:

- `AlgebraicGeometry.Scheme.pbcActualModuleAdjunction_exists`
- `AlgebraicGeometry.Scheme.pbcActualModuleOperations_additive`
- `AlgebraicGeometry.Scheme.pbcActualPull_hasLeftDerived`
- `AlgebraicGeometry.Scheme.pbcActualPullUniversal`
- `AlgebraicGeometry.Scheme.pbcActualDirectUniversal`
- `AlgebraicGeometry.Scheme.pbcActualDerivedLeftComposite`
- `AlgebraicGeometry.Scheme.pbcActualDerivedRightComposite`
- `AlgebraicGeometry.Scheme.pbcActualPullShift_exists`
- `AlgebraicGeometry.Scheme.pbcActualPushShift_exists`
- `AlgebraicGeometry.Scheme.pbcActualCompletedPull_isComplete`

Three original holes remain, with their original statements and complete proof
plans unchanged. Each carries blueprint tag
`lem-weil-pbc-ringed-topoi-module-adjunction`:

- `AlgebraicGeometry.Scheme.pbcActualCompleteInclusion_isRightAdjoint`
- `AlgebraicGeometry.Scheme.pbcActualCompletionShift_exists`
- `AlgebraicGeometry.Scheme.pbcActualDirectCompletionIso_exists`

No holes added, no split-off statements, and no changes to data constructions.
These are proofs from the existing declared dependencies, some of which still
contain their own original holes; this is not a claim that the target axioms
check is already complete.

## No longer needed

Removed direct proof imports:

- `Sheaf.Algebra.Homology.DiagramKFlatReplacements`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct` (the shared
  repository currently spells this import
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`)
- `Sheaf.Algebra.Homology.KFlat`

The diagram replacement node `lem-weil-pbc-diagram-kflat-replacements` is not
used by these proofs. The ordinary derived pair is already specified, and
single-complex independent-coefficient K-flat resolutions suffice to prove
absoluteness of the left composite. No new tensor-product construction or
fresh proof of quasi-isomorphism preservation is needed here. The removed
modules can remain dependencies of the existing constructions they define;
this delivery does not claim they are globally unreachable. No unit statement
or realized unit proof step has been bypassed or withdrawn.

## Where the brief, the DAG or earlier work was wrong

No node has `lean.module` equal to this assigned module. All its declarations
are tagged `lem-weil-pbc-ringed-topoi-module-adjunction`, but that node's Lean
attachment is `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction` and
its statement concerns arbitrary geometric morphisms. Its proof does not
describe this file's additional completed-coefficient derived and reflector
assertions. I have not overwritten that different theorem's node with this
specialized proof. The independent reviewer should retain this attachment
mismatch for the maintainer to repair.

The remaining reflection and completion comparisons require an explicit
identification of `PbcIsIntrinsicallyComplete` (existential generators and a
representative over the comparison coefficient presentation) with the
fixed-generator predicate `WfIsComplete` in
`Sheaf.Paper.WeilCompletedTensorReflector`, or with locally derived ringed-ideal
completeness. Those predicates are not definitionally equal. The generic
ringed-site reflector and pushforward/completion statements also use equal
site object and morphism universes, requiring a proved small-model transport
before they can apply here. The integral-specific predicate comparison in
`CompletedCoefficientPresentationTransport` does not cover arbitrary `d`.
`SfIntegralConstructibleTriangulated` cannot supply shift closure here: it
imports this assigned module and its intrinsic triangulation proof uses
`pbcActualCompletionShift_exists` itself. These issues are left explicit in
the original three upper statements rather than replaced by equivalent holes
under new names.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
