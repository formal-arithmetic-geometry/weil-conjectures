## What changed

Restored the assigned quarantined module from
`quarantine/Sheaf/Paper/DirectedGaloisFiniteTensorGenerators.lean`, preserving its public
imports and the complete signature of
`AlgebraicGeometry.Scheme.GaloisPartition.finite_tensor_generators`.

Replaced its hole by a compiling reduction to two separate results of ILO XVII:
Proposition 7.4.6 (finite tensor extension closure) and Proposition 7.4.3 with Lemma 7.4.4
(exhaustion by constructible subobjects). The new statements do not repeat the original
statement: neither asserts normalized subobject filtrations, directedness, or a small filtered
colimit presentation. The consuming proof supplies these constructions.

The proof reuses the proved `subobject_filtration_of_closure` helper through a private
`import all WeilConjectures.CategoryTheory.FiniteFiltrationRefinement`. It transports retracts
under isomorphism, proves constructibility of the filtration terms by extension induction,
and proves directedness using images of finite sums in the exact weak subcategory. It then
shrinks the subobject poset, constructs its diagram in MonoOver, proves the colimit comparison
monic, uses exhaustion to identify its image with top, and obtains the required colimit.
Empty schemes, zero sheaves, and the mandated empty filtrations are handled explicitly.

The complete sandbox compiles through lcompile.py. No existing public signature, definition,
source-library module, target, or unit record is changed. The item node now records the actual
assembly; each new source result has its own module and node. Searches included LeanSearch,
LeanFinder, Loogle, Mathlib grep, the project Lean trees and the imported blueprint. Generic
filtration and Grothendieck-category results were reused; no existing fixed-partition tensor
or exhaustion theorem was found.

## Proved and sorry left

One original hole closed:
`AlgebraicGeometry.Scheme.GaloisPartition.finite_tensor_generators`
(node `lem-per-directed-galois-finite-tensor-generators`). The item module has zero holes.

Two holes added, each the whole proof of a public named theorem:

- `AlgebraicGeometry.Scheme.GaloisPartition.exists_tensor_filtrationClosure`, in
  `Sheaf.Paper.DirectedGaloisTensorFiltrationClosure`, node
  `lem-per-directed-galois-tensor-filtration-closure`.
- `AlgebraicGeometry.Scheme.GaloisPartition.constructible_subobject_sup`, in
  `Sheaf.Paper.DirectedGaloisConstructibleSubobjectSup`, node
  `lem-per-directed-galois-constructible-subobject-sup`.

This is a decomposition, not a net hole reduction: one hole closed, two added, net minus one
before the ledger's import-closure accounting. The two new statements concern separate source
propositions and are strictly parts of the original argument. Their docstrings and nodes give
complete natural-language proofs and their existing lower dependencies. The finite tensor
statement includes only abstract finite-extension generation; the exhaustion statement is
only a universal upper-bound property. Directedness and the categorical realization are
proved here rather than left as additional holes. No sorry occurs in a definition or a private
helper. No arbitrary data is installed in a definition from an existence theorem.

Edge cases checked: empty X, E=0, zero coefficient ring, empty generator list on empty X,
and nonempty indexing of the union by the zero subobject. No invertibility of ell or finite
underlying set of A is assumed.

## No longer needed

Removed these direct private imports from the item:

- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.RingTheory.FiniteAlgebraExternalTensorFiltration`
- `Sheaf.ConstructibleSheaf.GaloisCoverModuleDescent`
- `Sheaf.RepresentationTheory.NormalSubgroupIndUnipotence`
- `Sheaf.AlgebraicGeometry.TorsionLocalSystemMonodromy`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre`
- `Sheaf.SixFunctors.GeometricInverseImageConstantModule`
- `Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility`
- `Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`
- `WeilConjectures.SixFunctors.OpenClosed.Exact`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `WeilConjectures.SixFunctors.OpenClosed.Stalk`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.ConstructibleSheaf.GaloisDescentMonodromyTensor`
- `Sheaf.DeligneLaumon.ConstructibleExtensionFiniteStage`

These are not wholesale mathematical pruning: the geometry, monodromy, algebra filtration,
tensor comparisons and finite-stage extension remain needed in the appropriate new lower
source-result nodes. The retained direct Grothendieck-category import supplies the actual
colimit construction. The main node's proof_deps lists only its assembly dependencies.

In the exhaustion extension step, the constructible extension-closure clause of the existing
`exact_refinement` theorem directly supplies constructibility of the finite-stage middles.
The former separate uses of `lem-sfb-discrete-noetherian-constructible-serre`,
`lem-sfb-noetherian-global-constructibility`, and
`lem-sc-noetherian-finite-module-finite-presentation` are unnecessary for that step. This does
not withdraw their modules or source declarations. No whole module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned module is quarantined, not withdrawn. Its absence from lean/ was reconciled
with coord/rework.tsv and its archive; the original declaration is restored.

The cited lower results do not directly supply the normalized subobject-chain interface or
the small directed presentation in the item statement. The new source propositions isolate
the geometric content, and the item now proves that categorical glue explicitly. Ambient
subobjects of a weak-class object need not remain in the same fixed class, so the directedness
proof uses images inside its exact abelian full subcategory rather than asserting ambient
Serre closure. There is no change to the unit route or to any statement of the paper.

## New nodes

`lem-per-directed-galois-tensor-filtration-closure` records ILO XVII 7.4.6 with 7.4.7 and
the directed stratum filtration. It provides a finite prime-field family uniformly over A
and only finite-extension-closure membership. It inherits the blueprint ancestor and unit
of the assigned item. Its source steps retain the needed descent, monodromy, tensor and
open/closed dependencies; all three required kinds of Mathlib search are recorded.

`lem-per-directed-galois-constructible-subobject-sup` records the exhaustion assertion of
ILO XVII 7.4.3, proved via 7.4.4. It states only that every upper bound for the constructible
subobjects in the fixed class is top; it does not bundle directedness or a colimit. Its proof
retains the finite-orbit, finite-stage extension and directed-stratum induction. It inherits
the same blueprint ancestor and unit, with the searches recorded. No change record is needed:
no existing statement or definition was changed.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
