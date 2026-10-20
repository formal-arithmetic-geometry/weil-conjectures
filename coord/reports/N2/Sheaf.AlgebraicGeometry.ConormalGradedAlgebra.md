## What changed

Repair of the return on delivery head `07ff8649a`: added all three omitted
consumers to the relocation change record's `## Users` table:
`Sheaf.AlgebraicGeometry.ConormalAlgebraAffineGenerators`,
`Sheaf.AlgebraicGeometry.ConormalAlgebraHomogeneousRingMap`, and
`Sheaf.AlgebraicGeometry.ConormalAlgebraRingAdjoint`.
Read their current declarations and proofs: they import the original module and
use the unchanged `power`, `powerInclusion` and `homogeneousClass` definitions
through its public re-export. Their statements and proofs need no adaptation.
The repair changes documentation only; the retained proof packet is preserved.
Recompiled all seven retained packet modules successfully, then compiled unchanged
copies of all three consumers against the packet's compiled modules: all passed.
Those consumer copies are only verification scratch files and are not delivered.
Re-ran the current downstream use scan for all six relocated definitions; every
listed user is covered by the updated change record.

Completed `exists_conormalGradedAlgebra` from the separate affine algebra
construction. The proof establishes the fixed ideal-power identification,
quasi-coherence, normalized pushforward quotient, degree zero, coherence under
exactly the stated Noetherian assumption, symmetric comparison, unique normalized
augmentation, and the unique inclusion-preserving algebra isomorphism between
presentations. The augmentation and comparison are built as module maps using the
coproduct, then proved to be algebra maps using the normalized affine charts and
sheaf separatedness. Their uniqueness proofs use genuine coproduct extensionality.

Proved the new normalized degree-piece, conormal, total-algebra and symmetric-algebra
stalk comparisons. The conormal comparison includes compatibility with the actual
quotient-stalk scalar map; the symmetric comparison requires no quasi-coherence.
Moved six unchanged definitions to `ConormalGradedAlgebraBasic` to avoid an import
cycle. The original module publicly re-exports them. No target or source-library
signature or body is changed, and no consumer needs a forced adaptation.

The remaining `exists_affineData` is the source's construction of the total algebra:
its statement asks only for the sheaf coproduct, representative operations and
normalized affine charts. It does not assume or repackage the stalk, conormal,
symmetric, augmentation, finiteness or uniqueness conclusions proved here. Its
source, full argument and edge cases are recorded in its docstring and node.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.ConormalGradedAlgebra.exists_conormalGradedAlgebra`.
The item module contains zero `sorry`.

Added one hole:
`AlgebraicGeometry.ConormalGradedAlgebra.exists_affineData`, node
`lem-pur-conormal-graded-algebra-construction`.
Thus this delivery is a decomposition: one upper hole closed, one strictly smaller
construction hole added, net zero holes closed. It is not claimed as a complete
axiom-free proof of the target.

The following new public theorems are fully proved, with no new holes in their modules:
`AlgebraicGeometry.ConormalGradedAlgebra.conormal_stalk`,
`AlgebraicGeometry.ConormalGradedAlgebra.graded_piece_stalk`,
`AlgebraicGeometry.ConormalGradedAlgebra.affineData_stalk_chart`, and
`AlgebraicGeometry.SymmetricAlgebraSheaf.stalk_iso`.
All private helpers in the packet are proved. All existing data definitions retain
real construction bodies; no arbitrary witness is chosen in a new public definition.

Single-file checks compile the complete upper proof and all four new stalk lemmas.
The total-stalk proof keeps tensor pullback locally irreducible to prevent expensive
unfolding; relaxed elaboration options are scoped to the proofs. The per-file time
limit is unchanged. The delivery tool compiles the complete packet and checks
its declarations, nodes and interfaces before pushing.

## No longer needed

Removed these imports from the item (some remain necessary through the separate
construction or are publicly available through the basic module; no claim of global
withdrawal is made):

- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`
- `Mathlib.Algebra.Category.ModuleCat.Stalk`
- `Mathlib.Algebra.Category.Ring.Colimits`
- `Mathlib.Algebra.Module.FinitePresentation`
- `Mathlib.Algebra.Module.LocalizedModule.Exact`
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`
- `Mathlib.AlgebraicGeometry.Modules.Tilde`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.StructureSheaf`
- `Mathlib.CategoryTheory.Abelian.Images`
- `Mathlib.Geometry.RingedSpace.Basic`
- `Mathlib.LinearAlgebra.Quotient.Basic`
- `Mathlib.LinearAlgebra.SymmetricAlgebra.Basic`
- `Mathlib.LinearAlgebra.TensorProduct.Map`
- `Mathlib.Topology.Sheaves.Functors`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.RingTheory.AssociatedGradedRingStructure`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `WeilConjectures.AlgebraicGeometry.AffineConormalSections`
- `WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated`
- `WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful`
- `WeilConjectures.AlgebraicGeometry.Coherent`
- `WeilConjectures.AlgebraicGeometry.CoherentFormalModule`
- `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`
- `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `WeilConjectures.AlgebraicGeometry.TensorPullback`
- `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`
- `WeilConjectures.RingTheory.SymmetricAlgebraBaseChange`
- `WeilConjectures.Topology.InverseImageModule`
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`
- `WeilConjectures.Topology.StalkDirectSums`

The original direct proof plan no longer needs the domain/function-field stalk
calculation `lem-weil-pbc-spec-domain-stalks-function-field`, the separate affine
conormal theorem `lem-weil-pbc-affine-conormal-sections`, the quasi-coherent symmetric
algebra package `lem-weil-pbc-quasi-coherent-symmetric-algebra`, or the symmetric
presentation/base-change results `lem-weil-pbc-symmetric-algebra-universal-property`
and `lem-weil-pbc-symmetric-algebra-base-change`. The normalized stalk proofs use
actual ideal ranges, exact quotients and the explicit symmetric presheaf instead.
The corresponding obsolete top-level `tool_uses` entries are removed. The algebra
construction still needs the ambient graded operations, closed pushforward descent
and affine tilde/pullback calculations: those are retained in its own proof plan.
No module is withdrawn and no adopted source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or missing hypothesis was found. The old plan's generic
symmetric-base-change and function-field-stalk detours are unnecessary. The ordinary
stalk comparison is valid without a domain assumption, and the symmetric stalk
comparison is valid without quasi-coherence. The Lean proof needs a lifted index type
for the existing same-universe coproduct-stalk theorem; its classical equality
instance must agree with that theorem's normalization formula.

## New nodes

`lem-pur-conormal-graded-algebra-basic`: the six fixed definitions, relocated verbatim;
primary declaration `piece`, with all six declarations attached.

`lem-pur-conormal-graded-algebra-construction`: the source's total-algebra construction
with its coproduct and normalized affine charts; one theorem hole remains.

`lem-pur-conormal-graded-piece-stalk`: proved normalized stalk quotient in every degree,
including zero.

`lem-pur-conormal-piece-stalk`: proved degree-one cotangent identification and
quotient-scalar compatibility.

`lem-pur-conormal-graded-algebra-stalk`: proved total ring stalk chart, assembled from
the coproduct and degreewise charts and proved multiplicative on representative germs.

`lem-pur-symmetric-algebra-sheaf-stalk`: proved scalar- and generator-normalized stalk
comparison for the fixed symmetric algebra sheaf.

Change record: `coord/changes/conormal-graded-algebra-basic-relocation.md`.
The existing parent node now records the actual proof route; the unit's normal-cone
construction and its realization are preserved.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
