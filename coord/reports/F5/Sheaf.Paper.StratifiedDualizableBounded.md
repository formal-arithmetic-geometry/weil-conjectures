## What changed

Proved `AlgebraicGeometry.ProEtale.stratified_dualizable_bounded` in
`Sheaf.Paper.StratifiedDualizableBounded`, keeping its signature and all public imports.
Four private proved helpers transport w-contractibility through a ring equivalence,
show that triangulated realization of perfect complexes is bounded when the ring has
bounded image, bound dualizable objects on w-contractible affines, and descend that
boundedness along a singleton cover.

The shorter route uses constructible strata directly: they are quasi-compact, their
immersions are quasi-compact into the quasi-separated root, and the existing finite
quasi-compact abelian-sheaf detection theorem detects homology vanishing on them.
Perfect-ring classical generation replaces the explicit projective-term and tail induction.
The canonical t-structure supplies the final lower-bounded cochain representative.
The existing node's proof and dependency list follow this implementation.

Validation: the final item module compiled cleanly through `lcompile.py` in 5.1 seconds,
with no errors or warnings. Its theorem signature is byte-identical to the original,
all Lean lines are at most 100 characters, all imports are cycle-free, and the revised
DAG dependency closure has no cycle.

Proof imports added: `WeilConjectures.Mathlib.RingTheory.Henselian`,
`Sheaf.CategoryTheory.DerivedCategory.PerfectRingClassicalGenerator`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed`,
`WeilConjectures.Topology.ConstructibleIsRetrocompact`,
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
The perfect-ring generator and constructible-retrocompactness nodes are generic proved
tools; the unit `sk-def-perfect` has no proof step assigned to this auxiliary node, and
its target statement and route are preserved. No source-library file is changed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.stratified_dualizable_bounded`
(node `lem-pod-stratified-dualizable-bounded`). There are zero remaining holes in the
item module and zero holes added anywhere. No theorem was split off. The proof uses
existing stated dependencies, including the permitted unfinished pullback-dualizability
and evaluation theory, rather than re-proving their statements here.

The new node attaches the already proved source declaration
`AlgebraicGeometry.ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp`;
it adds no Lean file or hole. All private helpers have complete proofs.

## No longer needed

Removed these proof-only imports:

- `Sheaf.SixFunctors.ConstructibleOpenClosedRefinement`
- `Mathlib.RingTheory.Finiteness.Defs`
- `Mathlib.Algebra.Module.Projective`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection`
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`

The following original direct proof dependencies are unused and removed from this node:
`lem-fix-constructible-open-closed-refinement`, `def-weil-finitely-generated-module`,
`def-weil-pbc-projective-module`, `def-weil-abstract-derived-category`,
`lem-weil-pbc-complex-ses-triangle`, `lem-sf-derived-homology-long-exact`,
`lem-trf-geometric-inverse-image-exact`, and `lem-exc-open-closed-detection`.
Definitions and generic results used by the imported generator/evaluation theorems remain
their dependencies; this does not request deletion of those declarations or modules.
The refinement tree is replaced by finite quasi-compact joint detection. Explicit
finite-projective splitting and tail triangles are replaced by the already proved
classical-generator theorem. The exact pullback API is already present, so there is
no additional geometric-exactness theorem to invoke. Mathlib's existing lower-bounded
representative theorem replaces the large truncations module.

Pruned obsolete top-level tool approvals for
`lem-fix-constructible-open-closed-refinement`,
`lem-trf-geometric-inverse-image-exact`, and `lem-exc-open-closed-detection`, preserving
the relative order of retained approvals. No Lean module is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

The original seven-step plan is mathematically usable but longer than necessary given
the current library. In particular, it does not need a refinement tree to detect zero
homology: the source library already proves finite quasi-compact joint detection for
arbitrary scheme morphisms. That declaration had no precise node attachment; the new
node records it rather than citing the more specialized open/closed theorem outside
its statement. The generator argument assumes only triangulated, strong monoidal
realization; it makes no false t-exactness assertion. Bounds are chosen as sums of
absolute values so that they are ordered even for no strata. Empty schemes, empty
strata, the zero ring, and zero complexes require no nonemptiness hypothesis.

## New nodes

`lem-pod-finite-qc-proetale-abelian-detection` records the existing proved theorem
`AlgebraicGeometry.ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp`
in `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.DetectionAb`
(lines 151–171). It is a generic tool for detecting the identity of each homology
sheaf along the given finite quasi-compact jointly surjective immersion family.
The exact source signature is recorded with `existing: true`; no duplicate public
statement or new Lean module is introduced. Searches by LeanSearch, Loogle,
LeanFinder, Mathlib grep, DAG grep and blueprint search found no exact Mathlib or
existing blueprint node. No change record is needed: no existing public interface
or mathematical statement changed.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
