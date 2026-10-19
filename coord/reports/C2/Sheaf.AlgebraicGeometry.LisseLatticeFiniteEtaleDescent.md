## What changed

Withdraw `Sheaf.AlgebraicGeometry.LisseLatticeFiniteEtaleDescent` using dispatched
brief step 8d. Its declaration is unused and its DAG node already realizes finite
etale lattice descent by the proved internal-module theorem
`AlgebraicGeometry.ProEtale.CondensedRing.continuousLisse_finiteEtale_lattice` in
`Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent`. The sole direct importer,
`Sheaf.Paper.LisseEConstructibleIntegralLattice`, already imports that replacement;
remove just its unused private import of the retired module.

Change record: `coord/changes/C2-withdraw-obsolete-finite-etale-lattice.md`.
The existing node, canonical attachment, and unit route remain unchanged. No new nodes.

## Proved and sorry left

Proved: 0 of the assigned module's 1 original sorry. Retired, rather than proved:
`AlgebraicGeometry.ProEtale.exists_lisse_lattice_finite_etale_descent`
(blueprint: `lem-weil-pbc-lisse-lattice-finite-etale-descent`).
Remaining in the withdrawn module: 0. Added: 0. Split off: 0.

The adapted importer retains its pre-existing hole unchanged:
`AlgebraicGeometry.ProEtale.exists_constructible_integral_lattice`
(blueprint: `lem-weil-pbc-lisse-e-constructible-integral-lattice`).
This delivery makes no claim to prove that result or the dependencies of the retained
canonical finite-etale descent theorem.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.LisseLatticeFiniteEtaleDescent`.
Removed its sole import, at line 20 of `Sheaf.Paper.LisseEConstructibleIntegralLattice`.
No other text of that importer changes. There are no consumers of the retired theorem
in either Lean root; `tools/downstream.py --uses` finds only its defining module.

The old module's imports all disappear from that module with the withdrawal:

- `Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`
- `Sheaf.NumberTheory.Padics.CoefficientExtension`
- `WeilConjectures.CategoryTheory.RingObjects.ContinuousMap`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`
- `Mathlib.Topology.NoetherianSpace`
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.CategoryTheory.SiteModuleSheafGluing`
- `Mathlib.LinearAlgebra.FreeModule.PID`

Those dependencies can remain needed elsewhere. No DAG node is removed or detached:
the finite-etale descent node already attaches to its active replacement.

## Where the brief, the DAG or earlier work was wrong

The assigned module is a stale duplicate of a node whose attachment was replaced by
C4 on 2026-10-16. The corresponding change record says the older file was absent;
it is present now, but no surviving proof refers to its declaration. Proving it again
would retain unnecessary work. The active node's intersection proof is already
implemented in `ContinuousFiniteEtaleLatticeDescent`. Its mathematical statement and
proper-base-change unit route are preserved by retiring this unused realization.

The prescribed searches were run with msearch (LeanFinder, Loogle, grep); none gives
a Mathlib proof of this specific lattice descent theorem. The shorter route is the
existing project realization and withdrawal of the unused duplicate.

## Forced adaptations

`Sheaf.Paper.LisseEConstructibleIntegralLattice` is held by H8. Only its unused
private import at original line 20 is removed; its entire remaining source is identical.
This is the consumer cleanup explicitly required by dispatched brief steps 8b/8d:
the deletion gate refuses withdrawal while any module still imports the retired one.
There is no claim that its original Lean proof fails against an empty module; the
necessity is removal of the obsolete dependency, not a changed declaration interface.

## Forced adaptations

### Sheaf.Paper.LisseEConstructibleIntegralLattice
Only imports removed (Sheaf.AlgebraicGeometry.LisseLatticeFiniteEtaleDescent), e.g. to break an import cycle; nothing else changed. CODEX verifies that the removal is needed.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
