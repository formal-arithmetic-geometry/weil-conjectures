## What changed

Proved `Rep.continuousCochains_shortExact` with its signature unchanged. Constructed the actual
continuous-map terms, the A-linear inhomogeneous differential, and postcomposition cochain maps.
Open stabilizers give continuity of the action. The proved
`Rep.exists_homogeneousCochains_inhomogeneous_coordinates` identifies the differential with the
homogeneous differential after forgetting to integer coefficients and applying ULift to match
universes; transporting its square-zero identity supplies the complex equation.

The declared `discreteModules_abelian` dependency supplies the exact forgetful functor to modules.
Pointwise injectivity, a unique lift on the kernel, and a set-theoretic section of the surjection
prove degreewise exactness. These choices occur only inside proofs; the complexes and maps are
explicit constructions. Mathlib's degreewise criterion then proves short exactness of complexes.
Updated the item's proof fields to this argument and added the proof-only import
`Sheaf.RepresentationTheory.HomogeneousInhomogeneousContinuousCohomology`.
Its node belongs to `sk-thm-br`; it is used as a generic coordinate tool only. No unit statement
or unit proof step is bypassed, and no maintainer-owned `tool_uses` approval was edited.

Source read: `literature/stacks-project/etale-cohomology.tex`, section-continuous-group-cohomology,
Tag 0DVG, displayed differential and the paragraph beginning “However, a short exact sequence”.
Checked the dependency signatures and the Mathlib criteria. LeanFinder, Loogle, and Mathlib grep
searches found the abstract inhomogeneous differential, which is restricted to a commutative ring
and a common universe. Reusing the library's proved homogeneous coordinate theorem avoids those
restrictions while retaining the original arbitrary-ring statement.

## Proved and sorry left

Closed 1 existing hole: `Rep.continuousCochains_shortExact`
(node `lem-exc-continuous-cochains-short-exact`). Added 0 holes and split off 0 statements.
There are no remaining sorries in the delivered module. The proof uses the existing stated
`CategoryTheory.discreteModules_abelian`; that declaration is outside this delivery and remains
an existing dependency. No definition or public signature was changed.

Remote compilation checks the full theorem, all private helpers, and the universes. The
construction covers degree zero uniformly, trivial groups, zero coefficient objects, and zero
rings; no extra nontriviality or finiteness assumptions enter the proof. The imported coordinate
theorem is used only on the discrete lifted underlying integer representation, whose open
stabilizers are exactly the original ones.

## No longer needed

No original imports, declared dependencies, nodes, or modules are pruned. Both original proof
dependencies are used. The new proof-only coordinate import is needed for square-zero.
The direct expansion-and-cancellation calculation in the old plan is replaced by transport of
the homogeneous square-zero identity. Extending to integer degrees and restricting back is
unnecessary: Mathlib's degreewise exactness criterion applies directly to `ComplexShape.up ℕ`.
Redundant trial imports of `Mathlib.Topology.Algebra.MulAction` and
`Mathlib.Algebra.Module.ULift` were removed; the retained imports already provide their
declarations. The proof-only `Mathlib.Algebra.Homology.ShortComplex.ModuleCat` import is
needed for the module exactness criteria.

## Where the brief, the DAG or earlier work was wrong

The original proof classified the full differential square-zero calculation as elementary.
The existing proved homogeneous coordinate theorem supplies a shorter checked route. The DAG
now records that dependency. Its older extension-to-integer-degrees detour is unnecessary.
The theorem statement and the unit route are unchanged. No source error was found.

Change record: `coord/changes/continuousCochains_shortExact.md`.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
