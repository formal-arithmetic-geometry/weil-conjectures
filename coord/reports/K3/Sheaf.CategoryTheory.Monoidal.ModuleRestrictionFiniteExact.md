## What changed

Proved `CategoryTheory.Mod.finite_limits_colimits_exact_comap` in
`Sheaf.CategoryTheory.Monoidal.ModuleRestrictionFiniteExact`, preserving its signature,
visibility and imports. The four finite (co)limit existence assertions follow from the
shape-wise instances in `WeilConjectures.CategoryTheory.Monoidal.Mod.Limits`.
For each finite shape, restriction followed by forgetting is definitionally the source
forgetful functor. That functor preserves the (co)limits, while the target forgetful
functor reflects them because it creates them. Mathlib's
`preservesLimitsOfShape_of_reflects_of_preserves` and its colimit counterpart therefore
give both components of `exactFunctor_iff`.

This is the existing DAG argument expressed through the creation/reflection API. It also
uses the proof pattern of the stronger abelian-only instances in
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`, without importing
that module or adding its abelian or monoidal-preadditive assumptions. The unit route is
unchanged. A single-file server compile passed without warnings in 2.0 seconds.

## Proved and sorry left

Closed the one existing hole:
`CategoryTheory.Mod.finite_limits_colimits_exact_comap`
(node `lem-sfb-modobj-restriction-finite-exact`).

Proved 1 of 1 original sorries. Zero sorries remain; zero holes added; zero split off.
No definitions or statements changed.

## No longer needed

None. No imports removed, and no DAG dependency, node or module pruned.
The proof uses all four existing proof dependencies: finite (co)limit existence,
forgetful creation, scalar restriction, and the definition of exactness.
No additional proof import is required.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement defect found. The DAG's explicit action-uniqueness and
comparison-isomorphism arguments are already packaged by the creation instances and
Mathlib's reflection lemmas, so they require no additional local construction.

Delivery infrastructure: the ordinary `lcompile.py` check passed. The first required
`deliver3.py` attempt failed while compiling its `ModuleRestrictionFiniteExact__probe.lean`:
`unknown module prefix 'Mathlib'`. The displayed search path contained the project's
compiled-library directory and Lean's core directory, but no Mathlib package directory.
Nothing was pushed. Three subsequent delivery attempts received no compile-server answer;
those transient responses do not establish that the probe's search-path defect was repaired.
The packet is preserved, complete, with no launcher script or shared-repository changes.

On resumption, the sandbox was checked against the current source: only the theorem's
proof differs, and the signature, imports, docstrings and four DAG proof dependencies
are unchanged. The two required delivery retries again received no compile-server answer
within 196 seconds and pushed nothing. These busy-server responses are being retried;
they do not establish a Lean error or a repair of the earlier axiom-probe search path.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
