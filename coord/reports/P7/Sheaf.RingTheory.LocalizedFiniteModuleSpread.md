## What changed

Proved `Module.exists_finite_localizationAway_model` in
`lean/Sheaf/RingTheory/LocalizedFiniteModuleSpread.lean` without changing its signature,
public imports, or definitions. Added two private proof imports:
`Mathlib.Algebra.Module.LocalizedModule.Submodule` and
`Mathlib.RingTheory.Finiteness.Small`.

Choose a finite generating set s of L over R[1/f], and take its R-span N inside L.
This is the image of R^n in L, hence the quotient R^n/K of Stacks Tag 05N5(1).
Mathlib's `Submodule.localized'_span` identifies its localization inside L with the
R[1/f]-span of s, which is all of L. `Submodule.isLocalizedModule` and
`IsLocalizedModule.mapEquiv` supply the localization equivalence. The proved smallness
of N allows `Shrink N` to serve as the required model in the universe of R.
The DAG proof and proof origin now record this image realization of the source argument.
No new node or interface change is involved.

Searches: LeanFinder for finite-module descent along localization returned forward
finiteness results only; Loogle on `IsLocalizedModule, Submodule.span` found the
localization-of-span API. The launcher grep search and direct rg searches in Mathlib,
Sheaf, and WeilConjectures found no duplicate descent theorem. All three stated
proof dependencies are Mathlib definition leaves and remain used.

## Proved and sorry left

Closed 1 hole: `Module.exists_finite_localizationAway_model`
(node `lem-trf-localized-finite-module-spread`). Added 0 holes; split off 0 statements.
No sorry remains in the delivered module, and no new modules are introduced.

The single-file server compile passes. The axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

None: no imports, nodes, or modules are pruned. The explicit quotient and fraction
calculations in the original plan are implemented by taking the quotient's image
and invoking Mathlib's proved localization APIs. All three original definition
leaves remain dependencies. Both new private imports are used.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original quotient proof is correct; its image
realization is shorter in Mathlib. The universe requirement is handled by the
proved finite-module smallness theorem and a transported equivalence, with no
additional hypothesis on L. The zero ring, f=0 or nilpotent, f a unit, L=0, and
an empty generating set require no case exclusions. The unit route is unchanged.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
