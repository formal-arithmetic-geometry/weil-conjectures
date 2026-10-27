## What changed

Proved `AlgebraicGeometry.Etale.support_compactImages_adjoint_sums` with its original
signature, universes, public imports and docstring unchanged. Added one proved private
helper comparing the two existing bounded-constructibility predicates. No definitions,
instances, source-library declarations, or consumer modules are changed.

The proof applies the existing truncation devissage to finite-type sheaf finiteness and
transports from its chosen compactification to the specified compactification. Projection,
tensor symmetry, and the assumed interval bound give the Tor interval. For an empty input
interval the tensor object is zero, so the argument does not assume `a ≤ b` silently.
Finite-ring compact generators supply compactness and detection; compactness of shifts
and the given shift comparison of F supply all shifted tests. The abstract compact-test
theorem proves preservation of coproducts by the fixed G. Its triangulated structure and
counit equation use the shift structure induced by the fixed adjunction.

For constants, the existing exact-left-adjoint derived adjunction applied to
`constantSheafΓAdj` proves coproduct preservation in arbitrary indexing universes.
For tensor, the existing derived tensor-Hom adjunction and symmetry do the same.
Composition instances finish the two coefficient functors. Updated the existing DAG
proof and proof dependencies to describe this route; no unit statement or step is bypassed.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Etale.support_compactImages_adjoint_sums`
(blueprint `lem-pur-etale-support-compact-adjoint-sums`).
The complete proof compiled in 12.3 seconds. Its original existential binder `hG`
is used only implicitly, so a theorem-local unused-variable linter option preserves the
statement verbatim without that style warning. The final source compiled cleanly in 22.0
seconds through `lcompile.py`, with zero errors and zero warnings.

Zero holes remain in the item; zero holes added and zero split off.
The private `boundedConstructible_iff` helper is proved.

## No longer needed

Removed the following direct proof imports:

- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`: the existing source-library
  `boundedConstructible_obj_of_forall_singleFunctor` implements the required truncation
  induction, so no homotopy-colimit construction is used.
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`: its Serre results are already used
  inside that devissage theorem; no direct invocation is needed here.
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`: already publicly exposed by the
  unchanged statement import `ShriekTensorComposition`.
- `WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`: the ordinary
  sheaf category's existing Grothendieck instances suffice; no ringed-module comparison
  from this module is used.
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`: the constant derived
  adjunction gives colimit preservation without termwise localization comparisons.
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorDirectSums`: tensor-Hom adjunction gives the
  requested arbitrary-universe preservation directly; its specialized statement only
  quantifies over `Type (u + 1)`.
- `Mathlib.CategoryTheory.Sites.Sheafification`,
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, and
  `Mathlib.Algebra.Category.ModuleCat.AB`: already supplied by the retained imports.

The route no longer uses `lem-kun-grothendieck-derived-coproducts`,
`lem-weil-pbc-ring-modules-grothendieck-abelian`,
`lem-weil-pbc-module-sheaves-grothendieck-abelian`, or
`lem-kun-derived-tensor-direct-sums` as separate dependencies. Their obsolete top-level
`tool_uses` entries are removed. This is local pruning of this proof's dependency edges,
not withdrawal of declarations or a claim that no other target branch uses these modules.

## Where the brief, the DAG or earlier work was wrong

The original plan proposed recomputing shifted constructibility and Tor amplitude;
compactness of shifts and F's specified shift comparison suffice. It also did not spell
out empty Tor intervals, which the existing definition permits; the proof treats them.

The tensor direct-sum dependency has a fixed indexing universe, whereas this theorem
quantifies over arbitrary `Type v`; the derived adjunction proves the required generality.
The termwise-derived-sum detour is unnecessary for the constant functor, which has an
existing derived right adjoint.

The rework row records an old quarantined source, but the current module exists again in
`lean/` and the current P5 return is empty. This delivery starts from that current source,
restores no absent archive, deletes nothing, and preserves the item's Lean attachment.

Searches run: LeanFinder for exact derived functors, constant sheaves, and compact-support
Tor amplitude (only unrelated condensed-category hits); Loogle for
`CategoryTheory.Functor.mapDerivedCategory` (exact-functor and triangulated instances);
launcher grep for `boundedConstructible_rightDerivedLowerShriek` (no hits); local `rg`
located the source truncation devissage, exact-left-derived adjunction and tensor-Hom
adjunction actually used. No new node or unsourced unfinished statement is introduced.

A dependency reachability check found an existing DAG return path from the already listed
`sbc-thm-finiteness-finite-type` through the finiteness/coefficient-convention nodes and
`def-weil-exceptional-inverse-image` back to this item. This edge predates the delivery;
none of the newly added proof dependencies creates another return path. The actual Lean
imports are acyclic, as confirmed by compilation and `tools/import_direction.py may` for
the new truncation-devissage import. The inherited DAG cycle needs maintainer reconciliation;
this delivery does not remove the necessary finiteness dependency to hide it.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
