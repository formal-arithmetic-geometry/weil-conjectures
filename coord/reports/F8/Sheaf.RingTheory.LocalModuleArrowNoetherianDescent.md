## What changed

Filled `RingHom.exists_local_module_arrow_noetherian_descent` from its stated dependencies.
The proof obtains the local tower, applies supplied-tower Noetherian collapse, and descends
both modules and the arrow using finite-presentation descent. It passes from the supplied
preorder to its antisymmetrization to use the partial-order descent API, then restricts to
the final upper tail. The fixed-arrow theorem supplies the module diagrams and comparisons.

Private proved helpers transport descent from the canonical ring colimit to the supplied
cocone, combine object and morphism descent, and lift colimits of underlying types to
additive-group colimits. Mathlib's
`Types.FilteredColimit.isColimitOf` constructs the type colimits from the already supplied
representatives and eventual equality. Mathlib's `Algebra.FiniteType.small`,
`small_of_surjective` and `Module.Finite.small` supply `Shrink` models in the original
independent universe `v`. All transition maps, cocones, arrow maps, finite presentations
and comparisons are transported along these linear equivalences. Public signatures and
public imports are unchanged. The local command changes are
recorded in `coord/changes/local-module-arrow-proof-commands.md`, including every
downstream module and its current holder. The warning about the two named
module-structure binders used implicitly is suppressed only for this theorem, retaining
their original names and statement verbatim.

## Proved and sorry left

Closed the one original hole:
`RingHom.exists_local_module_arrow_noetherian_descent`
(node `lem-trf-local-module-arrow-noetherian-descent`).
Added zero holes. No `sorry` remains in the delivered module. No new split-off statements.
The theorem uses the existing declared dependencies; their transitive proof status is
independent of this assembly.

## No longer needed

No declared proof dependency is pruned: all five nodes in the current plan are used.
The original direct proof import `WeilConjectures.RingTheory.TensorLocalizationTowerTransition`
is redundant after using `Sheaf.RingTheory.LocalTowerCollapseNoetherian` for tower collapse.
Its node remains needed transitively by that dependency, as do the Noetherian permanence
and essential finite type composition nodes. No module is withdrawn. Removed the unused
proof import
`Mathlib.Data.Finsupp.Encodable` from the returned packet: no polynomial/countability
argument remains. The two duplicate private helper declarations are removed; their
source-library declarations remain untouched.

## Where the brief, the DAG or earlier work was wrong

The descent theorem requires a partial order, whereas the tower produces a preorder.
Antisymmetrization and its final representative functor bridge this without changing any
statement. The independent module universe requires an actual small-copy construction;
merely enlarging universes would not prove the given signature. Smallness of the finite
type subalgebra, its localization and finite modules supplies it directly.

The plan's second step describes using a tower model for M. Both M and N can instead be
descended by the object clause of the same declared affine descent theorem, which avoids
an unnecessary additional comparison of the tower module. The updated node records this.

The returned head duplicated two private source-library helpers. Both have been removed:
`RingHom.countable_of_essFiniteType` and `RingHom.additive_diagram_isColimit`.
The cited source declarations are all private, so importing them cannot expose them and
the source-library boundary forbids changing their signatures or visibility. The repair
uses Mathlib's public APIs instead. Smallness replaces countability entirely. The new
proved private `RingHom.additive_isColimit_of_types` has genuinely different hypotheses:
an arbitrary filtered category and an existing colimit of underlying types. It proves
only that the universal descending functions preserve addition, using common-stage
representatives; Mathlib's `IsColimit.ofFaithful` provides the universal property.
The original representative/eventual-zero colimit theorem is no longer restated.
The argument also covers the zero group and singleton index categories, and requires
no relation between the index universe and module universe. No adopted source module
is edited.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
