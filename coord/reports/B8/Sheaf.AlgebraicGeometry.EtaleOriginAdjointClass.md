## What changed

Replaced the proof hole in `AlgebraicGeometry.ProEtale.exists_comparisonClassAdjunction` by
reuse of `AlgebraicGeometry.ProEtale.exists_fixedComparisonClassAdjunction`, already proved in
`Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction`. Retain its cohomological-dimension
bound and its chosen ordinary étale right adjoint and adjunction. Transfer each field of
`FixedComparisonClassAdjunction` to `ComparisonClassAdjunction`: bounded-below preservation, the
Hom equivalences and their normalization and naturality, and the compactification comparisons
with normalization, identity, cocycle and Hom compatibility.

Both structures have identical field types, including the literal compactification and chosen
adjunction. The coefficient-ring finiteness instance is the same one explicitly specified in the
theorem's conclusion. No existing signature, public import, definition or visibility changes.
The source argument for blueprint `thm-sf-ambient-adjoint-class` remains implemented in the
reused theorem, including the unit's comparison Hom chain.

Validation: `lcompile.py` compiled the item without warnings in 12.7 seconds. A sandbox
profiling compile succeeded in 24.6 seconds, with a 0.17-second kernel check for the theorem;
`#print axioms` reported exactly `propext`, `Classical.choice`, and `Quot.sound`. A direct
compile with the exact delivery probe appended succeeded in 7.4 seconds and checked all
23 declarations (`SHEAF-PROBED 23`); its only warning was the probe's own long line. An
instrumented version of that probe also succeeded in 21.4 seconds with no exceptional axioms.
Earlier required dry runs timed out in their remote compile. On resumption, the required
dry run passed its compilation, axiom probe and server preflight: `OK (dry run)`,
commit `9b9986684c`, review class `AUTO`. Earlier
infrastructure diagnostics are retained in the sandbox scratchpad.

A fresh source comparison verifies that the existing module docstring, structure, theorem
docstring and theorem signature are unchanged, and that all ten structure fields are identical
to those of `FixedComparisonClassAdjunction`. The reused theorem has a complete proof in the
current source. The sandbox has no lines longer than 100 characters and no textual `sorry`. No
launcher script, shared source, public signature or definition changed.

## Proved and sorry left

The sole original hole is `AlgebraicGeometry.ProEtale.exists_comparisonClassAdjunction`
(blueprint `thm-sf-ambient-adjoint-class`). Its replacement proof compiles. Holes closed: 1, by
that declaration. Holes added: 0. Holes left in the item: 0. No statements are split off.

## No longer needed

Removed these proof-only imports because the proof uses the already-proved fixed comparison
class theorem instead of repeating its construction:

- `WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`
- `Sheaf.AlgebraicGeometry.DerivedCategories`

No DAG dependency is mathematically bypassed: the reused theorem supplies the complete argument
for the same blueprint node. No module withdrawal or globally unreachable module is claimed. All
existing public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The node's current primary Lean attachment is module
`Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`, declaration
`AlgebraicGeometry.ProEtale.specifiedExceptionalHomEquiv`, so searching only the `lean.module`
field does not find this older retained existence theorem. Its docstring still correctly
identifies `thm-sf-ambient-adjoint-class`. The node's implemented proof already describes the
fixed comparison class existence theorem used here. No node edit is needed.

The earlier missing published object and server-response failures were intermittent; the latest
direct compile succeeded. The preserved proof also required a structure-literal indentation
repair. No launcher script or shared repository file was changed.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
