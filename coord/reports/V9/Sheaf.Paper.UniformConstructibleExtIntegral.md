## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.uniformConstructibleExtIntegral`
from the existing supported-lattice reduction tower, finite-coefficient Hom comparison,
and torsion stratum bound. The public theorem signature and public import are unchanged.
Three private helpers prove the adjacent-degree inequalities, shifted-product Hom
vanishing by product extensionality, and vanishing through a Roos triangle by Mathlib's
triangle Hom exactness.

The shorter assembly applies Hom directly to the integral target's Roos triangle. It
retains the unit's reduction, finite-coefficient supported-Hom calculation, torsion bound,
and one-degree inverse-limit loss. No new module, public declaration, definition,
instance, or statement is introduced. Updated the item's node to match this assembly.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.uniformConstructibleExtIntegral`
(`det-uniform-constructible-ext-integral`). Added zero holes. No `sorry` remains in the
item or is added elsewhere. This is a proof from the existing named dependencies;
those dependencies retain their existing unproved statements.

Validation: the final item compiled through `lcompile.py` with exit code 0 in 10.4 s,
with no warnings. The theorem signature is byte-for-byte identical to the shared source.
Both new proof imports passed `tools/import_direction.py may`. The packet has no
new public interface or changed shared definition, so no importer adaptations are needed.

## No longer needed

Removed direct proof imports:

- `Sheaf.Paper.FormalClosedSupport`
- `Sheaf.Paper.FormalClosedSupportII`
- `Sheaf.CategoryTheory.Sites.RGammaDerivedLimit`
- `WeilConjectures.CategoryTheory.Triangulated.MilnorSequence`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`
- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`
- `Sheaf.Paper.IntegralModels`

The existing tower and finite-comparison modules provide all required interfaces.
The item no longer directly needs `lem-pc-derived-limit-milnor-sequence`: Hom exactness
on the integral Roos triangle proves the needed zero case without constructing an
abelian-group Milnor short exact sequence. Removed that proof dependency.

Removed stale top-level tool-use entries `sk-lem-integral-models`,
`sk-lem-formal-closed-support-ii`, `lem-kun-site-rgamma-derived-limit`, and
`lem-pc-derived-limit-milnor-sequence`. The first three are encapsulated by existing
comparison dependencies and are not direct tools of this proof. This does not assert
that their modules can be withdrawn: existing dependencies can still need them.
Neither of the two lattice-comparison dependencies nor the torsion bound is pruned.

## Where the brief, the DAG or earlier work was wrong

The source file's six-step docstring predates the DAG's three-step comparison split.
It was updated to describe the actual proof. The generic Milnor sequence is more than
this particular vanishing argument requires: the tower theorem already supplies the
integral target's Roos triangle, and representable Hom preserves its products.

The rework entry mentions an import failure through `SfP1ChartExchange`; the item
source is present in the current shared repository and is preserved with its original
statement and Lean attachment. The remote compiler resolved that dependency using its
existing private overlay cache. No quarantined file is deleted or withdrawn.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
