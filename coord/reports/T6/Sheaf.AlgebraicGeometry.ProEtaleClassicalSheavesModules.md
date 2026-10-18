## What changed

Proved `AlgebraicGeometry.ProEtale.proEtaleClassicalSheavesModules` with its exact original
signature, for every `X : Scheme.{u}` and every `Λ : Type (u + 1)` with `CommRing Λ`.
Only the assigned Lean module and its node are changed. No definitions or statements used
by consumers are changed. Removed public imports are documented in
`coord/changes/T6-classical-modules-import-pruning.md`, with all four downstream consumers. The node proof now follows the shorter proof actually written.

The existing generic comparison API already supplies the adjunction, finite-limit and
finite-colimit preservation, and full faithfulness. Three private helpers prove that
module forgetting preserves the required Kan extensions, construct its canonical
inverse-image comparison, and derive compatibility with the actual counits from the
unit equation and the two right triangle identities. The set essential-image theorem
then gives the module counit characterization; the fully faithful adjunction criterion
gives the module essential image.

Added proof imports: `WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful`,
`Sheaf.CategoryTheory.SheafPullbackForgetComparison`, and
`Mathlib.Algebra.Category.ModuleCat.FilteredColimits`.

Validation: the completed and pruned module compiled through `lcompile.py` in 6.1 seconds,
without warnings. The import-pruning consumer check passed. The argument is uniform for
the empty scheme and the zero ring; it uses no element choices or nonzero assumptions.
No new public declaration or intermediate obligation is introduced. Kan-preservation
evidence is a private theorem, installed only locally, so it adds no global instance. The unit-level route
remains the classical comparison route: use the actual adjunction and its counit, with
classicality supplied by `det-pe-classical-sheaves-image`.

Two existing proved tools are reused outside this node's unit:
`lem-weil-pbc-sheaf-pullback-forget-comparison` gives the canonical comparison including its
unit equation, and `lem-weil-pbc-comparison-grothendieck-unit` records the source-library
theorem already giving the module full-faithfulness instances. They replace explicit
reconstruction of algebraic operations and do not bypass a unit statement.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.ProEtale.proEtaleClassicalSheavesModules`
(node `det-pe-classical-sheaves-modules`).

Added 0 holes; split off 0 obligations. No `sorry` remains in the delivered module or its
private helpers. This is a proof from existing declarations, not a decomposition.
The imported `AlgebraicGeometry.Scheme.proEtaleClassicalSheavesImage` remains its existing
upstream obligation (node `det-pe-classical-sheaves-image`), unchanged by this delivery.

## No longer needed

Removed direct proof imports and proof-dependency edges:

- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesUnit`, node
  `det-pe-classical-sheaves-unit`: generic module full faithfulness already exists.
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`, node
  `lem-weil-pbc-site-pullback-abelian-exact`: module exactness is already an instance.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`, node
  `lem-weil-pbc-module-sheaves-colimits-forgetful`: no conversion through varying-ring
  module sheaves or abelian kernels and cokernels is necessary.
- The direct proof edge to `def-weil-sheaf-of-modules-category` is unnecessary; its statement
  dependency stays, and the proof uses the existing fixed-coefficient ModuleCat encoding.

Removed unused public imports:

- `WeilConjectures.SixFunctors.ProEtale.Comparison`: replaced by the narrower proof import
  `WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful`, avoiding its derived
  base-change and acyclicity imports.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`.
- `Sheaf.CategoryTheory.RingedSiteModules`.

The latter statement infrastructure already arrives where needed through retained statement
imports, and this theorem does not use those declarations directly. This does not claim
that the corresponding nodes are globally unreachable. In particular the set image theorem
still needs its own unit/continuity dependencies. No module is withdrawn.

Removed both obsolete `tool_uses` approvals from this node:
`lem-weil-pbc-site-pullback-abelian-exact` and
`lem-weil-pbc-module-sheaves-colimits-forgetful`.

## Where the brief, the DAG or earlier work was wrong

The planned explicit module-adjunction, exactness and full-faithfulness reconstruction was
unnecessary: the source library proves those facts for arbitrary Grothendieck abelian
coefficients, including modules over every commutative ring. Its finite-coefficient
specialization is not the interface limitation of `comparisonAdjunction` itself.

The existing canonical forgetful comparison and unit equation also supply precisely the
compatibility needed for the classicality transfer. Counit compatibility is proved here
by Hom-equivalence injectivity and triangle identities, rather than asserted as new theory.
No mathematical statement was disputed or changed. There are no new nodes, consumer adaptations, or new proof obligations. The import
change record is `coord/changes/T6-classical-modules-import-pruning.md`.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
