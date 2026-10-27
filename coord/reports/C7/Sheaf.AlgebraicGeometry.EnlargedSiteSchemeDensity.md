## What changed

Completed `AlgebraicGeometry.AlgebraicSpace.enlargedSite_scheme_density` in
`Sheaf.AlgebraicGeometry.EnlargedSiteSchemeDensity`, preserving its full signature,
universes, public imports, and all eleven conclusions. Added only proved private
helpers and private instances in that module. No existing dependency module changes.

The proof constructs the terminal object and actual sheaf pullbacks, proves the
covering axioms from chartwise permanence and field-extension lifting, constructs
Yoneda full faithfulness, proves exact agreement of scheme coverings and enlarged
coverings, and constructs scheme pullbacks and singleton atlas coverings. The atlas
refinement retains the original index set. An induction on the generated topology
then proves cocontinuity. Identity coverings give local equality and local lifting,
so all special cocontinuity conditions hold. Finally the same data give Mathlib's
`IsDenseSubsite`, and its restriction equivalence proves the last conclusion for the
exact universe in the statement.

The node's eight proof steps, proof dependencies, and proof origin now follow this
Lean argument. The unit's own statements and steps are unchanged. Both new generic
tools used from another unit are already Mathlib leaves:
`lem-weil-pbc-scheme-pullback-compatible-point` and
`lem-pc-fppf-dense-sheaf-equivalence`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.AlgebraicSpace.enlargedSite_scheme_density`
(node `lem-trf-space-enlarged-site-scheme-density`).

Added 0 holes; split off 0 theorems. No `sorry` remains in the delivered module.
The proof uses the existing declared geometric prerequisites, including the
algebraic-space property of the published scheme-space and fibre-product
constructions; their outstanding proofs are not changed in this delivery.

Validation: the module is checked with `lcompile.py`; delivery also runs the
server preflight and declaration/axiom probes. The public theorem signature is
textually unchanged. Empty covering families and empty schemes are handled without
nonemptiness hypotheses: a target field section would force a covering index, and
all residue-field choices are made only after obtaining an actual scheme point.

## No longer needed

Removed private imports:

- `WeilConjectures.FieldTheory.CommonExtensionFields`: point lifting uses a point
  of the scheme pullback and its residue field instead of a separate amalgamation.
- `Sheaf.CategoryTheory.SpecialCocontinuousSheafEquivalence`: the existing Mathlib
  dense-subsite equivalence directly handles the categories and coefficient universe.
- `Mathlib.CategoryTheory.Yoneda`: its API is already supplied by the preserved
  public imports.

Removed proof dependencies `lem-weil-common-extension-fields` and
`lem-weil-pbc-special-cocontinuous-sheaf-equivalence`, and removed both obsolete
entries from this node's top-level `tool_uses` list. Their modules are no longer
needed as direct proof imports by this item. They may remain transitively imported
by the published enlarged-site definitions or needed by other consumers; this
delivery does not withdraw them or claim whole-library pruning.

No other original proof dependency is pruned. Added the existing proved
`lem-trf-presheaf-field-lift-family-calculus` for the explicit covering calculus.
No module is withdrawn and no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The planned direct use of `specialCocontinuous_sheafEquivalence` has a small-category
signature in one universe, while the actual algebraic-space sites have distinct
object and morphism universes. No statement repair is needed: Mathlib's
universe-polymorphic dense-subsite equivalence applies to the exact restriction
functor after the density, continuity, and cocontinuity clauses are proved.

The common-field-extension step is unnecessary because Mathlib already proves that
compatible scheme points lift to the scheme fibre product. Its residue-field map
supplies precisely the extension and lift needed here.

No change records are needed: no public declaration signature, definition,
attribute, public import, or other module is changed. There are no new nodes.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
