## What changed

Filled `AlgebraicGeometry.ProEtale.CompletionTriangle.completion_triangle_comparison`
in `Sheaf.Paper.CompletionTriangleComparison`. The public theorem statement, tower
construction and completion abbreviation are unchanged. All additional helpers are
private and proved in this module.

The proof assembles the given principal-calculus tower and its augmentation, applies
the Roos calculus, and descends through the derived localization. It assembles coherent
shifts and cone comparisons by evaluation, proves augmentation compatibility with
shifts, and transfers distinguished cone triangles through localization. Naturality
and the shift equation give all three squares of the augmentation triangle morphism.

For the canonical completion comparison it works in the actual internal-module
category. The coefficient short exact sequence and tensor flatness give the augmented
cone-to-tensor quasi-isomorphism for flat complexes. A flat K-flat resolution,
tensor invariance on K-flat complexes and cone two-out-of-three extend it to every
K-flat representative, as the theorem requires. The maps commute strictly with tower
transitions and units. An explicit chain isomorphism `(v,u) ↦ (v,−u)` identifies the
resulting tensor Roos complex with the specified completion complex and fixes its
augmentation. Thus the comparison identifies the specified map, not merely its target.

Recorded the existing `lem-sfb-abstract-kflat-resolution`,
`lem-sfb-sheaf-functorial-flat-resolution` and `lem-sfb-modobj-flat-resolutions`
as the adopted flat-resolution inputs. Updated the node's proof, proof dependencies and proof origin to this route, and
removed obsolete top-level tool approvals. No existing public interface changed.
The required command-context record is
`coord/changes/F7-completion-triangle-proof-context.md`; it lists the item and all
77 downstream modules, with their holders and the unchanged consumer semantics.

## Proved and sorry left

Closed the one existing hole in
`AlgebraicGeometry.ProEtale.CompletionTriangle.completion_triangle_comparison`
(node `lem-pe-completion-triangle-comparison`). No holes added, no split-off statements,
and zero `sorry` occurrences remain in the delivered Lean module. The proof uses the
existing principal-reduction and Roos calculus declarations as intended by stage 3.

Validation: the complete proof compiled through `lcompile.py` with the standard
limits in 58.9 seconds, exit code 0, with no warnings. The subsequent visibility-only
correction described below also passed the delivery compile check.

## No longer needed

Removed these proof imports and their corresponding proof dependencies:

- `Sheaf.CategoryTheory.InternalSectionTensorComparison`
  (`lem-pe-internal-section-tensor-comparison`): no change to section-module encoding.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
  (`lem-pc-kflat-resolution`): the adopted proved internal-category flat K-flat
  resolution supplies the needed replacement directly.
- `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`
  (`sk-def-sfb-derived-extension-of-scalars`): use the actual tensorRight levels and
  levelUnit maps already defining completion.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
  (`def-pc-flat-sheaf-modules`): use the internal monoidal category's flat-object API.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
  (`lem-weil-proetale-countable-products-exact`): obtain internal-module
  CountableAB4Star from adopted proved pro-etale repleteness and Mod's epi-limit API.
- `Sheaf.CategoryTheory.StrictRoosComparison`
  (`lem-weil-strict-roos-comparison`): a direct normalized augmented chain isomorphism
  compares the two actual Roos complexes.

Also removed the redundant explicit import of
`Mathlib.Algebra.Homology.HomotopyCategory.ShortExact`; its cone-to-quotient API remains
available transitively and is used. Thus `lem-pc-cone-short-exact-quasi-iso` stays a
proof dependency. The localization universal-property node is also still used through
its Mathlib match. Removed top-level tool approvals for `lem-pc-kflat-resolution`,
`lem-weil-strict-roos-comparison` and `lem-weil-proetale-countable-products-exact`.

These are direct dependencies unnecessary for this proof. A transitive import-graph
check found no project module removed from this item's full import closure: adopted
source-library imports continue to reach those modules. Thus the delivery claims no
global module pruning. No source-library declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement was found, and the unit's principal-cone/Roos route is retained.
The DAG's comparison route used a section-module equivalence and a general strict
Roos comparison unnecessarily: the live completion definition uses internal modules
and gives its complex explicitly. Its sign normalization can be proved directly.
The theorem quantifies over every K-flat representative, not only termwise flat
ones; the proof therefore transfers the flat cone-to-quotient calculation along a
flat K-flat resolution instead of assuming all K-flat terms are flat.

The initial preflight caught the ScalarCone namespace-local colimit instance
inheriting public visibility from the file section. It is now explicitly
`private local instance`; all added declaration names are private.

The module-command checker also requires a change record for the additional
namespace variables, opens and elaboration options. The record named above
documents their proof scope and every downstream consumer; no public signature,
public definition or target statement changes, and no consumer adaptation is needed.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
