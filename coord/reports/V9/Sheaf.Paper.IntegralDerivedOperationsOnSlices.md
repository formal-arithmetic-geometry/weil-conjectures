## What changed

Repaired the return for head `7e062ee8ca`: added all three missing landing-side consumers
to `coord/changes/V9-integral-slice-proof-scopes.md`, under `## Users`:
`Sheaf.Paper.IntegralCompletionUnitCriterion`,
`Sheaf.Paper.IntegralFiniteTensorComparison`, and `Sheaf.Paper.IntegralLineRoosTensor`.
Each row records the declarations it uses and why no adaptation is required. These
modules are absent from the current local read-only snapshot; the rows explicitly
preserve the landing tool's consumer evidence. The retained Lean proofs are unchanged.

Proved `WeilConjectures.IntegralOnSlice.transition_existsUnique` for the global site and every slice. The existing proved coefficient transition is restricted from the constant coefficient sheaf, its compatibility with the completed projection follows from the limit cone, and the balanced tensor formula extends through sheafification. Tensor generation proves uniqueness; naturality gives the chain-map equations.

Proved `WeilConjectures.IntegralOnSlice.completionUnit_existsUnique`. The explicit `(c, 0)` cocone lift is natural. Unary resolving-representative full faithfulness, proved using the existing restriction-localization and full essentially-surjective whiskering lemmas and transported along Mathlib's quotient/localization comparison, extends this transformation uniquely from the good representatives. The displayed normalization follows by cancelling the completion comparison.

Added the proved public equation `WeilConjectures.IntegralOnSlice.reduction_obj` to the existing definition node; all other new helpers are private and proved. The generator and private unit-module constructor use this named equality instead of projecting the full derived-functor witness repeatedly. `generator_original_formula` proves by reflexivity that the public generator still equals its exact original formula. This changes only the equality proof used by its cast. All existing theorem statements, public imports and instance bodies are retained; all other public data-definition bodies are retained. The former inferred types of `reduction`, `transition`, `augmentation`, `completion` and `hom` are now explicit, with identical exported types.

The completion-unit choice spells out its type, predicate and existence proof, retaining the same `Classical.choose` application as the original field notation.

Added four private proof imports, including `import all` for the unrestricted tower and resolving-whiskering modules to reuse their already-proved private helpers. The change record `coord/changes/V9-integral-slice-proof-scopes.md` records the generator proof-term normalization and every transitive consumer; no consumer is adapted. Generic proved categorical and ringed-site whiskering interfaces avoid repeatedly checking these constructions with concrete scheme and slice parameters. They use the existing K-flat resolution theorem. The existing generator-map proof reuses tensor-section naturality; the augmentation proof uses a proved degreewise-unit formula; the Roos-unit naturality proof uses a proved equation for its cocone lift. All added reducibility attributes are local.

## Proved and sorry left

Closed two of the four original holes:

- `WeilConjectures.IntegralOnSlice.transition_existsUnique`.
- `WeilConjectures.IntegralOnSlice.completionUnit_existsUnique`.

The two original holes retained, both attached to `def-pur-integral-derived-operations`,
with their existing signatures and proof docstrings:

- `WeilConjectures.IntegralOnSlice.completion_exists`.
- `WeilConjectures.IntegralOnSlice.completedTensor_global_comparison`.

Added holes: zero. Split-off holes: zero. This is a partial proof delivery, not a decomposition. The completion-unit proof uses the existing normalized completion declaration and therefore still depends on its existing descent hole.

## No longer needed

None. No imports, public declarations, modules, or existing dependency nodes are withdrawn. The remaining descent and tensor comparison arguments still require their recorded dependencies. The scalar-extension helpers are reused from the existing unrestricted tower module rather than duplicated; the remaining private helpers follow the established sheafification and tensor-generation route; no blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The attached definition node had no proof steps or proof dependencies, although this module contains four normalization/descent theorem holes. Its sandbox copy now records the two formalized arguments and explicitly records the two retained holes. No mathematical statement is disputed or changed.

The private restriction-localization and full essentially-surjective whiskering lemmas underlying the two-variable resolving theorem give unary unit descent directly. No new public descent theorem or product-category detour is needed. The existing private scalar-extension helpers can be reused via `import all`; copying their definitions into this module was unnecessary and increased compilation cost.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
