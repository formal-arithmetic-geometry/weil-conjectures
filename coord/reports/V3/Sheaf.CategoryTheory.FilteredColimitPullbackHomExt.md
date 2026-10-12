## What changed

Proved `CategoryTheory.filteredColimit_pullback_hom_ext` in
`Sheaf.CategoryTheory.FilteredColimitPullbackHomExt`, without changing its signature,
visibility, or existing docstring. Added proof-only imports
`Mathlib.CategoryTheory.Limits.Types.Filtered` and `Mathlib.Tactic.FinCases`.

Three proved private helpers implement finite simultaneous eventual equality,
composition of equal arrows with identified endpoints, and common-stage lifting
of two arrows into the image of a specified stage object. The main proof lifts the
arrows, enforces the two projection equations at a later stage, applies joint
monicity of the preserved stage pullback, and maps the equality back to the cocone.
The route is exactly the existing node's plan and uses its existing Mathlib leaf
`lem-weil-pbc-filtered-colimit-sets-elementwise`; no node update is needed.

## Proved and sorry left

Closed the single original hole:
`CategoryTheory.filteredColimit_pullback_hom_ext`
(node `lem-weil-pbc-filtered-colimit-pullback-hom-ext`).

Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module,
and no new modules or assumed intermediate theorems were added.
The module compiles without warnings using `lcompile.py`.

## No longer needed

None. No original imports or proof dependencies were removed. The normalized-category
finite-lifting and list-equality modules were inspected but are not needed or imported;
they were never dependencies of this item's planned proof. The unit's route is retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The existing plan suffices for arbitrary cocones whose
object and arrow cocones are colimits, without normalizing the cocone category or
assuming existence of arbitrary pullback factorizations. The endpoint transports are
handled explicitly with `eqToHom` and equality of objects of the arrow category.

## Second reading by V3

1. **Visible declarations and statements — PASS.** Compared the delivered module with
   the repository version. The existing theorem signature, visibility, and docstring
   are unchanged; only proof-only imports, private helpers, and the proof body differ.
2. **Compilation and axioms — PASS.** `lcompile.py` compiles the module without errors
   or warnings. There are no `sorry`s, forbidden declarations, or hollow definitions;
   the proof uses only ordinary Lean and the imported colimit and pullback results.
3. **New or split statements — PASS.** No public statements or nodes were added. The
   three helpers are private proof infrastructure, and the existing node remains the
   sole theorem proved. No duplicate Mathlib or library theorem was introduced.
4. **Shortest route and pruning — PASS.** The proof follows the node's planned route:
   finite eventual equality, arrow lifting, preservation of the pullback, and joint
   monicity. All existing public imports remain needed by the theorem or its context;
   the two added imports are proof-only. The unit route and its realized node are kept.
5. **DAG agreement — PASS.** The theorem's proof uses the existing elementwise filtered
   colimit dependency recorded by the node, and no dependency, statement, or route
   field requires an update.

Changed only the proof implementation and added the two proof-only imports; no
statements, definitions, nodes, or dependency records needed repair.
