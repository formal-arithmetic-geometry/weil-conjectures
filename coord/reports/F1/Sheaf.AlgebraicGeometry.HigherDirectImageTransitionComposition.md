## What changed
Proved `AlgebraicGeometry.Etale.higher_direct_image_transition_composition` without changing its statement. The proof expands the coefficient maps by functoriality, applies canonical-coefficient composition, and uses coefficient naturality to move f across the second transition. Added two independent modules for these strictly smaller statements. Updated the parent DAG proof and dependencies to match the Lean proof. All Lean files compile locally in import order.

## Proved and sorry left
Closed the original hole in `AlgebraicGeometry.Etale.higher_direct_image_transition_composition` (1 of 1).
Added two holes: `AlgebraicGeometry.Etale.higher_direct_image_transition_core_composition` in node `lem-sbc-higher-image-transition-core-composition`, and `AlgebraicGeometry.Etale.higher_direct_image_transition_naturality` in node `lem-sbc-higher-image-transition-naturality`. This is a decomposition, not a sorry-free proof. The first has no arbitrary coefficient maps; the second concerns one triangle and one coefficient morphism. The main module has no sorry.

## No longer needed
Removed proof imports `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction` and `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` from the main module. Their infrastructure is available through the unchanged public transition-definitions import.
The main theorem no longer directly uses `prop-weil-pbc-derived-inverse-image-adjunction`, `lem-weil-pbc-inverse-image-composition`, `lem-weil-pbc-exact-functor-derived-factorization`, or `lem-sbc-lower-star-plus-transition-comp`; these remain needed below the new composition/naturality statements and are not claimed to be globally pruned. No unit-level statement or proof step is bypassed. No additional whole module is known to leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong
The existing `LowerStarPlusTransitionComp` module cannot be imported directly here: it reaches the original source transition module, which reaches this module, creating a cycle. A trial import-only repair compiled, but it is not included in this delivery. The new canonical-coefficient composition node records this existing derived lemma as part of its mathematical plan; its eventual proof must repair that dependency route rather than duplicate the derived lemma.
Attempts to specialize generic adjunction naturality directly to the expanded derived transition definition exceeded the single-file limit. The final assembly uses the smaller coefficient-naturality statement instead. No definition or existing statement is changed. No axiom or data-valued sorry is added.

## New nodes
`lem-sbc-higher-image-transition-core-composition`, module `Sheaf.AlgebraicGeometry.HigherDirectImageTransitionCoreComposition`: composition with canonical pullback coefficients, before arbitrary f and g are inserted. Its docstring and node give the derived mate calculation and degree-zero comparison argument, including identity and zero edge cases.

`lem-sbc-higher-image-transition-naturality`, module `Sheaf.AlgebraicGeometry.HigherDirectImageTransitionNaturality`: naturality for one coefficient morphism and one triangle, derived from naturality of unit, counit and single-complex comparison. Identity and zero coefficient maps satisfy the stated equality. No change record is needed.

## Second reading by F1
1. Compared the delivered composition module with the repository version. The
   theorem signature is byte-for-byte unchanged; only proof imports and the proof
   body changed. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. The composition
   theorem has no `sorry`, and the only remaining holes are the two named split-off
   theorems, each with a matching DAG node and proof docstring. Verdict: pass.
3. Checked both split-off statements against their declarations and searched the
   repository for existing equivalents. They are strict reductions (canonical
   coefficients and one coefficient map), with identity and zero edge cases
   documented; no duplicate library theorem was found. Verdict: pass.
4. The proof uses the shortest available assembly from the two split-off lemmas;
   removed imports are recorded above. The unit-level route and its realized target
   are retained, and the known lower-star cycle is documented. Verdict: pass.
5. Updated the parent node's proof and `proof_deps` to match the Lean proof; the two
   new nodes carry their declarations, sources, routes, and metadata. Verdict: pass.

Changed only the parent proof/imports and added the two explicitly documented
split-off modules and nodes. No statement, definition, or unit route was changed.
