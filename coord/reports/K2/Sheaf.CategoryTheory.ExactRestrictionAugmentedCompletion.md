## What changed

Proved `CategoryTheory.ExactRestrictionAugmentedCompletion.exists_exactRestrictionAugmentedCompletion`
in `lean/Sheaf/CategoryTheory/ExactRestrictionAugmentedCompletion.lean` with its signature unchanged.
All existing definitions are unchanged. The proof constructs the normalized right-derived
limit comparison by derived uniqueness, constructs the left-derived tower comparison by
preservation of right Kan extensions under the localized exact right adjoint, and proves
the actual completion-unit equation on the resolving class before extending by localization.

Added fully proved private helpers for the contractible-summand resolution construction,
K-injective computation, exact localization of an adjunction with independent universes,
right-adjoint preservation of right Kan extensions, resolving-class extensionality, and
ordinary/unit normalization. The resolution construction follows the already proved helper
in `Sheaf.CategoryTheory.DerivedTowerCounitProjections`; that module is not imported.
Private proof imports now use the source right-derived-composition API and Mathlib's
whiskered-adjunction/localized-adjunction APIs. Updated only `proof`, `proof_deps`, and
`proof_origin` of `lem-weil-pbc-exact-restriction-augmented-completion` to match the proof.
No public signature, definition body, unit statement, or unit route was changed.

## Proved and sorry left

Closed the one existing hole in
`CategoryTheory.ExactRestrictionAugmentedCompletion.exists_exactRestrictionAugmentedCompletion`
(node `lem-weil-pbc-exact-restriction-augmented-completion`).
Holes closed: 1. Holes added: 0. Holes remaining in the delivered module: 0.
No split-off statements, axioms, or assumed proof obligations were added.
Validation: the final module compiles without warnings (21.6 seconds).
`#print axioms` for the theorem reports exactly `propext`, `Classical.choice`,
and `Quot.sound`. All Lean lines are at most 100 characters.

## No longer needed

- Removed private import `Sheaf.CategoryTheory.KInjectiveTotalDerived` and proof dependency
  `lem-weil-pbc-kinjective-total-derived`: the existing cochain K-injective derivability
  structure computes the supplied universal presentations directly. The specialized
  existence theorem and its chosen model are unnecessary here.
- Removed private import `Sheaf.SixFunctors.OpenTensorNormalizationData`: its exact-derived
  adjunction helper fixes common universes. The short Mathlib localization proof works
  directly at the four independent derived-category universes of this statement.
  The mathematical exact-derived-adjunction dependency is retained.
- Separate compatibility proofs for the augmented map and the constant-unit map from the
  earlier plan are unnecessary: their composite has a direct ordinary-map normalization.
  The augmented-derived-unit node and its module remain needed for the specified interface.

All original public imports are retained, including the unused Roos-triangle interface,
to preserve existing consumers. These are dependencies removed from this item's route; no claim is made that other
consumers no longer require their modules. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The original plan's separate augmentation and constant-unit
calculations can be replaced by one shorter calculation for their composite, tested on
resolving objects. Counits are cancelled only on that class, where invertibility is supplied.
The recorded exact-derived-adjunction helper does not accept the independent universes of
this item; its existing Mathlib localization argument generalizes privately without any
change to the public interface or to another module. The retained site-abelian import is
needed for Mathlib's constant-diagram additive instance.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
