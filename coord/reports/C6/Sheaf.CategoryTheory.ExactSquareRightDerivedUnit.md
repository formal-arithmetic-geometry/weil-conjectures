## What changed

Proved `CategoryTheory.Functor.exactSquare_rightDerived_unit` in
`Sheaf.CategoryTheory.ExactSquareRightDerivedUnit`, preserving its signature and the
postcomposition unit definition. The proved private helper
`isLeftKanExtension_of_isIso_on_kInjectives` implements the existing node's steps 2–5:
resolve representatives, lift derived morphisms into K-injective targets, construct the
factorization, verify naturality and factorization, and prove uniqueness by cancellation
and transport. The main proof verifies the unit is invertible on K-injectives, constructs
the comparison's input natural transformation with all canonical identifications, and
applies Mathlib's derived descent and extensionality lemmas. Surjectivity of the homotopy
quotient on objects converts the condition on complexes into natural-transformation
extensionality.

The existing six-step node proof and all four recorded proof dependencies are used;
there is no route change, new node, signature change, definition repair, or adaptation.
The current blueprint's direct-image paragraph and Stacks `derived.tex`,
`lemma-K-injective`, `lemma-K-injective-defined`, and
`lemma-enough-K-injectives-implies` were read. Searches through the supplied msearch
LeanFinder/Loogle/grep services and the pinned library found generic Kan-extension
infrastructure; the explicit K-injective argument supplies the remaining universal
property without adding any adjoint assumption on V.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Functor.exactSquare_rightDerived_unit`
(node `lem-sfb-exact-square-right-derived-unit`).

Proved 1 of 1 original sorries. Zero sorries remain in the item, zero holes were added,
and zero statements were split off. The private helper is fully proved.

The file compiled cleanly after import cleanup (9.4 seconds). A direct
`#print axioms CategoryTheory.Functor.exactSquare_rightDerived_unit` check returned
exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` is reachable.
The diagnostic command was removed from the delivery source.

## No longer needed

Removed the redundant direct proof imports
`Mathlib.CategoryTheory.Localization.Predicate` and
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`: the retained public imports
already expose their declarations. This does not prune either module from the
transitive dependency closure. No DAG dependency or module is made unnecessary:
all four recorded proof dependencies are used, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface defect was found. The DAG plan translates to Lean using
the pinned Mathlib Hom bijection and derived-functor descent API. The assertion does
not require U to preserve K-injectives or the comparison to be invertible, and neither
assumption was introduced.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
