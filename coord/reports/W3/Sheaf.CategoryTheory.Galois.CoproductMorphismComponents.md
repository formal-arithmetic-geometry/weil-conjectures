## What changed

Proved `CategoryTheory.morphism_coproduct_connected_components` in
`Sheaf.CategoryTheory.Galois.CoproductMorphismComponents`, keeping its statement,
universes, visibility, docstrings and imports unchanged.

The proof follows Stacks Project, `pione.tex`, Lemma 0BN0
(`lemma-epi-mono`), item (8), and the existing node's pullback argument.
The Stacks exactness and conservativity fields supply preservation and reflection
of initial objects and pullbacks. Mathlib's cofan lemmas show that the mapped
target coprojections are jointly surjective and individually injective;
`reflects_mono_of_reflectsLimit` makes the original coprojections mono.
A point of each connected source fibre chooses a target summand. Preservation
of pullbacks supplies a point of the corresponding pullback, so connectedness
makes its first projection an isomorphism. Its inverse followed by the second
projection gives the component map; `pullback.condition` proves its required
equality. Dependent choice assembles the index function and component maps.

Validation: the complete module compiled through `lcompile.py` without errors
or warnings. A temporary `#print axioms` check was run and removed before
submission; its output is recorded below. No other modules require adaptation.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.morphism_coproduct_connected_components`
(node `lem-galois-coproduct-morphism-components`).

Proved 1 of 1 original sorries; added 0 holes; split off 0 theorems.
No sorry remains in the delivered module. The axiom check reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No imports removed, no nodes or modules pruned, and no new imports needed:
the existing public imports already expose the required Mathlib interfaces.
All original dependency nodes remain relevant as definitions or Mathlib tools.
In particular, `lem-galois-mono-iff-injective` is used via its recorded Mathlib
reflection lemma, rather than through a new project theorem.

The displayed component equations require neither the source cofan's colimit
property nor connectedness of the target summands. These hypotheses remain in
the unchanged signature. The proof also does not need uniqueness of the chosen
target index or a final coproduct hom-extensionality argument. No unit statement
or unit proof step is bypassed; the item node's planned pullback route is retained,
so its proof metadata does not need changing.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The existing node's plan is sufficient, and its
Mathlib tools are already available through the module's original imports.
Empty source and target index types need no separate construction: the
componentwise existence proof and dependent choice handle an empty source,
and joint surjectivity rules out a target with no summands when a source
component is present. All original index universes remain unrestricted.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
