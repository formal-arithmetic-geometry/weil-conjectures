## What changed

Proved `AlgebraicGeometry.isIso_of_isProper_of_isOpenImmersion_of_schematicallyDenseOpen`
in `Sheaf.Compactification.ProperOpenDenseIso`, preserving its signature and all public
imports. Properness makes the image closed. Its open complement W is disjoint from U,
so injective restriction into the sections on the empty intersection gives 0 = 1 on W.
Any point in W contradicts `LocallyRingedSpace.component_nontrivial`. The image is
therefore the whole target, and Mathlib's open-immersion criterion gives the isomorphism.
Updated the node's second proof step and proof origin to describe the actual proof.

The single-file server compile through `lcompile.py` passed with no warnings (4.7 s).
The argument covers empty schemes and empty U, and uses neither reducedness nor
quasi-compactness of U. No definitions, statements, or consumer modules changed.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.isIso_of_isProper_of_isOpenImmersion_of_schematicallyDenseOpen`
(node `lemma-nagata-proper-open-dense-iso`). Zero holes remain in the item. Zero holes
added; zero split off. This is a complete proof, not a decomposition.

## No longer needed

None. All four declared proof dependencies are used: proper closed image, open immersion,
schematic density, and the locally ringed space underlying a scheme. No imports were added
or removed, and no nodes or modules were withdrawn. No explicit cofinal-neighbourhood
argument is necessary: Mathlib's nontriviality lemma uses a single germ map to a stalk.
The existing public imports are retained as the statement's interface.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the assigned statement. The latest blueprint adds
quasi-compactness of the dense open and uses topological density, whereas the assigned
Lean statement and reviewed DAG intentionally impose no quasi-compactness. The proof
establishes this stronger existing statement directly, so no signature repair is needed.
The upstream `isIso_of_isProper_of_isOpenImmersion` likewise requires quasi-compactness
and cannot directly replace this theorem. The unit route is unchanged.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
