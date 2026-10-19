## What changed

Proved `CategoryTheory.Triangulated.TStructure.texact_truncation_comparison` in
`Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison`, with its entire signature
unchanged. The existing `Functor.eTruncLTIso` and `Functor.eTruncGEIso` supply existence,
object naturality, and their characterizing counit/unit equations. Mathlib's
`to_truncLT_obj_ext` and `from_truncGE_obj_ext` supply uniqueness. A proved private helper,
`cancel_truncGE_unit`, transports lower-truncation cancellation along an isomorphism.
The remaining proof explicitly checks arbitrary natural transformations, identity, and
composition for both signs. No new public declarations, definitions, or interfaces.

Removed the proof-only import
`WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology` and updated the existing
node's proof, proof dependencies, and proof origin to match the actual argument.
The theorem docstring now describes that implemented argument as well.

Searches: LeanFinder found general triangulated-functor infrastructure, Loogle
`"truncLT", "ext"` found `to_truncLT_obj_ext`, and msearch grep plus local source searches
found both Mathlib truncation extensionality lemmas and the upstream comparison equations.
The existing comparisons make a second construction from distinguished triangles unnecessary.

Validation: the complete module compiled cleanly through `lcompile.py` after removing the
unused import; rechecked against the current compiled library in 1.9 seconds. The signature
text was compared to the original and is identical.
The proof applies to every integer cutoff, retains independent category/hom universes, and
uses no boundedness simplification or compatibility hypothesis on the natural transformation.
Zero objects and identity comparisons require no exceptional cases; the identity clauses are
proved directly by the same universal properties.

## Proved and sorry left

Closed 1 original hole:
`CategoryTheory.Triangulated.TStructure.texact_truncation_comparison`
(node `lem-pod-texact-truncation-comparison`).

Added 0 holes; split off 0 statements. There are no remaining `sorry`s in this module or
elsewhere in this delivery. The private cancellation helper is completely proved.
This is a proof, not a decomposition.

## No longer needed

Removed import/module:
`WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`.
Removed proof dependency: `lem-weil-heart-short-exact-triangles`.
Its heart, short-exact sequence, and cohomological-functor machinery is unnecessary here:
Mathlib supplies the truncation extensionality principles directly, and the already public
`WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject` import
supplies the canonical natural isomorphisms and equations.

No other imports were removed. Both `def-weil-t-structure` and
`def-weil-triangulated-category` remain as dependencies. No blueprint unit statement or
unit proof step is bypassed; this is an implementation of a generic supporting lemma below
the unit level. No claim is made that the removed dependency is unused by other modules.

## Where the brief, the DAG or earlier work was wrong

The DAG's mathematical argument is sound, but it reconstructs the comparisons and their
object naturality even though these already occur in the statement as existing source-library
natural isomorphisms. The proof reuses their established characterization equations and only
proves the uniqueness/coherence clauses. The node's nine steps now record this implementation.
No statement or definition repair, new node, or consumer adaptation was needed.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
