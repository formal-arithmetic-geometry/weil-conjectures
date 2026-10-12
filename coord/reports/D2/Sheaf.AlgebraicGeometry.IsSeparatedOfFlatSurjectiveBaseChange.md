## What changed

Proved `AlgebraicGeometry.isSeparated_of_flat_surjective_baseChange` with its original
signature. Replaced the proof-only import of
`Sheaf.AlgebraicGeometry.UniversallyClosedOfFpqcCover` by proof-only Mathlib imports
`Mathlib.AlgebraicGeometry.Morphisms.FlatDescent` and
`Mathlib.AlgebraicGeometry.Morphisms.Immersion`. Public imports are unchanged.

The proof uses generic descent for the diagonal property of universal closedness,
then the preimmersion and closed range of the original diagonal. It follows the
02KU diagonal argument; all unit statements and realized steps stay unchanged.
Updated the existing node's proof, proof_deps and proof_origin accordingly.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.isSeparated_of_flat_surjective_baseChange`
(node `lem-weil-pbc-fpqc-descend-separated`). Proved 1 of 1; no sorry remains in the
item and no hole or new declaration was added. Local single-file compilation passes.
The delivery dry run also checks the allowed axioms.

## No longer needed

Removed import: `Sheaf.AlgebraicGeometry.UniversallyClosedOfFpqcCover`.
Its declaration `AlgebraicGeometry.universallyClosed_of_fpqc_cover`, node
`lem-weil-pbc-fpqc-descend-universally-closed`, and its proof-only dependency subtree
are no longer needed through this item. Other target paths may still need them.

The following original proof dependencies are no longer needed as separate steps:
`lemma-nagata-diagonal-base-change`, `lem-weil-pbc-cartesian-square-pasting`,
`def-weil-closed-immersion`, `def-weil-finite-type-morphism`, `def-pc-scheme`,
`def-weil-surjective-morphism`, `def-weil-pbc-fpqc-covering`, and
`lem-weil-pbc-fpqc-descend-universally-closed`. Definitions used in the statement
remain represented by stmt_deps and their existing public Mathlib imports; this
prunes only redundant proof dependencies. The canonical pullback identifications
are handled inside Mathlib's generic diagonal descent rather than explicit local
pasting and isomorphism arguments.

Retained the actual geometric inputs: closed immersions are universally closed;
flatness, surjectivity and quasi-compactness are stable under base change; every
diagonal is an immersion; a preimmersion with closed image is a closed immersion.
The single-map universal-closedness descent instance is recorded through
`lem-weil-pbc-universally-closed-affine-descent`'s Mathlib match, used in its full
general form rather than restricted to affine schemes.

## Where the brief, the DAG or earlier work was wrong

No statement error. The planned fpqc-family descent is unnecessary here because
Mathlib already proves descent along one surjective flat quasi-compact morphism,
and its generic diagonal descent performs the pullback identifications.
Searches through launcher LeanFinder, Loogle and grep found no direct separatedness
descent theorem but identified the generic diagonal descent instance. Local source
inspection supplied `IsClosedImmersion.of_isPreimmersion` and the diagonal immersion
instance. The referenced Stacks source file is absent in this clone; the proof route
is the documented 02KU argument in the existing node and the tagged Mathlib proofs.

## Second reading by D2

1. The delivered theorem has the same binders and hypotheses as the repository declaration: schemes `X`, `S`, `S'`, morphisms `f` and `g`, and instances `Flat g`, `Surjective g`, `QuasiCompact g`, and `IsSeparated (pullback.snd f g)`. The conclusion remains `IsSeparated f`.
2. The proof compiles without `sorry`, axioms, unsafe declarations, or hollow definitions. The diagonal descent instance is applied with exactly the stated covering properties, and the final closed immersion construction uses the diagonal's closed range.
3. The node's three proof steps remain the same mathematical route: universal closedness of the pulled-back diagonal, descent through the generic diagonal property, then immersion plus closed image. The Mathlib declarations used by the proof state these facts directly; no new statement was added.
4. I checked the edge cases represented by the hypotheses: the proof does not assume affine schemes or finite presentation, and uses the supplied quasi-compactness instance. The generic `DescendsAlong` construction handles the canonical pullback identifications.
5. The unit route is retained: the separatedness argument still proceeds through diagonal universal closedness and the 02KS descent step, with the existing unit and target statements unchanged. The proof-only import was pruned to the two Mathlib modules actually needed.

Second-reading changes: appended this review only; the first worker's Lean proof and node metadata were retained. The explicit `#print axioms` scratch check returned exactly `propext`, `Classical.choice`, and `Quot.sound`. The node diff changes only `proof`, `proof_deps`, and `proof_origin`; `proof_deps` equals the union of all step `uses`. Every removed old dependency is listed under No longer needed. No split-off statements need review, and the unit's `realized` statement and steps are untouched. Source inspection of Mathlib `FlatDescent.lean`, `MorphismProperty/Descent.lean`, `Immersion.lean`, and `ClosedImmersion.lean` confirms all three proof steps. A search of the local Mathlib, upstream, and Sheaf sources found no shorter direct separatedness descent declaration.
