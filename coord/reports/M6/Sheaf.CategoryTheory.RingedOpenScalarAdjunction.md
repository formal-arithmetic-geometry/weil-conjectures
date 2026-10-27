## What changed

Proved `SheafOfModules.RingedOpenScalar.comparison` in
`Sheaf.CategoryTheory.RingedOpenScalarAdjunction`, preserving its statement and
all existing public definitions and imports. The change record is
`coord/changes/M6-ringed-open-scalar-proof-helpers.md`; it documents the
preflight classification of added section-variable commands around private
helpers. No global instance is added. The presheaf comparison is the
sectionwise identity linear map. Its inverse extends through the module
sheafification Hom equivalence; after forgetting module structures it is the
sheafification of a presheaf isomorphism, so it is invertible. The Hom equivalence
also proves its normalization on the specified generators.

Private proved helpers identify the comparison as a mate from its unit equation,
obtain the counit equation, and lift both equations to complexes and strict
towers. A private proof import of
`Sheaf.SixFunctors.ExactLocalizationInverseMate` supplies compatibility of the
specified derived comparison with the specified exact derived adjunctions.
The same generic argument applies to the abelian tower categories.

Updated the proof, proof dependencies, and proof origin of
`lem-cbc-ringed-open-scalar-adjunction` to describe this argument. No public
interface, source-library file, or target statement changed.

## Proved and sorry left

Closed the one existing hole:
`SheafOfModules.RingedOpenScalar.comparison`
(`lem-cbc-ringed-open-scalar-adjunction`). Added zero holes, split off zero
statements, and left zero holes in the item module. The final item compiled cleanly in 54.2 seconds through `lcompile.py`, with
no errors or warnings. The first delivery preflight
requested a change record for the private-helper section commands; that record
is included and the private invertibility instance was made a theorem used locally. The existing proofs of
`scalarExact`, `sliceExact`, `adjunctionGenerators`, and `tupleAction` are retained.

## No longer needed

No Lean imports removed and no modules withdrawn. The direct appeal to
`lem-weil-pbc-localization-universal-property` in the final proof step is replaced
by the already proved `lem-sf-exact-localization-inverse-mate`; the former remains
needed transitively by that theorem. No claim is made that its module can be
pruned. The direct generator check for the counit is replaced by the general
mate counit identity, so no separate counit-on-sheafification lemma is needed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The prescribed sheafification and exact termwise
route is retained. The DAG's direct localization argument is implemented through
the existing inverse-mate theorem. An initial implementation using definitional
identity of independently presented additive sheafifications unfolded too much;
expressing the underlying map as abelian sheafification of the presheaf
comparison avoids that problem without changing any library definitions.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
