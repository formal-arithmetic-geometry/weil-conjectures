## What changed

Replaced the proof of `ModuleCat.exists_derivedExtension_ringEquiv_counit` without changing
its signature. Its proof imports two new modules privately. It obtains a raw derived-category
comparison `a`, applies derived homology, and composes with the homology descent isomorphism `z`.
The square follows from naturality of `z` at the universal counit, the factorization equation
for `z`, the raw counit equation mapped by homology, and naturality of the composite
homotopy/derived homology factorization at `t`. This is a genuine decomposition with a
completed homology step, not a closed proof of the universal derived transport itself.

Added `Sheaf.Algebra.Homology.DerivedRestrictionHomologyFactors`, fully proved directly from
Mathlib. It works for every ring homomorphism and any functor `E` equipped with a complex
localization factorization `q`. Construct the short-complex homology isomorphism on complexes,
compose with `q` and the homology factorization isomorphisms, and descend using
`Localization.fullyFaithfulWhiskeringLeft`. Its `preimageIso` and `map_preimage` yield the exact
factorization equation after cancellation. Neither scalar extension nor its counit appears
in this lemma.

Added `Sheaf.Algebra.Homology.DerivedExtensionRingEquivRawCounit`, containing the remaining
named obligation before any homology functor is applied. Its statement produces the
restriction lift `E`, localization factorization `q`, derived-category comparison `a`, and
raw universal counit equation, independently of the degree. The original module contains
no remaining `sorry`. All three modules compile together with no non-sorry warnings,
using the mandated single-file compiler and its import-ordered sandbox mode.

The original node's proof and dependencies now describe this actual argument. No existing
statement, definition, visibility, or public import was changed. No forced adaptations.

## Proved and sorry left

Closed the original hole `ModuleCat.exists_derivedExtension_ringEquiv_counit`
(node `lem-pc-derived-extension-ring-equiv-counit`) by a completed proof from the new
raw-transport obligation and the fully proved homology descent theorem.

Also proved the new theorem `ModuleCat.exists_derivedRestriction_homology_factors`
(node `lem-pc-derived-restriction-homology-factors`), with no holes.

The delivery adds exactly one hole:
`ModuleCat.exists_derivedExtension_ringEquiv_raw_counit`
(node `lem-pc-derived-extension-ring-equiv-raw-counit`), in its own new module.
Its docstring gives the complete transport/universal-property argument and source.
There are no other holes in the delivered modules. Thus this is one original hole closed
and one lower hole added: a decomposition, with net hole count zero, rather than a proof
free of unproved dependencies.

## No longer needed

No original import, node, or module was removed. The original public import remains necessary
for the public additive scalar-extension instance used in the statement. The two original
DAG definition dependencies remain necessary below the new raw-transport node; they have
not been pruned from the argument. The homology descent needs no universal-derived-functor
or tensor-product imports, and the raw node needs only the existing public model import;
redundant imports were removed from those new modules.

The tensor generator hypothesis `_ht` is not used by the completed upper proof. A supplied
natural tensor-transport isomorphism suffices for the raw transport: it descends through the
homotopy quotient using its naturality. The hypothesis remains exactly as originally stated.
No claim is made that a module becomes unreachable from the project targets.

## Where the brief, the DAG or earlier work was wrong

The original DAG names only the two definition nodes for a substantial right-Kan-extension
transport argument. Their recorded declarations define derived categories and ordinary
base change; neither supplies the raw transport theorem. That gap is now isolated in the
raw node instead of hidden in the original theorem's proof. The homology calculation does
have a short complete proof from existing Mathlib APIs, and is not another obligation.

Searches: LeanFinder found `leftDerivedNatIso`, `isLeftDerivedFunctor_iff_of_iso`, and
exact-functor localization factorizations, but no assembled ring-equivalence counit result.
Loogle found `Localization.fullyFaithfulWhiskeringLeft`. Local grep inspected the source
library's exact-functor homology API and the proved model-independence theorem's use of
`leftDerivedNatIso`, and Mathlib's localization and short-complex homology APIs. LeanSearch
was attempted and returned an Internal Server Error; its unavailability is recorded without
a negative search verdict. This did not block the other searches or compilation.

Edge cases checked mathematically: exact restriction preserves homology for arbitrary ring
maps, including zero rings; the factorization isomorphisms and localization full faithfulness
do not require nonzero objects, bounded complexes, or equal morphism universes. Raw transport
uses equivalences and universality, with no flatness or nontriviality assumption. The new
homology lemma accepts arbitrary `E,q` because `q` determines the needed localized homology
comparison up to unique natural isomorphism. No arbitrary witness of mere existence is used
to define library data. The item's node is not a realized unit statement or proof step
(the unit's `realized` entries are empty); the unit and chapter route are untouched.

## New nodes

`lem-pc-derived-extension-ring-equiv-raw-counit` is the derived-category portion of original
steps 1–2. It removes the homology degree and all homology factorization data from the
remaining obligation. Module: `Sheaf.Algebra.Homology.DerivedExtensionRingEquivRawCounit`.

`lem-pc-derived-restriction-homology-factors` is the fully proved exact-restriction homology
descent used in original step 3. It is independent of scalar extension, tensor generators,
and universal counits. Module: `Sheaf.Algebra.Homology.DerivedRestrictionHomologyFactors`.

No change records are needed: all existing statements and interfaces are unchanged.

## Second reading by F3

1. Compared the delivered counit module with the repository version. The existing theorem
   signature is byte-for-byte unchanged; the two new modules and their nodes are additions
   declared in this report.
2. Compiled all three delivered modules with `lcompile.py --all`. There are no errors,
   forbidden declarations, hollow definitions, or unlisted `sorry`s. The only remaining
   `sorry` is the named raw-counit theorem and its node.
3. Checked the split statements against the transport and localization arguments and the
   zero-ring and arbitrary-ring-map edge cases. The homology-factor theorem is fully proved;
   the raw-counit statement is the strictly smaller unresolved derived-category obligation.
4. Checked the proof route and imports. The upper proof uses the raw transport node and the
   proved homology descent, while the unit route is unchanged. No unused original import was
   found and no public import was added for proof-only dependencies.
5. Checked the DAG records against declarations, proof dependencies, sources, and origins.
   The nodes and report agree with the Lean code, and no existing target statement or
   definition changed.

Changed during second reading: appended this review record only; no Lean declarations or
DAG statements required repair.
