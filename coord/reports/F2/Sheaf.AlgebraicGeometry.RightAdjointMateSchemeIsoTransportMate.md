## What changed

The original statement of `AlgebraicGeometry.rightAdjoint_mate_scheme_iso_transport_mate`
is unchanged. Its proof now identifies `r` as the pullback map induced by `e.hom`, proves
it invertible, obtains normalized comparisons for the two pairs of right adjoints,
constructs the source comparison from fixed pullback composition isomorphisms, and
assembles `Arrow.isoMk` using the normalized second-mate square.

`SchemeIsoRightAdjointNormalized.lean` proves the endpoint-comparison existence theorem.
The private categorical helper reverses an equivalence adjunction, composes it with
the supplied right-adjoint adjunction, and applies Mathlib right-adjoint uniqueness;
the normalization follows by the counit identity and cancellation. Its scheme proof
restricts the pinned derived adjunction through full QCoh inclusions. The normalization
is real data expressed as a proposition, not an arbitrarily chosen unproved witness.

`SchemeIsoSecondMateNormalizedSquare.lean` constructs the source isomorphism explicitly
and states the remaining equality for supplied, counit-normalized comparisons. It is
strictly a square calculation: it does not assert existence of endpoint comparisons
or of an arrow isomorphism. This is a decomposition, not a complete proof of the item.

## Proved and sorry left

Closed original hole: `AlgebraicGeometry.rightAdjoint_mate_scheme_iso_transport_mate`.
Proved new theorem: `AlgebraicGeometry.exists_schemeIsoRightAdjoint_normalized`
(node `lem-sc-scheme-iso-right-adjoint-normalized`). Its private helper
`AlgebraicGeometry.normalized_comparison` is also proved.

Added one hole: `AlgebraicGeometry.schemeIso_secondMate_normalized_square`
(node `lem-sc-scheme-iso-second-mate-normalized-square`), whose entire proof is `by sorry`.
No other sorry remains in the delivered files. One original hole closed, one lower
hole added: net zero holes, with the endpoint construction and assembly now proved.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.DerivedBaseChangePasting` and
`Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition` from the item.
The former is still a dependency of the new square calculation; it is not globally
pruned. The latter and node `lem-pc-ringed-spaces-derived-direct-image-composition`
are not needed on this branch: the relevant direct-image comparisons are constructed
as conjugates of the fixed pullback comparisons instead.

The other original dependency nodes remain needed through statements, constructions,
or the new square proof plan: derived pullback, ordinary base change, the fixed
second mate, QCoh preservation/right adjoints, pullback composition, and categorical
adjunction composition/uniqueness. The item’s public imports are unchanged. In the new endpoint module, the second
reader changed `DerivedPullbackTensorQCoh` to a plain proof import. In the new
square module, the redundant public `Mathlib.CategoryTheory.Adjunction.Mates`
import was removed; the needed mate API remains available through its statement
imports. The square now imports `DerivedBaseChangePasting` privately, as its
recorded proof plan requires.

## Where the brief, the DAG or earlier work was wrong

The original direct-image composition dependency can be bypassed by constructing
the needed comparison as the conjugate of pullback composition. No statement or
unit route was changed. The unit record has no realized node or step assigned to
this item; the proof still follows its source-isomorphism transport argument.

Edge cases checked: the normalization for identity scheme isomorphisms reduces to
ordinary right-adjoint uniqueness; twisting either supplied adjunction is accounted
for by its counit normalization. Zero objects and empty schemes do not require
invertibility of the second mate, only the ordinary comparison. All comparisons
are natural isomorphisms constructed from supplied data or a determining universal
property. The square statement requires the actual normalized comparisons, so it
cannot silently choose arbitrary endpoint automorphisms.

The Stacks references 0ATR and 0AA8 were read on the official website because the
local Stacks source is absent on this machine. Mathlib searches were run through
msearch.py (LeanFinder, Loogle, and grep) and recorded in searches.jsonl. Blueprint
searches for “right adjoint”, “0ATR”, and “isomorphism mate” found no duplicate of
these normalized comparison statements. The library's existing inverse-square mate
formula was also inspected as an alternate route.

## New nodes

`lem-sc-scheme-iso-right-adjoint-normalized`:
`Sheaf.AlgebraicGeometry.SchemeIsoRightAdjointNormalized`, a proved one-map
right-adjoint comparison with a counit normalization. This is usable independently
of any base-change square. Includes its supporting normalization proposition.

`lem-sc-scheme-iso-second-mate-normalized-square`:
`Sheaf.AlgebraicGeometry.SchemeIsoSecondMateNormalizedSquare`, the remaining square
identity for supplied normalized comparisons. Includes the explicit source
isomorphism construction. No change records or forced adaptations are needed.

## Second reading by F2

1. Compared the complete item module against the repository with `diff -u`.
   Its only changes are its two proof imports and the original theorem body;
   the existing signature, docstring, visibility and public imports are byte for
   byte unchanged. The two other modules and their declarations are new. No
   existing definition or statement was altered, and no change record is needed.

2. Read all three delivered modules, including the private categorical proof.
   The only delivered `sorry` is the complete body of the named square theorem
   listed above. No forbidden declaration mechanism or hollow definition occurs.
   All three files compiled locally with `lcompile.py --all`; the final delivery
   dry run also printed OK after compilation and the preflight. Explicit
   `#print axioms` checks in scratch copies show only propext, Classical.choice
   and Quot.sound for `normalized_comparison` and `schemeIsoMateSourceIso`.
   `SchemeIsoRightAdjointNormalized`, `exists_schemeIsoRightAdjoint_normalized`,
   `schemeIso_secondMate_normalized_square` and the original transport theorem
   additionally use sorryAx, as allowed for their remaining open dependencies.
   No other axiom occurs. The scratch checks were rerun on a stable artifact copy
   after two checks overlapped preflight regeneration of the sandbox artifacts.
   The source comparison is an explicit composition of fixed pullback isomorphisms.
   The chosen pullback comparisons are pinned by their derived universal property,
   and the chosen adjunctions by their Hom-equivalence equation. The endpoint
   comparison is constructed in a proved theorem by right-adjoint uniqueness;
   its counit normalization determines it, rather than permitting arbitrary data.

3. Checked the square from the top down against the fixed second-mate definition.
   Its two supplied normalized comparisons are exactly the counit comparisons
   for the inverse equivalence adjunctions; transposition gives the corresponding
   unit comparisons. Pullback composition coherence and ordinary base-change
   transposition therefore give the displayed commutative square, without requiring
   the second mate to be invertible. Identity isomorphisms reduce to right-adjoint
   uniqueness with its counit equation; twists of the supplied adjunctions are
   controlled by the normalizations. Empty schemes and zero objects impose no
   extra condition. This is a strictly smaller remaining calculation: existence
   of both endpoint comparisons and the arrow-isomorphism assembly are proved,
   not assumed again under another name. The new hole has a complete proof
   docstring and its own node. Independently searched LeanFinder for Beck–Chevalley
   compatibility with equivalences, Loogle for the iterated mates identity, and
   grep for conjugate composition/naturality and mate isomorphisms (searches.jsonl).
   Read the library’s `QCohInverseBaseChangeMate` and the other transport modules.
   The inverse-square formula is useful to a future square proof but does not
   itself supply source-isomorphism transport or duplicate either new theorem.
   The Stacks sources 0ATR, 0D5S and 0AA8 were checked on the official website.

4. The reduction first proves invertibility of r by Mathlib pullback.map, constructs
   the comparisons using Mathlib adjoint uniqueness, and uses only the remaining
   specified square for assembly. Corrected the proof-only public import of QCoh
   preservation, removed the redundant mate import, and restored the square’s
   private pasting-plan import. The original direct proof dependencies
   `def-pc-derived-base-change-map`, `def-pc-derived-pullback`,
   `def-sc-duality-equation-base-change-map`, `lem-cat-right-adjoint-composition`,
   `lem-pc-derived-base-change-pasting` and
   `lem-pc-qcqs-derived-direct-image-right-adjoint` remain through the new lemmas
   or the unchanged statements. Pullback composition remains directly needed.
   Only `lem-pc-ringed-spaces-derived-direct-image-composition` is bypassed, as
   reported under No longer needed. The unit `sk-thm-picard-duality` has empty
   realized statement and step lists; no unit realization or route was changed.

5. Compared the old and delivered node records: only lean/proof/proof_deps/
   proof_origin changed in the existing node. Its two steps match invertibility,
   normalized endpoint existence, explicit source construction and Arrow.isoMk.
   The new nodes have source, searches, creation/blueprint metadata, Lean records,
   and proof-dependency unions matching their written constructions or remaining
   proof plan. All statements stay unchanged. Verdict: valid decomposition,
   one original hole closed and one smaller square hole added, net zero holes.

Second-reading changes: import visibility and dependency cleanup in the two new
modules, and this independent review record. No proof, statement, definition or
DAG route was rewritten.
