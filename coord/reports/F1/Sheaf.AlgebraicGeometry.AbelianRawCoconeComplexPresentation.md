## What changed

Proved `AlgebraicGeometry.Etale.abelianRawCocone_complex_presentation` without changing
its signature or public imports. Added proof-only imports of
`RawRestrictedCohomologyNaturalIso` and `RestrictedAffineComplexSystemNatural`.
The proof uses the existing natural raw/restricted comparison, constructs the stage
and limit isomorphisms explicitly, proves both transport squares from the supplied
`hmap` and `hleg`, and transports the restricted geometric presentation. The private
proved helpers `comparison_square` and `presentation_of_iso` perform respectively
additive comparison and categorical transport; neither uses continuity.

Added `Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural`, containing the
geometric restricted-system obligation with simultaneous transition and leg
compatibility. It has no raw derived-Hom groups or prescribed raw diagram/cocone.
The source places are Stacks Tags 09Z1 (affine-object reduction) and 0EZM (the input
complex system), read online because the Stacks source is absent in this checkout.
Updated the item's DAG proof and dependencies to match the reduction.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.abelianRawCocone_complex_presentation`
(node `lem-sbc-abelian-raw-cocone-complex-presentation`). No sorry remains in the item.

Added: `AlgebraicGeometry.Etale.exists_restricted_affine_complex_system_natural`
(node `lem-sbc-restricted-affine-complex-system-natural`). Its proof is exactly
`by sorry`, with the full construction and coherence argument in its docstring.
This is a decomposition: one upper hole closed and one geometric hole added,
net zero new-hole progress. The raw comparison and both transports are proved
from the independently stated existing comparison theorem and the geometric input.
No other holes were added. Both private helpers are fully proved.

## No longer needed

No original imports were removed. No module is globally pruned.

Every old direct proof dependency absent from the new parent `proof_deps` is:
`def-weil-pbc-inverse-image`, `lem-weil-pbc-inverse-image-composition`,
`lem-weil-pbc-affine-morphism-permanence`, `def-pc-fibre-product`,
`lem-weil-pbc-etale-restriction-injectives`, and
`prop-weil-pbc-derived-inverse-image-adjunction`. These are delegated to the
geometric construction or raw/restricted comparison, not globally unnecessary.
The original direct dependencies for pullbacks, affine permanence, inverse-image
composition and derived adjunction are now used inside the geometric obligation
and the existing raw/restricted comparison, rather than separately in the item's
proof. They are not claimed unnecessary in the transitive closure.
`RestrictedAffineComplexSystem` and `HigherDirectImageRawAffineComplexPresentation`
were inspected but are not imported: their interfaces intertwine cocone legs only,
and do not supply stage naturality needed for this prescribed diagram.

## Where the brief, the DAG or earlier work was wrong

The original geometric restricted-system statement provides a restrictionIso for
each stage and proves its leg compatibility, but supplies no transition equation
for those same isomorphisms. Naturality of the legs cannot imply that equation:
legs are not assumed monic. Its construction in the docstring does produce the
needed natural isomorphisms, so the new obligation records that construction with
both equations explicitly. Existing declarations and statements were not changed.

Edge cases checked in the new statement: empty affine U and zero coefficients give
zero restricted groups and the equations still hold; degree zero is the ordinary
section comparison; a singleton directed index leaves just identity coherence.
There is no positivity condition on p, no nonemptiness assumption on U, and no
cohomology-colimit assertion. The unit realization record has no realized node
for this item, and the affine restriction and complex-system route is preserved.

The initial direct existential assembly repeatedly expanded the raw groups and
isomorphism composites, exceeding the per-file compile limit. The new geometric
obligation now uses the existing presentation definition instead of duplicating its
full dependent telescope, and generic proved transport helpers in the same module
avoid repetition of raw-group expressions. No file was split for compilation and
no existing definition or signature was changed.

## New nodes

`lem-sbc-restricted-affine-complex-system-natural` is the geometric restricted
single-complex construction from parent steps 1 and 3, with the omitted stage
naturality recorded explicitly. It is strictly smaller than the item: it has no
raw comparison, prescribed K or B, or transport along arbitrary raw isomorphisms.
The existing restricted-system node was checked and found insufficient for this
additional equation. Whole-blueprint searches for "restricted cohomology" and
"complex" found no exact existing realization of the combined construction;
Mathlib searches are recorded in searches.jsonl, including LeanSearch's service
failure. No change record is needed because no existing interface was changed.


## Second reading by F1

1. Compared the delivered item with the repository by `diff`, and separately
   compared the entire existing theorem telescope and conclusion byte for byte:
   identical. No existing definition, target, visibility or signature changes.
   The additional geometric theorem is in its own new module. Verdict: pass.
2. Compiled both delivered modules in import order using `lcompile.py`. The item
   has no `sorry`; the new geometric theorem has exactly its reported named
   `by sorry`. No forbidden declarations or hollow definitions occur. Witnesses
   of existence are eliminated inside a proposition proof, never selected by a
   library data definition. A scratch copy checks `#print axioms` for both
   private helpers, the item and the split theorem. Both helpers use only
   `propext`, `Classical.choice`, `Quot.sound`; the item and split theorem also
   use `sorryAx` through the explicitly open inputs. Verdict: pass.
3. Read the split theorem against `rawAffineRestrictedCohomology`, its fixed
   coefficient and pullback maps, and the presentation definition. The geometric
   construction is true and strictly separates the geometric part from the raw
   comparison and arbitrary-diagram transport. Checked degree zero, zero
   coefficients, empty affine U, singleton index, and identity transitions.
   The bound-zero single complexes and restriction of the coefficient colimit
   give the claimed presentation. Stage compatibility requires naturality of
   the construction, not cancellation of legs. Read Stacks
   [09Z1](https://stacks.math.columbia.edu/tag/09Z1) and
   [0EZM](https://stacks.math.columbia.edu/tag/0EZM); the additional explicit
   Lean coherence equations are an elaboration of their geometric setup.
   Independent searches used “Functorial etale cohomology ... base change”,
   `NatIso.ofComponents`, and `cohomology.*(pullback|map)|singleFunctor.*colimit`;
   they found no replacement for the geometric obligation. Searched the local
   library for restriction isomorphisms and complex presentations. The existing
   restricted-system theorem only intertwines legs and cannot supply stage
   naturality. Closing the geometric construction is not a few-minute proof.
   Verdict: valid decomposition, one closed hole and one added hole, net zero.
4. Read the categorical transport and both comparison squares from the top down.
   They use the existing raw/restricted comparison and exactly both equations
   of the new geometric theorem. The private transport helper retains every
   witness of the presentation. Public imports provide signature notions
   (including inverse-image coherence); the two new inputs are proof imports.
   Enumerated all six old direct dependency nodes no longer directly used.
   The unit `sk-lem-failure-field` has empty realized statement/step lists;
   no realized node or prescribed affine-restriction route is bypassed.
   Verdict: pass; no global module pruning claimed.
5. Checked both node records against their Lean declarations, proof steps,
   dependency unions, sources, search records, chapter and unit. Existing node
   changes are confined to the permitted proof fields. Added the omitted affine
   permanence dependency to step 1 and `proof_deps` of the new geometric node.
   No change record is needed: no existing declaration interface changes.
   Verdict: pass after this dependency correction.

Second-reading changes: completed the old-dependency accounting; restored
affine permanence in the new node's proof
plan; recorded this independent review. The mathematical proof was retained.
