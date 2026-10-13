## What changed

Reduced `AlgebraicGeometry.rectangle_ordinary_geometric_direct`, with its statement unchanged,
to two strict ordinary steps: constructing the canonical comparison lifts and proving ordinary
compatibility of those lifts. The item's complete Lean proof obtains the comparisons, applies
ordinary compatibility, reflects the three given ambient component isomorphisms through the
fully faithful QCoh inclusions, and cancels their inverses to obtain the required identity.

Added `RectangleQCohComparisonLifts` and `RectangleQCohOrdinaryCompatibility`, each with one
named theorem, source, complete proof in words and DAG node. The first constructs the comparison
isos without any base-change invertibility assumptions; the second proves ordinary compatibility
for arbitrary comparison isos with the canonical component formulas. Neither restates the
inverse rectangle theorem. All data in their statements are the existing pinned choices.

Also added and fully proved `DerivedBaseChangeHorizontalPasting`: the horizontal ordinary law
for two commutative squares, without cartesian or invertibility assumptions. The ordinary
compatibility node uses this law alongside the existing upper-precomposition pasting law.

No existing public signature, public import, definition or target statement was changed.
Updated the parent DAG proof route and added the three new nodes. The full construction was
attempted in Lean repeatedly; unresolved QCoh restriction conversions are packaged in the two
strict steps rather than left inside the item's proof. Scratch attempts are not delivered.

## Proved and sorry left

Closed the item's one existing hole by decomposition:
`AlgebraicGeometry.rectangle_ordinary_geometric_direct`
(`lem-sc-rectangle-ordinary-geometric-direct`). Its combining proof has no `sorry`.

Fully proved the new theorem
`AlgebraicGeometry.schemeDerivedBaseChange_horizontal_pasting`
(`lem-pc-derived-base-change-horizontal-pasting`).

Added exactly two named holes:
- `AlgebraicGeometry.rectangle_qcoh_comparison_lifts`
  (`lem-sc-rectangle-qcoh-comparison-lifts`), in `RectangleQCohComparisonLifts`.
- `AlgebraicGeometry.rectangle_qcoh_ordinary_compatibility`
  (`lem-sc-rectangle-qcoh-ordinary-compatibility`), in `RectangleQCohOrdinaryCompatibility`.

This is a decomposition, not a net reduction in holes: one original hole closed, two added.
No hole was put inside a definition or private helper. Existing dependencies' holes are unchanged.

## No longer needed

Removed unused proof-only Mathlib imports `CategoryTheory.Adjunction.FullyFaithful` and
`CategoryTheory.Limits.Shapes.Pullback.Pasting` from the comparison-lift statement module.

Removed the item's import `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition`
and its proof dependency `lem-pc-ringed-spaces-derived-direct-image-composition`. That proof
branch is unnecessary: the comparison comes from conjugating the pinned pullback comparison
and cancelling the equivalence unit. This is the module/node pruned from this item's route.

Removed the direct import `Sheaf.AlgebraicGeometry.DerivedBaseChangePasting` from the item;
its module remains needed by `RectangleQCohOrdinaryCompatibility`, so it is not pruned.
The pinned pullback composition, ordinary/inverse QCoh base-change definitions, and both
ordinary pasting laws remain necessary. No realized blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing `schemeDerivedBaseChange_pasting` theorem is upper-left precomposition, rather
than horizontal composition of two successive base squares. The ordinary compatibility step
also needs the horizontal identity. The new proved theorem supplies the adjunction verification
omitted in Stacks Tag 0ATM. The planned direct-image composition dependency is unnecessary.

The two new intermediate statements were checked on their endpoints, on identity arrows,
empty schemes and zero objects. The construction uses the canonical scheme isomorphism and
adjunction equivalence unit; compatibility uses naturality and the two ordinary pasting laws.
Neither assumes the ordinary maps invertible. Those three invertibility assumptions are used
only in the combining proof of the original item.

## New nodes

`lem-pc-derived-base-change-horizontal-pasting`, module
`Sheaf.AlgebraicGeometry.DerivedBaseChangeHorizontalPasting`, proves horizontal ordinary pasting
from Stacks Tag 0ATM with the counit formula of Tag 08HY and pullback associativity of Tag 0D5S.

`lem-sc-rectangle-qcoh-comparison-lifts`, module
`Sheaf.AlgebraicGeometry.RectangleQCohComparisonLifts`, isolates construction and fully faithful
restriction of the two canonical comparison isomorphisms, with their precise ambient components.

`lem-sc-rectangle-qcoh-ordinary-compatibility`, module
`Sheaf.AlgebraicGeometry.RectangleQCohOrdinaryCompatibility`, isolates the ordinary pasting
identity for comparison isomorphisms satisfying those components and the fixed upper comparison.

All three nodes inherit the item's chapter and unit. There is no interface change and no
change record or forced adaptation is needed.

## Second reading by K4

1. Compared the delivered item with the repository version. The existing theorem signature is
byte-for-byte unchanged; only proof imports and proof text changed. The three added modules and
their node statements match their Lean declarations.
2. Compiled the delivered modules with `lcompile.py`; the horizontal pasting theorem and both
intermediate modules compile after correcting the universe-polymorphic comparison family. The
only remaining `sorry`s are the two named split-off theorems listed above; no forbidden commands
or hollow definitions occur.
3. Checked the split-off statements against their endpoint and identity cases and searched the
library and Mathlib for duplicates. They are strict intermediate claims, each needed by the
combining proof and stronger than a restatement of the target.
4. Traced the proof dependencies and imports. The obsolete direct-image-composition branch is
removed, while the unit's pullback composition and both ordinary pasting steps remain in the
route. The DAG proof and `proof_deps` agree with the Lean proof.
5. The realized unit route is preserved; no target or existing public declaration was weakened.

I changed `RectangleQCohComparisonLifts` to use a universe-polymorphic `Scheme` binder so the
pinned comparison family elaborates. No mathematical statement was changed.
