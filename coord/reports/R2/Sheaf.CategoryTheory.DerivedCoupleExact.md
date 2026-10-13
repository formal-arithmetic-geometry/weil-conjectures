## What changed

Proved `CategoryTheory.BigradedExactCouple.pageCouple_image_prefix` in
`Sheaf.CategoryTheory.DerivedCoupleExact` without changing any existing signature.
Constructed the families of alpha powers and image inclusions explicitly with private
recursive definitions. Private, fully proved helpers establish the two forms of the
alpha-power recurrence, monicity, alpha compatibility, and the image induction.
Added the proof-only import `WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits`
for `imageSubobject_comp_of_epi`. Updated the prefix node's proof route and the parent's
iteration step to match this argument. No statement, definition interface, or public
import changed. No arbitrary data is selected from an existence theorem: the new
families are explicit recursions; the pre-existing derived maps have uniquely prescribed
commutation equations.

## Proved and sorry left

Closed 1 of the item's original 1 holes:
`CategoryTheory.BigradedExactCouple.pageCouple_image_prefix`
(node `lem-sp-derived-couple-image-prefix`). No holes added, and no `sorry` remains
in the delivered module. The already proved `derived_couple_exact` and
`pageCouple_image` retain their proofs. Their existing imported dependencies can still
contain `sorry`; this delivery does not claim to close those dependencies.
The image-prefix proof uses `DerivedMaps.alpha_comm` from `ExactCouple`, rather than
the other three imported derived-couple lemmas. All private helpers are proved.

The compiler accepted the module without warnings. The zero case treats all integer
bidegrees and has image top, including when the object is zero. The successor argument
requires only abelian image factorizations and works equally for zero or invertible
alpha maps. No extra exactness, boundedness, or positivity hypothesis was added.

## No longer needed

No imports or modules removed: the three existing proof imports are still used by
`derived_couple_exact`. The prefix node no longer depends on
`lem-sp-derived-couple-exact`; it depends directly on `def-sp-exact-couple` and
`def-sp-abelian`. The parent's direct dependencies no longer include `lem-sp-abelian-refinements`
or `def-sp-abelian`: its exactness clauses apply the existing kernel-identities,
map-uniqueness, and boundary-vanishes nodes. Those imported helpers retain their
own dependencies; no whole-module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The old prefix plan unnecessarily called the parent exactness theorem at every
induction step. The existing `DerivedMaps.alpha_comm` equation suffices. Its old
proof dependency pointed back to its parent; this is removed in the delivered prefix
node. The earlier parent proof record had not recorded the already introduced prefix
lemma in its iteration step; the delivered parent now records that use.

The local literature copy `literature/stacks-project/homology.tex` is absent.
Read the sources online at https://stacks.math.columbia.edu/tag/011S and
https://stacks.math.columbia.edu/tag/0AMJ. The induction respects the iterated image
construction and the induced alpha restriction described there. The proper-base-change
unit's realized statement and proof steps are preserved. Search used `msearch.py`
leanfinder, loogle, grep, and local `rg`; no existing proof of the prefix was found.


## Second reading by R2

1. Compared the delivered module with the repository by `diff` and checked all three
   existing theorem signatures byte for byte: identical. Existing proofs are retained;
   the only added import is proof-only. No public definition or visibility changed.
2. Compiled the module with `lcompile.py`: clean, no errors or warnings. Searched for
   forbidden declarations and holes: none. A scratch copy printed axioms for all three
   public theorems and all eight private declarations. The prefix, image theorem, and
   every private declaration use only `propext`, `Classical.choice`, and `Quot.sound`.
   The unchanged `derived_couple_exact` additionally uses `sorryAx` from its imported
   open helper theorems. Explicit recursion constructs A and I. Existing derived maps
   are uniquely determined by their commutation equations (mono inclusions and epi
   projections), so there is no arbitrary witness construction.
3. No statements were split off and no holes were added. Read each private helper:
   they prove recurrence, monicity, compatibility, or image induction, each strictly
   part of the argument. Checked n=0, arbitrary integer indices, zero objects/maps,
   and invertible alpha: the isomorphism base case and epi-image successor argument
   cover these cases. Searched Mathlib and the project for image-composition results,
   including a fresh Loogle query for `"imageSubobject", "comp"`: the existing epi
   image lemma is used; no shorter complete prefix theorem was found.
4. The proof takes the direct image-factorization route and does not call the parent
   exactness theorem. Each of the four proof imports is used. The removed direct DAG
   dependencies are listed above; no module is pruned. Read the proper-base-change
   unit's `realized` statement and three steps: none is bypassed or changed.
5. Compared both delivered nodes with their originals. The prefix's induction route,
   dependencies, and origin agree with Lean. Repaired the parent's stale steps and
   dependencies to name the three existing helper theorems actually applied, the
   ExactCouple equations, and the prefix used for iteration. Node statements, Lean
   records, unit, and chapter are unchanged; there are no new nodes.

Second reading changed only the parent node's proof metadata and this report.
The Lean proof needed no repair.
