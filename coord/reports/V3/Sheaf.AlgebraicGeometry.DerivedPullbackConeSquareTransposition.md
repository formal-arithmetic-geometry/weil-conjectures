## What changed

Proved `AlgebraicGeometry.derivedPullback_cone_square_transposition` without changing its
signature. A functorial flat resolution gives a strict K-flat replacement of the source
arrow; the localized cone comparison is invertible by its distinguished-triangle morphism.
Two private, proved helpers construct that replacement and precompose the specified cone
homotopy. The three required equations follow from additive cone transposition and the
pinned K-flat derived adjunction formula.

Added two reusable, fully proved theorem modules:
`Sheaf.CategoryTheory.AdditiveAdjunctionConeSquare` and
`Sheaf.AlgebraicGeometry.KFlatPullbackAdjunctionComparison`. Their imports needed by their
statements are public; the item's new proof imports are ordinary imports. Updated the
item's node proof and dependencies to describe the functorial replacement route.
Elaboration options are scoped to individual declarations. No existing definition,
statement, visibility or target signature changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.derivedPullback_cone_square_transposition`
(`lem-pc-derived-pullback-cone-square-transposition`): one of one original holes.
Added no holes. The new theorems
`CochainComplex.additiveAdjunction_cone_square` and
`AlgebraicGeometry.kFlat_pullback_adjunction_comparison` are proved, as are all private
helpers. No `sorry` remains in any delivered Lean module. Independent `#print axioms` checks of all three public theorems and all three
private helpers show only `propext`, `Classical.choice`, and `Quot.sound` in the compiled
snapshot. In particular, none of their transitive dependencies contributes `sorryAx`.

## No longer needed

Removed the direct proof imports `Sheaf.Algebra.Homology.KFlatResolution`,
`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`, and
`Mathlib.Algebra.Homology.DerivedCategory.Fractions`.
The ordinary pullback adjunction remains needed and available through the statement
imports; its node `lem-pc-module-pullback-adjunction` is used by the new comparison lemma.

The item no longer needs `lem-pc-kflat-resolution`, its module
`Sheaf.Algebra.Homology.KFlatResolution`, or the right-fraction/refinement argument.
It also does not need the telescope-closure node `lem-pc-kflat-closure` or its module
`Sheaf.Algebra.Homology.KFlatTelescopeClosure`: the cone-specific node
`lem-pc-kflat-cone-direct-sum` suffices. These are removals from this proof's route;
other target routes can still require them.

For completeness, the other removed old direct proof-dependency edges are
`def-pc-derived-base-change-map`, `def-pc-derived-pullback`,
`def-pc-mayer-vietoris-image-chain-data`, and `def-pc-relative-mv-maps`.
These are delegated to `lem-pc-kflat-pullback-adjunction-comparison`, whose node
records those dependencies; their statement imports remain public where the unchanged
item signature needs them. They are not claims of modules leaving the targets' closure.
No unit statement or realized proof step is bypassed: `sk-thm-picard-coherence` has
`realized.statement = []` and `realized.steps = [[]]`.

## Where the brief, the DAG or earlier work was wrong

The original route is valid in principle, but its fraction argument is unnecessary:
`schemeModule_hasFunctorialFlatResolution` and the source library's
`kFlatResolutionFunctor` already give a functorial strict replacement. Also the planned
`lem-pc-kflat-closure` refers to telescope closure, whereas the needed cone closure is
`lem-pc-kflat-cone-direct-sum`. The existing theorem docstring is retained; the updated
DAG proof and this report record the shorter replacement construction.

The math search service `leansearch` returned Internal Server Error; no absence claim
was inferred from that failure. Local searches and the other search tools supplied the
component APIs. No statement was found false and no forced adaptation was needed.

## New nodes

`lem-pc-additive-adjunction-cone-square` records the chain-level compatibility of an
arbitrary additive adjunction with the specified homotopy cone map. It is stronger than
a statement only about homotopy classes, is proved by comparing cone components, and
applies to zero complexes and the zero homotopy without additional assumptions.

`lem-pc-kflat-pullback-adjunction-comparison` records a comparison isomorphism depending
only on a K-flat source, and its compatibility with every ordinary chain transpose into
any target complex. It is proved from uniqueness of left-derived counits and the pinned
derived Hom formula. Neither target K-injectivity nor boundedness is assumed. The zero
source and zero map satisfy the same formula by the additive functor construction.

No change record is required: no existing interface changed.


## Second reading by V3

1. Compared every delivered module with the repository. Only the item already exists;
   its complete theorem signature is byte for byte identical, including the family of
   derived-category instances, arbitrary morphism g, unbounded source/target complexes,
   specified homotopy, and all three comparison equations. The two helper modules are new.
   No existing definition, declaration visibility, public import, or target changed.
   No change record is needed.

2. Compiled each of the three files through lcompile.py. Checked every public theorem and
   private helper using `#print axioms` in scratch copies: replacement, cone_precompose,
   counit_isIso, additiveAdjunction_cone_square, kFlat_pullback_adjunction_comparison,
   and derivedPullback_cone_square_transposition all use only propext, Classical.choice,
   and Quot.sound. No delivered file contains sorry, axiom, unsafe, opaque,
   implemented_by, extern, or a hollow definition. The replacement uses the constructed
   reduced LeftResolution.kFlatResolutionFunctor and its augmentation, whose naturality
   gives the strict square; it selects no unconstrained witness from an unproved existence
   theorem. The first full-set compile timed out at 60 seconds for the item; subsequent
   single-file compilation and the axiom check succeeded within the same limit. This
   motivated checking the elaboration of concrete ring and adjunction types.

3. There are no split-off holes. Read both new statements against their proofs and sources:
   Stacks [014F](https://stacks.math.columbia.edu/tag/014F) gives the specified homotopy's
   off-diagonal cone component; [014P](https://stacks.math.columbia.edu/tag/014P) supplies
   the additive-functor/triangle context. The additive helper constructs H-prime with the
   mapped homotopy and counit, then compares both cone injections, retaining its sign.
   For the K-flat helper, [06YJ](https://stacks.math.columbia.edu/tag/06YJ) computes the
   derived counit on K-flat sources and [079W](https://stacks.math.columbia.edu/tag/079W)
   gives the derived adjunction. Uniqueness transports invertibility to the pinned counit;
   the library's exact normalized Hom formula yields the equation for every target.
   The comparison e depends only on P and its K-flatness proof, as required for all three
   uses. Neither statement assumes boundedness, flatness of g, or K-injectivity.
   Checked zero maps/complexes and zero homotopies by their additive formulas; the cone
   component calculation also handles nonzero homotopies, so it is stronger than a claim
   merely about homotopy classes. Searched again with LeanFinder for off-diagonal counit
   transposition, Loogle for leftDerivedUnique, and grep for mapOfHomotopy and counit
   formulas, plus rg throughout lean/Sheaf and lean/WeilConjectures. The results supply
   component APIs, not a duplicate of either theorem. Both helpers are proper parts of
   the argument and are fully proved.

4. Followed the proof downward: the functorial resolution gives x,y and a strict square;
   cone_precompose transports exactly the specified H; additiveAdjunction_cone_square
   transposes its actual cone map; distinguished-triangle two-out-of-three makes Q(c)
   invertible; K-flat cone closure supplies the third source; the pinned comparison and
   homEquiv naturality prove each of the three equations. The old fraction route is
   unnecessary. Checked import visibility and removed the new comparison module's
   redundant KFlat import (already exported through RelativeMVMaps). Expanded
   No longer needed to enumerate every removed old proof_deps edge and distinguish
   delegated dependencies from modules leaving the targets' closure. The unit's realized
   fields are empty; this route bypasses no realized unit statement or step.

5. Checked each node's lean.statement against the corresponding declaration and each
   proof_deps against the union of its proof steps' uses. Existing-node changes are
   confined to proof, proof_deps, and proof_origin. New nodes carry source, complete proof,
   search records, created item/group/date, blueprint ancestry, chapter/unit, and Lean
   declaration records. The item uses the functorial replacement, cone closure, additive
   transpose, and pinned comparison described by those records. Verdict: these nodes
   agree with the delivered Lean and the unchanged statement.

Second-reading changes: scoped the comparison helper's transparency options to each
individual declaration; removed its redundant public KFlat import; completed the pruning
report; recorded the independent statement, proof, source, search, unit, and axiom checks.
