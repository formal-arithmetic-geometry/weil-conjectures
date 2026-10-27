## What changed

Replaced the proof hole in `AlgebraicGeometry.NativeBaseChange.forget_mate` by the
mate-cube argument. The abelian native pullback square is compared with the geometric
square through the canonical abelian forgetting comparisons, and the proved `Functor.mapDerivedCategory_exactCube`
localizes that calculation. The proved `exchangeMate_cube` gives the derived mate
identity; cancellation of the specified target comparison gives precisely the existing
statement. All existing public signatures, definitions and public imports are preserved.

Added the proof imports `Sheaf.CategoryTheory.DerivedExactCube`,
`Sheaf.CategoryTheory.ExchangeMateCube`, and `Sheaf.WeilSheaf.DerivedForgetMate`.
The compositor equations use the identity composition laws in abstract iso-algebras.
They are specialized as natural-transformation identities before evaluation on objects,
so their proofs do not unfold the sheaf constructions. The two new private abelian
comparison definitions are irreducible, with explicit unfolding in their API proofs;
the square is pasted by proved abstract whiskering calculations. This also avoids
unfolding the geometric sheaf construction during kernel checking. A private abstract
localization helper accepts the natural-transformation cube and converts inverse faces
before specializing to native categories. Proved construction equalities identify the
localized faces with the unchanged public comparison definitions.
The new module isolates the single-adjunction canonical derived comparison needed at
p and p'. It does not contain a base-change square or a base-change conclusion.

Validation: `lcompile.py` compiled the completed item in 20.3 seconds.
The new normalization module also compiled separately. All profiling and diagnostic
options and the scratch module were removed before delivery.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.NativeBaseChange.forget_mate`
(node `lem-sf-native-base-change-forget-comparison`) by a decomposition.
There are no remaining holes in the item module.

Added one hole:
`CategoryTheory.Adjunction.derived_exact_forget_mate`
(node `lem-sf-derived-exact-forget-mate`). It asserts that right derivation of one
compatible adjoint square, with exact vertical functors and preservation of
K-injectives on the source side, preserves the specified mate and its canonical
unit normalization. The theorem is used twice for the vertical maps of the original
square. This is one original hole closed and one strictly lower hole added, a
net-zero decomposition, not a complete proof of the original theorem from closed facts.
All private helpers are proved; no definition contains a hole.

## No longer needed

No existing Lean import was removed and no module was withdrawn.
The planned wrapper `lem-weil-pbc-ringed-topoi-module-adjunction`
(`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`) is unnecessary here:
the actual native adjunction already has the required carrier counit.
The planned `lem-weil-pbc-kinjective-hom-derived` is also unnecessary for the
cube calculation; the remaining derived comparison uses the normalized universal
property rather than an explicit arbitrary derived-Hom calculation.

The previous direct dependencies `lem-weil-pbc-kinjective-total-derived`,
`lem-pc-derived-adjoint-functors`, `lem-kun-derived-adjoint-square-comparison`, and
`lem-sf-right-derived-from-adapted-complexes` now occur in the new single-adjunction
node's proof plan, rather than being direct dependencies of the item. They are still
needed below that node and are not claimed as globally pruned.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies provide the general normalized adjoint-square theorem, but
its hypotheses include concrete cochain Hom compatibility and right-derived unit
normalization. They do not directly identify the canonical native `pushForget` with
the mate of `pullForget.inv`. The new node isolates exactly that normalization bridge.
The final cube calculation and exact localization already have proved library lemmas;
no new base-change theorem or geometric assumption is needed.

The unit route and the target statements are unchanged. No properness, Cartesian,
boundedness, constructibility or non-characteristic hypothesis has been added.

## New nodes

`lem-sf-derived-exact-forget-mate`, in
`lean/Sheaf/WeilSheaf/DerivedForgetMate.lean`, is the single-adjunction part of the
item's former proof step 2. Its source is the blueprint's “Forgetting the Weil
structure” paragraph, with the canonical derived adjoint-square argument of Stacks
Tags 09T5, 0DVC and 0FND. Its docstring gives the complete normalization argument.
Identity comparisons give the identity case, and the K-injective-preservation
hypothesis is retained explicitly; no assertion that arbitrary mates are invertible
is used. There is no change record because no existing interface was changed.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
