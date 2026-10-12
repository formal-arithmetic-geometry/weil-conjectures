## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.isIso_limit_pullback_comparison` in
`lean/Sheaf/AlgebraicGeometry/FibreProductLimit.lean` with an explicit inverse.
The two projections from the pullback of the limits give natural transformations
from its constant functor into X and Y. Their composites into S agree by the
limit projection equations and the pullback condition. Their functor-category
pullback lift gives a cone, whose limit lift is the inverse. Limit extensionality
and the pointwise pullback isomorphism prove the first inverse identity;
pullback extensionality proves the second.

Added the proof-only import
`Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks` for
`pullbackObjIso` and its projection equations. Removing this import was tested
and fails with an unknown `pullbackObjIso`, so it is necessary.
The declaration signature, visibility, public imports and docstring are unchanged.
The proof implements the original node's two universal-property steps, so no
DAG route change or new node is needed. The unit's route is preserved.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.isIso_limit_pullback_comparison`
(blueprint: `lem-kun-fibre-product-limits`). One of one holes proved outright;
zero holes added, zero split off. No `sorry` remains in the delivered module.
Local compilation passes without warnings. The delivery dry run also checks
that the declaration uses only permitted axioms.

## No longer needed

None. The original module had only its necessary public Mathlib import,
and the node had no proof dependencies to prune. No Sheaf or WeilConjectures
proof dependency is needed. The added Mathlib proof import is used.

## Where the brief, the DAG or earlier work was wrong

No discrepancy. General limit-functor preservation results require all limits
of the indexing shape, which the statement does not assume. The explicit cone
construction uses exactly the four indicated limit instances and the existing
scheme pullbacks. It works for arbitrary J, including the empty category;
no cofilteredness, nonemptiness or affine-transition hypothesis is introduced.

## Second reading by N1

1. Compared the complete delivered module with the repository using `diff -u`.
   Verdict: the existing declaration signature (including its compatibility proof),
   visibility, docstring and public import are byte-for-byte unchanged. Only the
   theorem body and a proof-only plain import changed. No definition was changed.
2. Independently compiled the delivered file with `lcompile.py`: clean, without
   warnings. Scanned for `sorry` and forbidden declarations/attributes: none.
   Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.isIso_limit_pullback_comparison`: exactly `propext`,
   `Classical.choice`, `Quot.sound`. Read the inverse construction: the natural
   transformations `a` and `b` are compatible by the pullback condition and
   `limMap_π`; their functor-category lift is a cone. Its limit lift `t` has the
   two required projection equations. Limit extensionality, cancellation of the
   pointwise pullback isomorphism, and pullback extensionality establish both
   inverse identities. Verdict: a complete proof, with no arbitrary witness or
   postponed data construction.
3. No statements were split off or introduced, so no new statement/node or
   duplicate split-off lemma requires review. The argument uses arbitrary `J`:
   in the empty case limit extensionality is vacuous and the pullback identity
   still follows from its two projections. No nonemptiness or cofilteredness is
   assumed. Verdict: zero additional holes.
4. Searched independently with Lean Finder for a pullback of limit cones and
   searched the local Lean library for the comparison and related names. The
   search returned general pullback universal-property APIs, not an exact
   replacement. Read Mathlib's Fubini and preservation APIs: the general limit
   functor route requires `HasLimitsOfShape J Scheme`, absent here. The explicit
   inverse is appropriate. Both imports are used; the new pointwise-pullback
   import is private. The original `proof_deps` is empty, so `No longer needed`
   is complete. Read `dag/units/sk-prop-sf-kunneth-ordinary.json`: its `realized`
   statement and steps are empty; this delivery changes neither the unit nor
   its route. Verdict: no pruning or route correction needed.
5. Read `lem-kun-fibre-product-limits.json` alongside the Lean proof. Its two
   elementary universal-property steps describe precisely this inverse and
   the verification that the comparison acts on the same compatible pairs.
   `proof_deps = []` and `proof_origin` remain accurate; no new DAG dependency
   is used. Verdict: no node edit needed.

Second reading changed only this report by adding the independent review;
no Lean repair was necessary. One of one holes closed, zero holes added.
