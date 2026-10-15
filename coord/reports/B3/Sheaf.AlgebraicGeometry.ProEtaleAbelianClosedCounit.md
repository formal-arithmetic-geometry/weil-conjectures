## What changed

Proved `AlgebraicGeometry.ProEtale.abelian_closed_counit` in
`lean/Sheaf/AlgebraicGeometry/ProEtaleAbelianClosedCounit.lean`, keeping its signature and
public imports unchanged. The affine argument uses the opposite closed-site adjunction to
make precomposition fully faithful, then transfers full faithfulness through the affine
basis equivalences. An arbitrary affine-target closed immersion is transported to a quotient
immersion. The actual counit follows from full faithfulness of its right adjoint.

The global argument restricts to the inverse images of an affine open cover. Restriction
base change is the map induced by `Over.pullbackMapComparison`; its horizontal mate is
invertible by the site map/pullback adjunction. The double-mate and mate-counit identities
then show that the actual global counit is invertible after restriction. The existing theorem
`AlgebraicGeometry.ProEtale.isIso_of_isIso_localizationRestriction` supplies open-cover
conservativity.

Removed the two duplicate private conservativity helpers identified by the return:
`counit_isIso_app_of_restriction` and `counit_isIso_of_restrictions`. The proof now imports
and uses the existing conservativity theorem. Its module is unclaimed; its two theorem
statements now spell out `Over.map.sheafPushforwardContinuous`, the definitionally equal
underlying restriction functor, and no longer import the legacy lower-shriek API.
All remaining added geometric and categorical helpers are private and proved. The restriction
calculation adapts the proved library module
`WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale` to the
finite-coefficient definitions already used by this item's statement. The conservativity
module is reused directly rather than copied. Three existing callers in `Adic.DenseOpenUnit`,
`Adic.LisseInternalHom`, and `Derived.OpenCover` receive only the necessary goal-type refinements
listed below; their theorem signatures and imports stay unchanged. Two generic
categorical calculations keep scheme pullback constructions out of the expensive component
calculation. The item's DAG proof and proof origin now describe this argument.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ProEtale.abelian_closed_counit`.
No holes added, no split-offs, and no `sorry` remains in any of the five delivered Lean modules.
This is a proof from the existing dependency declarations, rather than a decomposition
into new obligations. The complete file compiles within the 60-second limit. `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` remains in its proof closure.

## No longer needed

The item's public imports are unchanged and all four original proof-dependency nodes remain in
the DAG. The plain proof-only import `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` was
removed; its needed finite-coefficient declarations arrive through the direct proof-only
imports listed above. There are no newly unnecessary DAG modules. In the existing conservativity module,
removed the public import
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs`; neither existing
conservativity theorem needs this inverse-image/extension-by-zero API. In the returned
item removed the now-redundant direct proof imports
`WeilConjectures.Mathlib.CategoryTheory.NatIso` and
`WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf`; the needed categorical declarations
are already available from the remaining imports. Removed the duplicate private declarations
`counit_isIso_app_of_restriction` and `counit_isIso_of_restrictions`. The explicit
left-Kan-extension and sheafification comparison calculations in the original proof plan are unnecessary:
full faithfulness transfers directly through the sheaf-to-presheaf inclusions and affine
restriction equivalences. No new statement modules are introduced for those calculations.

The second reading also removed the redundant direct proof imports
`Mathlib.CategoryTheory.Adjunction.Whiskering`,
`Mathlib.CategoryTheory.Adjunction.Opposites`, and
`Mathlib.CategoryTheory.Adjunction.FullyFaithful` from the item. Their needed declarations
are already exported through the remaining imports. In the conservativity module,
`WeilConjectures.Mathlib.CategoryTheory.NatIso` is now a plain proof-only import, and the
redundant direct `WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf` import is removed;
the public pro-etale site import already exports the latter module.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. In particular, the proof uses no quasi-compact-open-
complement, reducedness, finite-presentation, or qcqs-base hypothesis. The empty closed
scheme is covered by the same argument.

The returned proof duplicated two conservativity lemmas already in the library. That
was unnecessary. Importing their module previously clashed with this item's
finite-coefficient definitions because the conservativity module imported the legacy
lower-shriek API. The repair removes that dependency in place: both existing theorem
names and all binders are preserved, and their restriction functors are unfolded in the
hypotheses. The underlying mathematical and elaborated statements are definitionally the
same for existing callers. The objectwise proof uses `change` rather than the legacy
restriction evaluation lemma. No theorem is copied under a fresh name.

The static checker requests a record for added proof-scope commands:
`coord/changes/B3-proetale-abelian-closed-counit-private-scopes.md`.
The API-independent conservativity change is recorded separately in
`coord/changes/B3-proetale-conservative-api-independent.md`.

## Forced adaptations

The three affected caller modules are unclaimed. Their signatures, visibility and imports
are unchanged; only an explicit goal-type step restores the named restriction functor immediately
after application of the API-independent conservativity theorem. These edits are needed
because `rw` and typeclass search treat the explicit functor differently from its named
wrapper, despite their definitional equality. The exact lines are in
`coord/changes/B3-proetale-conservative-api-independent.md`.

- `WeilConjectures.SixFunctors.ProEtale.Adic.DenseOpenUnit`, original error at 159:
  failed to synthesize `∀ X, IsIso (...)` for the presheaf component of the explicit
  restriction functor. Added a two-line `change IsIso ((localizationRestriction ...).map ...)`.
- `WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom`, original error at 52:
  `rw` could not find `(localizationRestriction ...).map 0` in the goal containing the
  explicit site pushforward. Added one `change` line wrapping the same zero map.
- `WeilConjectures.SixFunctors.ProEtale.Derived.OpenCover`, original error at 73:
  `HasZeroObject (Sheaf (ProEt.topology (U i)) A)` instance search reached its deterministic
  20000-heartbeat limit. Added an explicit `show` refinement wrapping the same zero map. No heartbeat
  or time limit is increased.

All seven external callers were checked against the changed conservativity module.
`Adic.MayerVietoris`, `LowerShriek.Proper`, `UpperLowerStar.ClosedImmersion`, and
`Derived.ClopenIdempotent` compile unchanged and are not included in the delivery.

## Second reading by B3

1. Compared all five delivered modules with the shared repository and checked the existing
   declarations. `abelian_closed_counit` has exactly its original signature, with no added
   hypotheses. Read Stacks Tags 09AA (global closed full faithfulness), 09BL
   (affine counit), and 09BK (fully faithful cocontinuous site lift); their hypotheses
   agree with this route. The three adapted caller modules have identical signatures and visibility.
   The only two changed signatures are the explicitly recorded conservativity hypotheses:
   unfolding `localizationRestriction` gives precisely their new functor. The ordinary-API
   scratch compatibility check typechecks both original statements against the changed
   theorems. No definition or target statement is changed.
2. Compiled all five files with `lcompile.py`. Independently checked `#print axioms` for
   `abelian_closed_counit` and both conservativity lemmas: each uses exactly `propext`,
   `Classical.choice`, and `Quot.sound`. There is no `sorry` or prohibited declaration in
   the delivered files. The private base-change definition constructs the induced natural
   transformation directly; there is no arbitrary data chosen from unproved existence.
3. No statements are split off and no new holes or nodes are added. Checked the affine
   quotient argument also for the unit ideal (empty closed scheme), and the cover argument
   for empty schemes; neither requires a nonempty cover, radical ideal, finite presentation,
   or quasi-compact complement. The proof chooses the site adjunction only inside a proof.
4. Read the affine full-faithfulness proof, site-mate component calculation, pullback
   comparison, double-mate step, and final restriction-conservativity application. Searched
   the library and Mathlib for closed-counit/full-faithfulness alternatives. The existing
   ordinary-API theorem is for module coefficients and imports the conflicting ordinary
   definitions; it cannot directly prove this finite-coefficient abelian statement. The
   existing conservativity theorem is reused. The four original DAG dependencies remain
   genuinely used, including the affine-basis equivalence instances. The realized statement
   and three steps of `sk-thm-properbasechange` are unchanged; this node is below them.
5. Compared the node's proof, proof dependencies, proof origin, and Lean statement with
   the implementation. The proof describes the affine quotient reduction and the actual
   global counit via mates, rather than an unnamed counit isomorphism. Its dependency union
   is exactly its four recorded proof dependencies. No old dependency node is pruned.

Second-reading changes: made the conservativity module's NatIso import proof-only and
removed its redundant direct Sites.Sheaf import (already publicly imported by the site
module). Independently compiled all three original adapted callers against the changed
conservativity module: DenseOpenUnit fails instance search, LisseInternalHom fails its
rewrite, and Derived.OpenCover reaches the deterministic instance-search limit, confirming
that the goal-type adaptations are necessary. Replaced OpenCover's `change`, which the
unused-tactic linter intermittently flags, by an explicit `refine (show ... from ?_)`;
this retains the needed elaboration type and compiles without suppressing a linter.
Removed the item's three redundant direct Mathlib adjunction imports as listed above.
Updated the change record and report accordingly. The mathematical proof is unchanged.
