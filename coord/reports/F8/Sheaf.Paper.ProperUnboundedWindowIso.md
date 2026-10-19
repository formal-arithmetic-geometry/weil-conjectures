## What changed

Proved both coefficient cases in `Sheaf.Paper.ProperUnboundedWindowIso`, following the unit's
window argument. A proved private helper applies the two canonical truncation triangles,
preserves them under the triangulated derived pushforward, and uses the existing
`DerivedCategory.isIso_homologyMap_mor₁` and `isIso_homologyMap_mor₂` lemmas. Their proofs are
the long exact cohomology argument in the node. The coefficient proofs invoke
`proper_indConstructible_unbounded` / `_padicAlgCl` on K and its truncations to obtain the
three IndCons memberships and the two required amplitude bounds. Existing
`indConstructibleDerived_sums_and_truncations` declarations supply truncation closure.
The private `dimension_bound` proves the conversion of the integer fibre bound to the
amplitude theorem's WithBot bound, including negative d and empty fibres.

Restored the missing standing separated finite-type positive-characteristic field setting
in both statements, with the same assumptions as the parent window and amplitude theorems.
This is a statement repair, not a proof of the former arbitrary-scheme claim. The current
branch has the external consumer
`Sheaf.Paper.ProperUnboundedWindow`. Its two calls are adapted in this repair to pass
`k p₀ hp₀ hpℓ X Y`, all already present in its hypotheses. Its signatures, visibility and
imports stay unchanged. `ProperUnboundedCoproducts` is a transitive importer; it does not
use either changed declaration and needs no adaptation. The conclusions still concern
the actual canonical maps.
The change record is `coord/changes/F8-proper-window-standing-setting.md`.

The DAG records the restored setting, actual truncation-closure dependency and proof route.
All new proof imports are private. Standard truncation imports replace the unrelated
homotopy-colimit bundle. Compilation through lcompile.py is clean, with no remaining sorry
in the module. No new theorem with sorry, definition, module or node was added.

## Proved and sorry left

- `AlgebraicGeometry.ProEtale.proper_unbounded_window_iso`: proved from the existing
  amplitude and truncation-closure declarations, after the documented statement repair.
- `AlgebraicGeometry.ProEtale.proper_unbounded_window_iso_padicAlgCl`: proved by the same
  argument for the condensed algebraic closure, after the documented statement repair.

Original holes: 2. Holes closed in the repaired statements: 2. Holes added: 0.
Sorries left in the item: none. No split-offs. The existing imported amplitude and
truncation-closure theorems retain their own sorries; these are the intended named
stage-3 dependencies, not proofs completed by this delivery. The private helpers are
proved without those sorried geometric dependencies. Node: det-proper-unbounded-window-iso.

## No longer needed

- Removed `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`; only the standard
  derived t-structure and canonical truncation triangles are needed. The module's
  homotopy-colimit, exact-couple and etale-cohomology bundle is not used here. The
  mathematical truncation dependency `def-kun-truncations` remains realized directly
  by Mathlib's standard truncation API.
- Removed `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses` and the
  corresponding explicit proof dependency/tool approval
  `lem-weil-pbc-ring-sheaves-grothendieck`: the internal module-object framework already
  provides its Grothendieck instance. No ringed-site universe transport is performed.
- Removed explicit imports of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution` and
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`, which are available through
  the derived triangulated-functor and homology-isomorphism APIs actually imported.
  Their underlying mathematical steps are still used and are not pruned from the DAG.

No proper amplitude, canonical triangle or long exact sequence step of the unit is bypassed.
No proof of stabilization, homotopy limits, or spectral sequences is developed in this item;
the existing amplitude theorem already supplies exactly what the window proof needs.

## Where the brief, the DAG or earlier work was wrong

The stage-1 expanded statement and stage-2 Lean signatures omitted the inherited
`sk-def-sfb-dc-setting` assumptions. The source detail says “as above”; the parent unit,
parent Lean theorem and stated amplitude declaration all retain the standing field setting.
The original Lean statement cannot use its declared amplitude dependency: it has no k,
positive characteristic distinct from ℓ, finite-type or over-base hypotheses. These are
restored explicitly in the item and its node, without changing any project target.

The main DAG citer `sk-lem-proper-unbounded-window` already has exactly these assumptions.
The other citer `det-proper-unbounded-window-ii-general` also omitted this setting in its
expanded prose and has no Lean attachment. Its expanded statement is repaired in the same delivery to restore the inherited setting
already explicit in its owning unit `sk-lem-proper-unbounded-window-ii`. Its proof is
unchanged and now uses the repaired window detail with the required hypotheses. There is
no Lean consumer of that DAG-only detail. Both corrected node records check their direct
citers. The current Lean consumer of the window-isomorphism item is adapted as above.

The DAG also omitted the available truncation-closure declaration as an explicit proof
input; the proof now records `det-ambient-ind-derived-sums`. The source's second triangle
writes its first term as a truncation of K; the DAG's already-corrected approach truncates
A directly, avoiding a redundant nested-truncation identification. This is the route used.

Edge cases checked in the proof: arbitrary integer q and d, including negative d and
empty fibres. The dimension helper treats d<0 separately and forces dimension bottom;
it never silently replaces a negative bound by zero. No nonemptiness of fibres is assumed.

The previous repair's downstream inventory was stale: the fresh 2026-10-19 scan lists
220 transitive downstream modules, while still finding only `ProperUnboundedWindow`
as an external textual user of either changed theorem. The change record now lists all
220 modules with their current holders and records why the unchanged parent interface
requires no further adaptation. The parent itself is currently unclaimed.


## Forced adaptations

`Sheaf.Paper.ProperUnboundedWindow` (unclaimed when checked): the original file was compiled
against the repaired `ProperUnboundedWindowIso`. It failed at lines 142 and 183 with
`Application type mismatch`: `p : X ⟶ Y` was expected to have type `Type _` in each
window-isomorphism application. The only changed lines pass the existing arguments
`k p₀ hp₀ hpℓ X Y` before `p`. Both theorem signatures and all other code are unchanged.

This repairs the return of head `f8f4bed504`: the consumer is now present in the change
record's `## Users` table and is adapted in the same delivery. The delivery tool rebuilds
the commit on the fetched current `sheaf-dag`. Revalidated on 2026-10-19: both Lean files
compiled cleanly together on the server (30.7 s and 5.2 s). Comparing the retained consumer
with current main shows exactly the two necessary call-site edits, with no signature,
visibility or import changes. The library-wide textual search still finds only this
external consumer of the two repaired declarations. No further proof holes were closed
or added during this repair retry; the delivered item has zero remaining holes.

The resumed repair refreshed the Users table against the current source graph: four newly
added transitive importers are now included. Both retained Lean files compiled cleanly
together again through lcompile.py before the fresh dry run.

The final resumed retry adds the newly present transitive importer
`Sheaf.SecSmoothPurity.ReductionCompatibilities` to the Users table (220 downstream
modules in the current scan). It does not mention either changed theorem. The required
external user `Sheaf.Paper.ProperUnboundedWindow` remains explicitly listed for both
changed declarations, with exactly the two necessary argument-list adaptations.

Final retry validation on 2026-10-19: `lcompile.py --all` compiled
`ProperUnboundedWindowIso` (1.8 s) and `ProperUnboundedWindow` (1.5 s) cleanly
on the server after one busy-server retry. Zero remaining holes in both delivered files.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
