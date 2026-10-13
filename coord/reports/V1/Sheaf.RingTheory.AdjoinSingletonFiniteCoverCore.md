## What changed

Replaced the sorry in `exists_finite_cover_adjoin_singleton_core` with a complete Lean
reduction to `exists_adjoin_singleton_splitting_cover`, in the new module
`Sheaf.RingTheory.AdjoinSingletonSplittingCover`. The latter states only the finite
splitting-cover construction with maximal contractions and coefficient-root witnesses.
It does not assert the normal principal open or the shifted local presentations.

Four proved private helpers clear a denominator, transport normality to prime
localizations, construct the normal principal open after arbitrary domain localization,
and shift the monogenic generator. The main proof constructs B as `Localization M`,
derives Noetherianity of B and the local presentation algebras, and composes the two
localization isomorphisms. All original public declaration signatures are unchanged.
The coefficient domain and fraction field supplied by the intermediate theorem are
shared by every maximal localization; no data-valued definition uses an unproved witness.
Updated the core node's proof and dependencies, and added a node for the remaining step.

Added proof imports `Mathlib.RingTheory.Localization.AsSubring` and
`Sheaf.RingTheory.AdjoinSingletonSplittingCover`. Changed
`Mathlib.RingTheory.Localization.Submodule` to a proof import: its Noetherian-localization
instance is needed only by the proof. The new statement module does not import it.

Validation: both sandbox modules compile without errors or warnings, with the supplied
single-file compiler. The reduction is a real construction and combination of arguments,
not application of a renamed copy of the original conclusion. The new statement's edge
cases include z in the coefficient ring (choose that coefficient as r), z=0, field base
rings, and inseparable splitting extensions; the construction needs no separability.
M avoids zero because its elements are images of elements outside the maximal ideal
under field embeddings. The coefficient-denominator localization is essential: finiteness
is over S_s before passing to S_m, not over the unlocalized original S.

## Proved and sorry left

Closed the sole original hole, `exists_finite_cover_adjoin_singleton_core`
(node `lem-weil-pbc-monogenic-maximal-finite-cover-core`), by decomposition.
No sorry remains in the original module.

Added one hole, `exists_adjoin_singleton_splitting_cover`
(node `lem-weil-pbc-monogenic-splitting-cover`). Its proof is exactly `by sorry`, with the
source and full construction in its docstring and node. This is one hole closed and one
added, hence a decomposition with net hole count zero, not an axiom-free proof of the
whole target. The denominator-clearing, normal-open, generator-shift and localization
isomorphism arguments are fully proved using Mathlib. No additional holes were added.

## No longer needed

Removed the direct public import `Sheaf.RingTheory.AnalyticallyUnramified`: neither the
statement nor its structural proof uses analytic unramifiedness. Its only direct library
importer, `Sheaf.RingTheory.AdjoinSingletonMaximalFiniteCover`, already publicly imports
that module itself. No analytic-unramified node is needed for this structural construction.

The original core's residue-polynomial, Nagata-localization, Japanese-domain,
integral-closure, finite-over-Nagata and integral-extension dependencies have moved to
the new splitting-cover node; they have not been pruned globally.
`lem-weil-pbc-integral-injective-lying-over` is no longer needed by this route: for each
maximal q of B already given, contraction and integrality suffice. No separate existence
of an ideal over m is used. This removes that dependency from this branch, without a
claim that other branches no longer need it. The new node
omits the original core's normal-localization dependency: that step is now proved in the
parent module. No globally unreachable module or node is claimed as pruned.

Removed the direct proof imports `Sheaf.RingTheory.FiniteOverNagata`,
`Sheaf.RingTheory.JapaneseDomain` and `Sheaf.RingTheory.NagataLocalization`.
`JapaneseDomain` remains available transitively through `NagataRing`; the other two
are needed only in the construction left open in the splitting-cover node.

For completeness, the old core proof dependencies removed from the core node are
`lem-weil-pbc-zariski-lemma`, `lem-weil-pbc-nagata-localization`,
`def-weil-pbc-japanese-domain`, `lem-weil-pbc-integral-closure-finite-extension-normal`,
`lem-weil-pbc-finite-over-nagata-nagata`, `def-weil-pbc-integral-closure`,
`def-weil-finitely-generated-module`, `lem-weil-pbc-finite-algebra-is-integral`,
`lem-weil-pbc-integral-injective-lying-over`,
`lem-weil-pbc-integral-prime-over-maximal-maximal` and
`lem-weil-pbc-integral-maximal-contracts-maximal`. All except lying-over remain
proof dependencies of the new splitting-cover node.

The retained `Mathlib.RingTheory.Localization.Submodule` proof import supplies the
Noetherian-localization instance. All other retained imports are needed by the statement,
proof or its typeclass instances. No unused proof imports remain.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically usable but hides several pieces of localization glue.
In particular, the finite module claim after clearing coefficient denominators is over
S_s, and the final finite cover is over S_m; it need not be finite over the original S.
The new node makes this explicit. Its remaining hole is exactly this construction,
through maximal contraction and root selection; the final shift, normality and
Noetherianity assertions have been removed from that hole and proved in the parent.

The repository's listed `literature/stacks-project/algebra.tex` is absent on this machine.
The source was read at https://stacks.math.columbia.edu/tag/0334, Step 5. LeanSearch returned
an Internal Server Error; LeanFinder, Loogle and source grep ran successfully and found no
existing splitting-cover theorem. No target, unit statement, unit step or existing
intermediate signature was changed. No other module was adapted.

## New nodes

`lem-weil-pbc-monogenic-splitting-cover`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-monogenic-splitting-cover.json`, records
`exists_adjoin_singleton_splitting_cover` in the new module. It isolates Steps 1--3 and
the root-selection part of Step 4 of the original node, without the shifted local ring
isomorphisms, Noetherianity conclusions or the normal principal open. It has a complete
source-based proof in words, existing dependency nodes, and four logged search kinds
(LeanSearch unavailable). The unit route is unchanged. Import visibility changes are recorded in
`coord/changes/AdjoinSingletonFiniteCoverCore-imports.md`; no signature changes or
forced adaptations were required.

## Second reading by V1

1. Compared both delivered modules with the repository. The splitting-cover module is
   new; the core theorem's complete signature is byte-for-byte identical (checked by
   extracting its text up to `:= by`). Only its proof, docstring, author line and imports
   changed. The import visibility changes have the supplied change record. No definitions,
   target statements or other existing modules changed. Verdict: pass.
2. Compiled both modules in import order with `lcompile.py --all`: clean, 2.0 s and
   8.5 s. Scratch copies with `#print axioms` verified all four private helpers use only
   `propext`, `Classical.choice`, `Quot.sound`. The core and splitting-cover theorem use
   those plus `sorryAx`, accounted for by the single reported splitting-cover hole.
   No forbidden declarations or data-valued definitions occur. Existential elimination
   takes place only in theorem proofs; no arbitrary witness is stored as defined data.
   Verdict: pass as a decomposition, not a completed axiom-free target proof.
3. Read the entire new statement, its docstring and node against Stacks Tag 0334,
   Step 5 (https://stacks.math.columbia.edu/tag/0334). The denominator-localized coefficient
   ring and its integral closure produce exactly the claimed finite extension and maximal
   contractions. Checked field bases, z=0, x already in R, and repeated or inseparable
   roots: the positive-degree product argument uses primality, not separability. Maximality
   is obtained by contraction to the local base followed by integrality over S_s, not by
   assuming R intersect m is maximal. Independent LeanFinder, Loogle and grep searches
   used splitting/integral-closure and subtraction queries; none supplies this cover.
   The remaining statement omits the normal open and shifted local presentations actually
   proved in the parent. It cannot be closed in a few minutes by the existing results.
   Verdict: true, needed, and a strict part of the argument.
4. Read all four helpers and the main proof top down. Normality comes directly from
   Mathlib localization, with the denominator represented by a genuine subalgebra;
   shifting uses equality of adjoins and existing localized ring equivalences. No unused
   source proof is duplicated, and no shorter direct cover theorem was found. Checked
   the sk-thm-p1 unit's `realized` statements and four step lists: unchanged, with this
   construction below unit level. Checked the direct importer retains both removed public
   imports itself. Expanded `No longer needed` to enumerate the removed proof imports and
   every removed old core dependency. No globally unreachable module is claimed.
   Verdict: pass.
5. Compared the old and new core JSON: only `proof`, `proof_deps`, `proof_origin` changed.
   The revised proof steps describe the actual Lean argument; their uses have exactly
   the listed union. Checked the new node's statement against its verbatim Lean signature,
   source-based proof, dependency records, searches, creation record, blueprint provenance,
   chapter, unit and split status. The new dependency exists in this delivery. Verdict: pass.

Second reading changed only this report: made the pruning inventory explicit and added
this independent review and axiom evidence. No Lean proof, signature or node needed repair.
