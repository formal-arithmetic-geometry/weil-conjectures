## What changed

Proved `FieldTheory.fg_separable_extension_is_filtered_colimit_smooth` without changing its
signature, visibility, or existing documentation. Convert `Algebra.EssFiniteType K L` using
`IntermediateField.fg_top_iff`, use the existing
`FieldTheory.exists_smooth_subalgebra_fraction_field`, and apply the proved new theorem
`FieldTheory.exists_smooth_fg_localization_family` in
`Sheaf.FieldTheory.SmoothFractionFieldLocalizations`.

The localization theorem constructs the ranges of the canonical injective maps
`Localization.Away f →ₐ[K] L` for nonzero `f : B`. Its denominator characterization proves
directedness and coverage. Smoothness transports through the algebra equivalence to each
range; finite generation follows from smoothness, finite presentation, and finite type.
All imports added to the item's module are proof-only. The new module publicly imports
only the Mathlib modules needed by its statement.

## Proved and sorry left

Closed the one existing hole:
`FieldTheory.fg_separable_extension_is_filtered_colimit_smooth`
(node `lem-kun-fg-separable-smooth`). No holes are added and no `sorry` is left in either
delivered module. This is a proof, not a decomposition into new holes.

The first worker's hole `FieldTheory.exists_smooth_fg_subalgebra_fraction_field`
(`new-smooth-fraction-field-fg`) was removed along with its unpublished module and node:
the existing smooth fraction-field theorem already supplies the required subalgebra,
and smoothness implies finite generation. The first worker's other hole,
`FieldTheory.exists_smooth_fg_localization_family`
(`new-smooth-fraction-field-localizations`), is now proved in full. The redundant `B.FG`
hypothesis was removed from this new, unpublished theorem; no existing signature changed.

## No longer needed

No repository import or old proof-dependency node was pruned. The original fraction-field
node `lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra` is used directly;
the original principal-localization node
`lem-weil-pbc-smooth-ring-map-principal-localization` is used through the new proved lemma.
Neither old dependency becomes unnecessary. The unpublished helper module
`Sheaf.FieldTheory.SmoothFractionFieldFG` and its node were deleted from the sandbox.

## Where the brief, the DAG or earlier work was wrong

The first worker overlooked the existing smooth fraction-field theorem and the fact that
smoothness already implies finite generation. Its two new nodes copied unrelated
blueprint/history/review fields from the parent, had empty proof dependencies despite using
non-elementary inputs, and recorded searches for the parent rather than the new statements.
The retained new node now records the actual proof, the principal-localization dependency,
and searches performed during this reading. LeanSearch returned Internal Server Error;
LeanFinder, Loogle and local source searches were available.

Read the Stacks Algebra source in the local literature copy at
`/home/ubuntu/work-bp/sheaf/literature/stacks-project/algebra.tex`, labels
`lemma-localization-smooth-separable` (Tag 037X), `lemma-colimit-syntomic` (Tag 07BV),
and the Mathlib principal-localization smoothness implementation (Tag 00T3).
The earlier reference to Tag 07BU for the smooth fraction-field theorem was inaccurate;
the existing library theorem correctly cites Tag 037X. The new module and node now use
the actual source labels. The existing item's documentation was preserved.

## New nodes

`new-smooth-fraction-field-localizations` records the proved localization-family theorem.
Its statement is the localization and directed-union portion of the original argument,
with a specified smooth subalgebra and fraction-field structure. It is strictly below the
item: it assumes no separability or finite field generation and does not construct the
initial smooth fraction-field subalgebra. No change record is needed: no repository
statement or definition is changed.

## Second reading by R3

1. Compared the item's entire module with the repository version using `diff`. The only
   changes are its proof and proof-only imports. Its existing declaration signature and
   visibility are byte for byte unchanged. The localization module is new; no definitions
   or target statements changed. Verdict: pass.
2. Compiled both delivered files in import order with `lcompile.py`, without warnings or
   errors. No `sorry`, axiom, unsafe, opaque, implemented_by, extern, or hollow definition
   occurs in either delivered module. Checked both declarations with `#print axioms` in
   scratch copies. The localization theorem uses only propext, Classical.choice and
   Quot.sound. The item uses those plus sorryAx through its existing smooth fraction-field
   dependency, whose upstream proof is still open. This delivery closes the item's own
   hole and adds none; it does not claim the whole import closure is axiom-free. Verdict:
   pass for stage 3 with that existing open dependency.
3. Read the new statement clause by clause. Fields K and L and the inclusion B⊆L ensure
   B is a nontrivial domain. For f≠0 the lift into L is injective. The index f=1 proves
   nonemptiness; f=0 is deliberately excluded. At exponent n=0 the membership criterion
   reduces to z∈B. For f=g=1 directedness gives B again. If B=L (a smooth field extension),
   all ranges equal L. The formulas z(fg)^n=ag^n and z(fg)^n=af^n work in every
   characteristic. IsFractionRing supplies a nonzero denominator for every z, including
   z=0. Smoothness gives finite generation, so the removed B.FG premise was redundant.
   Searches used different terms (fraction field, directed union, principal localization)
   in LeanFinder/Loogle and rg across Mathlib, upstream WeilConjectures and lean/Sheaf.
   No existing localization-family theorem was found. Removed the duplicative
   fraction-field helper; proved the retained lower statement. Verdict: pass.
4. The proof first uses the existing fraction-field theorem, then Mathlib smoothness under
   principal localization and composition. Its remaining denominator argument is elementary
   and fully written. Every import is needed for statements or the proof. Both old
   proof-dependency nodes remain used, so the pruning list is complete. Inspected
   `dag/units/sk-prop-sf-kunneth-ordinary.json`: its realized statement and steps are empty,
   and this delivery changes neither its route nor its records. Verdict: pass.
5. Checked the item's node and the retained new node against the Lean declarations. The
   item now depends on the existing fraction-field theorem and the new proved localization
   theorem. The new node cites the principal-localization Mathlib node, records the explicit
   construction, denominator criterion, smoothness, finite generation, directedness and
   coverage, and has the required source, origin, creation, search, blueprint, and Lean
   fields. Removed copied unrelated history from the new node. Verdict: pass.

Second reading changed: removed the duplicate fraction-field hole/module/node, proved the
localization-family hole, removed its redundant finite-generation hypothesis and inherited
helper import, restored the existing fraction-field dependency, repaired source references
and new-node metadata, and rewrote the report to state the actual hole accounting.
