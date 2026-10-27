## What changed

Replaced the proof of `AlgebraicGeometry.qcqs_etale_topos_inverse_limit` by a
complete Lean assembly of the original argument. Its signature, universes, public
import and existing definitions are unchanged. All edits are confined to the item,
three new component modules, and their DAG records.

The item now proves the finite-cover points argument in Lean: colimit coverings
have finitely many distinct arrows; the finite composition/base-change axioms give
`IsSiteForCoverings`, including repeated indices; every indexed cover has a finite
refinement. `finitarySite_enoughPoints` supplies the conservative family, and
`Scheme.etaleToposPoint_isGeometric` identifies its projections with separably
closed geometric stalks. A proved singleton-site presentation of sets allows the
limit universal property to factor every supplied geometric-point cone. The
reindexed presentation's existence follows by transporting qcqs through the
scheme-diagram isomorphism and applying the same existence component.

The remaining construction steps are isolated as the three new public theorems
listed below. Each is a proper component, rather than the original conjunction
under another name. Each has a source, full proof in words, and matching DAG node.
The original dependency frontier is retained transitively through these nodes.

Validation: all four modules compiled together through `lcompile.py --all`.
The new modules took 3.5, 3.7 and 3.9 seconds, and the item took 6.3 seconds,
with no errors or warnings. The item's theorem signature was compared verbatim
with the original. All delivered Lean lines are at most 100 characters.

## Proved and sorry left

This is a decomposition, not a complete proof without new obligations: one
original direct hole was removed, three component holes were added (net +2).
The item itself contains zero `sorry` occurrences.

The removed hole is
`AlgebraicGeometry.qcqs_etale_topos_inverse_limit`
(`lem-per-qcqs-etale-topos-inverse-limit`), whose proof now compiles from the
component declarations and the existing enough-points/classification declarations.
Its finite-cover, points, sets-topos, and reindexed-existence assembly contains no
additional holes.

Exactly three `sorry` declarations remain in the delivery:

- `AlgebraicGeometry.QcqsEtaleLimit.presentation_nonempty`, in
  `Sheaf.AlgebraicGeometry.QcqsEtaleLimitPresentationExists`, node
  `lem-per-qcqs-etale-limit-presentation-exists`: original Steps 1–3 only.
- `AlgebraicGeometry.QcqsEtaleLimit.presentation_isToposLimit`, in
  `Sheaf.AlgebraicGeometry.QcqsEtalePresentationToposLimit`, node
  `lem-per-qcqs-etale-presentation-topos-limit`: original Steps 4–5 for an
  already supplied presentation, with finite-limit preservation made explicit.
- `AlgebraicGeometry.QcqsEtaleLimit.presentation_comparison`, in
  `Sheaf.AlgebraicGeometry.QcqsEtalePresentationComparison`, node
  `lem-per-qcqs-etale-presentation-comparison`: original Step 7 for two
  already supplied presentations.

All three are public named theorems with whole proofs `:= by sorry`.
There are no new definitions with postponed data, private holes, or axioms.

## No longer needed

No mathematical dependency or module is pruned: all sixteen original proof
inputs remain needed transitively by the component argument. The original
`tool_uses` approvals are therefore retained.

Six private imports were removed from the item: 
`Mathlib.CategoryTheory.Limits.MorphismProperty`,
`Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv`,
`Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`,
`Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings`,
`WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact`, and
`Sheaf.CategoryTheory.PseudofunctorSplitFamily`.
Their relevant roles moved to the existence/comparison component modules;
MorphismProperty is already supplied by the public presentation API.
The item retains the two point-theory imports and adds only its three component
imports, `Mathlib.CategoryTheory.PUnit` and `Mathlib.CategoryTheory.Sites.Finite`.
There are no withdrawals and no source-library edits.

## Where the brief, the DAG or earlier work was wrong

No statement was corrected or weakened. The supplied general dependencies do
not directly package the scheme-specific normalized presentation, its topos
universal property, or its canonical reindexing comparison. Those remaining
assembly steps are now explicit component items instead of being hidden inside
one large proof.

The passage from finite indexed axioms to site axioms must account for a cover
presented with infinitely many repeated arrows. The Lean proof works with the
finite uncurried presieve, and proves equality of the original and distinct-arrow
pullback presieves. Treating the original index type as finite would be invalid.

The local ILO source was checked at XX 4.4, printed p.373 (PDF p.379), and the
local Stacks sources at Sites 09YL, 0A35 and 00YQ. The current blueprint unit and
its realized route are unchanged. Edge cases checked: empty schemes and empty
covers, identity reindexing with different strictifications, arbitrary nonempty
cofiltered categories, and non-affine qcqs transitions. No limit scheme is used.

## New nodes

`lem-per-qcqs-etale-limit-presentation-exists` states existence of the site and
normalized projection data only. It preserves original Steps 1–3, with the same
strictification, finite-cover comparison, filtered category and colimit-site
inputs. Its corresponding module is `QcqsEtaleLimitPresentationExists`.

`lem-per-qcqs-etale-presentation-topos-limit` takes an existing presentation and
states its two-clause universal property only. Its proof in words uses
pseudococone restriction and lex-cover extension, including all natural
transformations and their adjunction mates. Its module is
`QcqsEtalePresentationToposLimit`.

`lem-per-qcqs-etale-presentation-comparison` takes two existing presentations and
states the canonical comparison over initial reindexing and diagram isomorphism
only. Its proof uses final reindexing and coherent objectwise equivalences of
filtered category colimits, dense site comparison, and full faithfulness of
extension. Its module is `QcqsEtalePresentationComparison`.

Each node has fresh LeanSearch, LeanFinder and Mathlib grep searches. Hits concern
limits inside a fixed topos, affine-transition scheme limits, or unrelated
reindexing equivalences; no component statement was found. The existing source
and Sheaf roots and the blueprint were also searched. No change record is needed:
no existing interface or statement was changed.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
