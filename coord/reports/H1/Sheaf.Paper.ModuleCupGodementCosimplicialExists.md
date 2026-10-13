## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.Modules.moduleCup_godement_cosimplicial_exists`
with an explicit construction. The concrete operators define a quiver action, a path functor,
and a functor on the quotient by the simplex relations. Fullness of the presentation functor
is proved locally by strong induction on source plus target length. Its proved faithfulness
gives unique preimages, through which the quotient functor is transported to the simplex
category. Identity, composition, degree terms and both prescribed operator families are
checked in Lean. The existing theorem signature and docstring are unchanged.

Added `Sheaf.Paper.ModuleCupGodementRelations`, containing a concrete quiver construction
and a proved relation-preservation theorem. Coordinate evaluation and stalk-map calculations
establish Godement functoriality, unit and multiplication naturality, both unit laws,
associativity, and all six simplex identities by induction on iterates and Fin indices.

Added `Sheaf.CategoryTheory.SimplexPresentationFaithful`, proving faithfulness of the generic
simplex presentation. Pure sigma words are distinguished by Mathlib's admissible normal forms.
Order duality turns pure delta words into pure sigma words. A natural split embedding into
the double dual then recovers equality of the original pure delta words. Image comparisons
identify both blocks of an arbitrary epi-mono factorization.

Both added imports in the item are proof-only. Updated its DAG route and added two proved
nodes. All three delivery modules compile together without warnings through `lcompile.py --all`.
The unit record has no realized statement or steps for this item; its route is preserved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.moduleCup_godement_cosimplicial_exists`
(node `lem-sc-module-cup-godement-cosimplicial-exists`).

Also completely proved the new intermediate declarations:
`AlgebraicGeometry.Scheme.Modules.moduleCup_godement_relations`
(node `lem-sc-module-cup-godement-relations`) and `simplexPresentation_faithful`
(node `lem-sc-module-cup-godement-simplex-presentation-faithful`).
All private helpers are proved. No holes were added and no sorry remains in the delivery's
three Lean modules. Existing upstream assumptions are unchanged. No data is chosen from an
unproved mere existence assertion: the Godement action is concrete and presentation preimages
are unique by the proved faithfulness.

## No longer needed

None of the original imports or dependency nodes can be pruned: the Godement model and
codegeneracy constructions are still needed through the relations module. No unrelated
resolution, augmentation, flasqueness, pairing or stalk-contraction module is imported.
The abstract stalk-family adjunction construction is unnecessary: the existing pointwise
skyscraper adjunction suffices for the coordinate calculations. No original module is
claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The final passage from simplex identities to a functor has no ready-made complete realization
theorem in the pinned Mathlib. `GeneratorsRelations.Basic` provides the presentation and
quotient API, while `NormalForms` leaves pure-delta normal forms as a TODO. The missing
faithfulness is proved here using sigma normal forms and order duality; fullness is proved
by factoring off delta or sigma maps until reaching an identity. No new assumption is needed.

The blueprint ancestor lookup returns no imported blueprint ancestor for this recent chain
of Godement nodes. The new nodes follow the existing
`lem-sc-module-cup-godement-model-pairing` chain and identify the realization step.

Edge cases are covered by the Lean inductions: degree zero, endpoint indices, both adjacent
mixed identities, repeated collapses, zero coefficients, and a scheme with no points.
Product extensionality covers the empty product without assuming a point exists. The
presentation proof includes identities and maps to or from [0], allowing empty blocks.
No target or existing intermediate signature was changed.

## New nodes

`lem-sc-module-cup-godement-relations` records the proved concrete path-relation preservation
and its quiver construction. Its proof follows Stacks Tags 0FKR and 08N8, with explicit
coordinate computations, using the existing model and codegeneracy definitions.

`lem-sc-module-cup-godement-simplex-presentation-faithful` records the proved generic
faithfulness theorem of Stacks Tag 0168(c), using Mathlib sigma normal forms, order duality,
a split embedding into the double dual, and epi-mono factorization. It has no new proof
dependency node. Search records are actual logged searches; unavailable LeanSearch requests
are recorded as such. There are no change records or forced adaptations.

## Second reading by H1

1. **Visible interface: pass.** Compared the complete item against the repository with
   `diff -u`. The only edits are two plain proof imports, two private proved helpers,
   and the replacement of the original sorry. The existing theorem signature and
   docstring are byte for byte unchanged. Both other delivery modules are new; no
   existing definition, target, hypothesis, conclusion, or public import was changed.
   There are no forced adaptations or change records.
2. **Proof and trust: pass.** Read all three modules and compiled them together using
   `lcompile.py --all`: faithfulness 2.4 s, relations 28.2 s, realization 3.4 s, with
   no warnings or errors. A scratch copy with `#print axioms` checked
   `moduleCup_godement_cosimplicial_exists`, `moduleCup_godement_relations`,
   `moduleCup_godementQuiver`, and `simplexPresentation_faithful`: each uses exactly
   `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.
   A source scan found no sorry or forbidden trust escape in any delivered module.
   The quiver is explicit; quotient lifting uses a proved relation theorem; the
   presentation preimages come from proved fullness and faithfulness. No data is
   obtained from an unproved existence assertion.
3. **New statements and edge cases: pass.** No statement is split off with sorry.
   Both new theorem statements describe strictly separate ingredients of the original
   construction, and both are fully proved. Checked the coordinate evaluation
   identities against the actual product/skyscraper definitions and the proved
   `skyscraperHomEquiv`; checked all six index inductions, including degree zero,
   first and last indices, both adjacent mixed identities, and empty products.
   Read the admissible-sigma-list uniqueness, contravariant duality, pure-coface
   double-dual cancellation, and image-factorization arguments. Identities and
   empty blocks are covered explicitly. Verified the cited sources:
   [Stacks 0FKR](https://stacks.math.columbia.edu/tag/0FKR),
   [Stacks 08N8](https://stacks.math.columbia.edu/tag/08N8),
   [Stacks 0168(c)](https://stacks.math.columbia.edu/tag/0168), and
   [Kerodon 04FQ](https://kerodon.net/tag/04FQ) /
   [04FT](https://kerodon.net/tag/04FT).
4. **Route and pruning: pass.** Independently searched with Loogle for faithfulness
   of `toSimplexCategory` (no hits), LeanFinder for extension of face/degeneracy
   actions (presentation API, no complete extension theorem), and grep for
   `GeneratorsRelations|standardσ|simplex.*presentation`. Also searched the local
   Mathlib, Sheaf, and upstream source for presentation and Godement identities.
   Mathlib supplies the sigma normal forms and epi-mono factorization, while its
   normal-form file explicitly leaves pure-delta uniqueness as a TODO; the delivered
   duality argument fills that gap without a new assumption. The existing unit
   `sk-prop-av-cube` has empty realized statement and step lists; none is bypassed.
   Every direct import serves either the public interface or the proof. The two
   original proof dependencies remain used through the relations module, so neither
   dependency module is pruned; no unrelated module has been retained.
5. **DAG and Lean agreement: pass.** Checked the three node files against the actual
   declarations and proof bodies. The realization node records quotient descent,
   fullness/faithfulness, and generator equations. The relations node records the
   coordinate monad identities and six inductions; the faithfulness node records
   sigma normal forms, duality, and epi-mono comparison. Their dependency unions
   agree with their steps. New nodes contain source, complete proof text, searches,
   creation and blueprint provenance, unit/chapter, and exact Lean signatures.

Second-reading changes: appended this independent review and recorded additional
searches. No Lean or DAG repair was necessary. One original hole is closed, zero
holes are added, and no module is pruned; this is a proof, not a decomposition.
