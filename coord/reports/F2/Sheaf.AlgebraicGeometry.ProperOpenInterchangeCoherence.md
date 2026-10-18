## What changed

Replaced the single proof hole of
`AlgebraicGeometry.Etale.properOpenInterchangeCoherence` by an explicit construction
and a proof combining its normalization and coherence clauses. The ordinary comparison is
constructed from proper-support composition. Its normalization uniquely determines its map.
The derived comparison is the canonical `rightDerivedFunctorPlusBaseChange`; its invertibility
follows from open-extended-injective proper acyclicity. The full unit equation follows from the
generic factorization API, rather than from choosing another injective resolution. Vertical pasting is proved from the ordinary normalization and the composite derived-unit
characterization. Both identity
laws are proved from ordinary normalization and uniqueness of right derived maps.

The three remaining equality laws are isolated in two new modules, for fixed ordinary and derived
comparison isomorphisms: horizontal pasting, and refinement/base-change normalization. The original theorem statement,
universes, binders and public imports are preserved. Private helpers contain no holes. A local instance priority selects
the additive structure carried by the sheaf category's abelian instance in the derived APIs,
avoiding expensive comparisons with its definitionally equal full-subcategory additive structure.
No existing definition is changed. All three modules compile together without warnings
(the item takes 56.0 seconds). The unchanged existing consumer
`Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange` also compiles against the delivered
module without warnings (19.3 seconds).

## Proved and sorry left

Closed the original body hole of `AlgebraicGeometry.Etale.properOpenInterchangeCoherence` by a
compiling proof from the stated dependencies and the following two strict subproblems. This is a
decomposition (one hole removed, two added), not a complete proof of the coherence theorem from
proved dependencies. The construction, ordinary and full derived-unit normalization, vertical pasting and both
identity clauses have real Lean proofs.

Holes added, each the entire body of one named public theorem:

- `AlgebraicGeometry.Etale.properOpenInterchangeHorizontalPasting_of_normalization`, node
  `lem-cbc-normalized-proper-open-pasting`: still needs the ordinary horizontal support-pasting
  equality and its lift through the right-derived units and specified compositors.
- `AlgebraicGeometry.Etale.properOpenInterchangeGeometricNormalization_of_normalization`, node
  `lem-cbc-normalized-proper-open-geometric-normalization`: still needs the proper-refinement
  adjunction calculation identifying `properOpenComparison`, and the ordinary support cube
  together with the generic derived-cube theorem and identification of its exact faces.

No hole remains in the item module. No definition or private theorem contains `sorry`.
The two new statements assume the chosen derived map equals the canonical base-change map,
which the construction proves; they assert only proper subsets of the original conclusions and
contain no existential reconstruction of the original theorem.

## No longer needed

Removed proof-only imports:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`
- `Sheaf.AlgebraicGeometry.DerivedOpenRestriction`
- `Sheaf.AlgebraicGeometry.ClopenSectionDirectImage`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `WeilConjectures.SixFunctors.BaseChange.Derived`
- `WeilConjectures.SixFunctors.BaseChange.Square`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`

The parent proof no longer directly uses the following original proof dependencies:

- `def-weil-proper-morphism`
- `def-weil-finite-type-morphism`
- `def-weil-open-immersion`
- `prop-pur-kinjective-resolutions-exist`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-extension-by-zero-exact`
- `lemma-weil-pbc-leray-acyclicity`
- `def-weil-pbc-direct-image`
- `lem-weil-pbc-kinjective-hom-derived`
- `def-weil-pbc-proper-open-comparison`
- `lem-weil-pbc-derived-open-restriction`
- `cor-cbc-derived-extension-zero-base-change`
- `lem-weil-pbc-clopen-section-direct-image`
- `lem-weil-pbc-extension-by-zero-adjunction`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lem-weil-pbc-mate-pasting`
- `lem-cbc-extension-zero-base-change`
- `def-weil-pbc-extension-by-zero`
- `lem-weil-pbc-derived-exchange-module-termwise`
- `lem-weil-pbc-exchange-forget-coefficients`
- `def-weil-pbc-bounded-derived-subcategories`
- `lem-weil-pbc-proper-base-change`
- `lem-weil-pbc-open-immersion-base-change`

Several of these remain in the two new nodes' proof plans; this is direct-dependency pruning,
not a claim that they are globally unnecessary. The explicit choice and comparison of injective
resolutions in the parent is replaced by the source library's generic right-acyclic base-change
API. No module is withdrawn: in particular the DAG parents still need the full coherence theorem,
even where their Lean proof has not yet imported it.

Removed the following obsolete top-level `tool_uses` entries of the parent node (the maintainer
may retain approvals still needed independently):

- `prop-pur-kinjective-resolutions-exist`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-extension-by-zero-exact`
- `lemma-weil-pbc-leray-acyclicity`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-derived-open-restriction`
- `lem-weil-pbc-clopen-section-direct-image`
- `lem-weil-pbc-extension-by-zero-adjunction`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lem-weil-pbc-mate-pasting`
- `lem-weil-pbc-proper-base-change`
- `lem-weil-pbc-open-immersion-base-change`
- `lem-weil-pbc-exchange-forget-coefficients`
- `lem-weil-pbc-termwise-adjunction-homotopy`
- `lem-weil-pbc-derived-exchange-module-termwise`

## Where the brief, the DAG or earlier work was wrong

The existing source API already constructs and characterizes the derived comparison on every
bounded-below homotopy object. Repeating the resolution-independence argument in the parent's
plan is unnecessary. The parent node's route is updated accordingly; the blueprint unit and its
realized steps are preserved. No false statement was found, and no existing statement was weakened.

The new statements were checked on the zero coefficient ring, empty schemes, identity
refinements and pasting with an identity square: they reduce to the corresponding unique
zero or identity maps. The cube allows noninvertible exchange maps and uses all four
Cartesian faces; it assumes neither invertibility of exchange nor preservation of
injectives by inverse image.

The theorem is required by DAG parents whose Lean proofs are still holes; actual Lean import
reachability alone is not a valid reason to withdraw this item.

## New nodes

`lem-cbc-normalized-proper-open-pasting`, in
`dag/nodes/sec-smooth-purity/lem-cbc-normalized-proper-open-pasting.json`, isolates the horizontal pasting
law for already supplied comparisons. Its source is Stacks Tag 0F7D and the ordinary
support identification of 0F7B. It is strictly the equality part of the pasting argument.

`lem-cbc-normalized-proper-open-geometric-normalization`, in
`dag/nodes/sec-smooth-purity/lem-cbc-normalized-proper-open-geometric-normalization.json`, isolates
proper-refinement normalization and arbitrary base-change compatibility for the same fixed maps.
Its source is Stacks Tags 0F7B and 0F7F. The cube argument does not cancel an exchange map or
assume inverse image preserves injectives. Both node records include source proof steps,
statement dependencies, actual Mathlib search results, and verbatim Lean signatures.

Change record: `coord/changes/F2-proper-open-interchange-elaboration.md` documents the local
instance-priority and elaboration commands conservatively flagged by the interface scanner,
with all downstream users. No consumer adaptation is required.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
