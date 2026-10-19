## Worker report

The sandbox carries the statement module
`Sheaf.CategoryTheory.SimplicialArrowAttachmentLocalization` and the node record for
`lem-coef-simplicial-arrow-attachment-localization`.  The module states the fixed
Bergner model structure and the strict interval attachment theorem, with all data
real and the theorem proof left as `sorry`.  The helper declarations are the
coproduct families `arrowFamily` and `replacementFamily`, their map, the labelled
arrow and pair predicates, the identity-collapse functor and predicate, the strict
pushout and unit, relabelling, compatibility, and the strict attachment functor.
They are all part of the attachment notion and are listed in the node's `lean`
record.

The theorem's Lean rendering matches the node clause by clause:

* `M : BergnerModelData.{u}` is existentially quantified.  Its weak equivalences
  are exactly `SSet.Bergner.dwyerKanEquivalences`, its cofibrations are exactly
  `SSet.Bergner.I.rlp.llp`, and for every
  `R : SSet.Bergner.IntervalRepresentatives.{u}` its fibrations are
  `(SSet.Bergner.J R).rlp`.
* The existential factorization is over `K : SCat.{u}`,
  `i : walkingArrow.{u} ⟶ K`, and `r : K ⟶ walkingGroupoid.{u}`; it states
  `i ≫ r = adjoinInverse`, the cofibration hypothesis on `i`, and the
  Dwyer--Kan equivalence hypothesis on `r`.
* For every such fixed factorization, the theorem states
  `CofibrantSimplicialInversion.IsBergnerCofibrant M K` and, for every
  `D : SCat.{u}`, `V : Type u`, and labelled map
  `a : arrowFamily V ⟶ D`, the existence of `L`, `q`, the
  `MappingProperty (labelledPair D V a)`, and an isomorphism between the
  homotopy image of `attachmentPushout D V K i a` and that of `L` carrying the
  homotopy image of `attachmentUnit` to the homotopy image of `q`.
* It then existentially supplies `Φ : StrictAttachmentFunctor K i`.  For every
  compatible map of pairs with a common label type and identity label function,
  a Dwyer--Kan equivalence `F` induces a Dwyer--Kan equivalence through
  `Φ.map`.  For every identity-collapsing `g : D ⟶ T` it supplies a `gbar` with
  `IsCollapseExtension`, whose definition records restriction to `g` and the
  specified `r` followed by `collapseAt` on every attached copy.  The next
  clause transports this extension along an arbitrary compatible map of pairs
  and postcomposition by `g'`; the final clause transports it along arbitrary
  postcomposition `H : T ⟶ T'`.

The only statement dependency is
`lem-coef-simplicial-inversion-universal-property`, imported from
`Sheaf.CategoryTheory.SimplicialInversionUniversalProperty`.  I read its full
signatures and docstrings: in particular `MappingProperty`, `Uniqueness`,
`InducedMaps`, `CompositionCompatibility`, and the theorem
`CategoryTheory.SimplicialInversion.simplicial_inversion_universal_property`.
The statement module also imports the proof-side simplicial model modules named by
the node's proof dependencies, as required by the stage-2 plan.

Edge cases checked against the statement and helper definitions include
`V = Empty` (the coproduct and extension clauses reduce to the original category
and functor), repeated or noninjective labels, coincident endpoints, labelled
identity arrows, and a one-object simplicial category.  All category, label, and
model universes are the single explicitly bound `u`; no independent smaller
universe is introduced.  The `collapseAt` definition has actual functor data and
contains no postponed data.

Searches for an existing notion or statement were made as follows.  The recorded
node searches include:

* `msearch.py ... leanfinder "Attaching a fixed cofibrant walking isomorphism to a simplicial category along a set of arrows computes derived localization and preserves Dwyer Kan equivalences"`: the hits were ordinary cofibrant-localization and pushout declarations, with no strict interval-attachment theorem.
* `msearch.py ... leanfinder "strict pushout attachment of a cofibrant walking isomorphism to a simplicial category computes derived localization of a simplicial category"`: the hits were general homotopy-category/localizer declarations, again no matching theorem.
* `msearch.py ... loogle "CategoryTheory.Functor.IsLocalization, CategoryTheory.Limits.HasPushout"`: zero matching declarations.
* `msearch.py ... grep "Bergner|Dwyer.Kan|walking.*isomorphism|localization.*pushout" CategoryTheory`: only unrelated `Extensive.lean` hits.
* `rg` over `WeilConjectures/` and `lean/Sheaf/` found no alternate declaration of this node's attachment theorem; the only matching project module is the one recorded here.

The existing module was compiled with `scompile.py` for this item and completed
without Lean errors or warnings (including the expected theorem `sorry` warning
suppression).  No statement correction or dependency repair was needed, and there
is no `STATEMENT-DISPUTED` finding.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
