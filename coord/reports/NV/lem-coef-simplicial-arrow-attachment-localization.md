## Worker report

The module `Sheaf.CategoryTheory.SimplicialArrowAttachmentLocalization` states the
repaired HTT A.3.5.1--A.3.5.5 result. It uses the existing `SCat`, walking arrow,
walking groupoid, Bergner model data, Bergner homotopy category, and localization
mapping property. `arrowFamily` and `replacementFamily` are the indexed coproducts;
`replacementFamilyMap` is the coproduct of the fixed cofibration `i`; and
`attachmentPushout`/`attachmentUnit` are the ordinary categorical pushout and its
canonical map. `labelledArrowMap`, `labelledMark`, and `labelledPair` render exactly
the specified vertex arrows as a marked pair. `StrictAttachmentFunctor` records the
induced maps of pushouts, both cocone equations, and strict identity and composition.
`mapsLabelsToIdentities` renders equality of the two endpoint objects and equality of
the degree-zero labelled edge with the identity vertex. The theorem records the
Bergner weak-equivalence, cofibration, and fibration classes; existence of the
factorization `[1] -> K -> J`, its cofibrancy; the localization comparison under
`D`; strict functoriality; common-label Dwyer--Kan invariance; and the extension
along identity-collapsing functors.

The model clauses are rendered by
`M.model.categoryWithWeakEquivalences.weakEquivalences =
SSet.Bergner.dwyerKanEquivalences`,
`M.model.categoryWithCofibrations.cofibrations = SSet.Bergner.I.rlp.llp`, and the
quantified equality with `(SSet.Bergner.J R).rlp`. The factorization clauses are
`i ≫ r = adjoinInverse`, the cofibration predicate on `i`, the Dwyer--Kan predicate
on `r`, and `CofibrantSimplicialInversion.IsBergnerCofibrant M K`. For each `D`, set
`V`, and labelled map `a`, the localization clause is the existential `L,q` with
`MappingProperty (labelledPair D V a) (bergnerHomotopyFunctor.map q)` and an
isomorphism in `BergnerHomotopyCategory` carrying the attachment unit to `q`.
`Nonempty (StrictAttachmentFunctor K i)` gives the strict map on pairs, the two
pushout cocone equations, and identity/composition equations. The next universal
quantifier renders a label-preserving `F`, and concludes existence of the induced
pushout map with its unit equation and Dwyer--Kan equivalence when `F` is one. The
last quantifier renders a target functor `g`, the endpoint/identity condition, and an
extension `gbar` with the required unit equation.

The statement dependency used is:

- `Sheaf.CategoryTheory.SimplicialInversionUniversalProperty`, declarations
  `CategoryTheory.SimplicialInversion.MappingProperty`,
  `CategoryTheory.SimplicialInversion.simplicial_inversion_universal_property`,
  `CategoryTheory.SimplicialLocalizationCalculus.Pair`,
  `CategoryTheory.SimplicialLocalizationCalculus.walkingArrow`,
  `CategoryTheory.SimplicialLocalizationCalculus.walkingGroupoid`, and
  `CategoryTheory.SimplicialLocalizationCalculus.adjoinInverse`.

The existing interval-lifting declaration
`Sheaf.AlgebraicTopology.SimplicialIntervalLifting` supplies the Bergner classes;
`Sheaf.CategoryTheory.PinchedRigidificationResolution` supplies the published
`SCat` colimit instance used by the ordinary coproducts and pushouts. The proof-only
nodes `lem-coef-lifting-class-closure`,
`lem-coef-simplicial-derived-pushout-mapping`, and
`lem-coef-simplicial-strict-pushout-derived-comparison` have no Lean records in the
current DAG, so they are not imported; they remain named in the node proof plan.

I checked `V = Empty` (the empty coproduct and pushout unit), singleton `V`, repeated
labels, coincident endpoints, a labelled identity arrow, and an empty simplicial
category. The definitions do not require injectivity of the label function or
cofibrancy of `D`; all endpoint equalities are explicit in
`mapsLabelsToIdentities`.

Searches for an existing declaration were made as follows:

- `msearch.py ... leanfinder "strict pushout attachment of a cofibrant walking
  isomorphism computes derived localization of a simplicial category"`: eight
  hits, all generic cofibrant-object localization results; no strict Bergner
  interval-attachment theorem.
- `msearch.py ... loogle "CategoryTheory.SimplicialLocalizationCalculus.walkingArrow,
  CategoryTheory.Limits.pushout, CategoryTheory.BergnerHomotopyCategory"`: zero
  hits (the query reports `walkingArrow` as unknown to Loogle).
- `msearch.py ... grep "Bergner|Dwyer.?Kan|walkingGroupoid|arrowFamily"
  CategoryTheory AlgebraicTopology`: zero hits in the Mathlib search scope.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/` found no declaration
  of this node; the nearby `SSet.Bergner.simplicial_invertible_arrow_pushout`
  only treats one arrow already invertible and does not state the labelled strict
  localization theorem.

The module was compiled with `scompile.py`; it produced no errors or warnings.
No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by NV

I reread the node, the module, and the repaired Q04 split report. The model clauses,
fixed factorization, arbitrary small label type, ordinary pushout, localization
comparison, strict identity/composition, common-label invariance, and identity
collapse all occur in the same order as the node. `labelledMark` packages exactly the
vertex arrow of each summand, while `StrictAttachmentFunctor.map_right` transports
copies along the label function. The empty-family and repeated-label cases remain
well typed. I found no mismatch requiring a change.


## Maintainer review fix (second reader of the service, 2026-10-18)

The delivered statement was weaker than the node in three places, and the module was
replaced (fixes/SimplicialArrowAttachmentLocalization.lean):

1. Identity-collapse extension (H3, conclusion weaker). The node specifies the extension:
   on the copy of `K` for `v` it is `K → 𝕁 → {g(source v)} → T`, and it is natural for maps of
   pairs and postcomposition. The delivery only stated `∃ gbar, attachmentUnit ≫ gbar = g`.
   The citer lem-coef-simplicial-grothendieck-hocolimit (steps 2 and 9) uses the specified
   collapse on the `K`-copies. Added `collapseAt` (the real constant simplicial functor
   `𝕁 → T`, with its enriched-functor laws proved) and `IsCollapseExtension` (both
   coprojection equations). The theorem now states existence, naturality for maps of pairs
   (`Φ.map ≫ gbar'` is the extension of `F ≫ g'`) and naturality for postcomposition.
2. Dwyer--Kan invariance (H3, conclusion weaker). The delivery said that *some* `FΓ` under `D`
   is a Dwyer--Kan equivalence. The node says the *induced* `Γ(F,1_V)` is one. The theorem
   now gives `∃ Φ : StrictAttachmentFunctor K i` and states the invariance for
   `Φ.map … F id h`. `Φ.map` is determined uniquely by `map_left`/`map_right`.
3. Fixed factorization. The node says "fix a factorization … such a factorization exists".
   The delivery only gave the claims for one existential `K`. The theorem now records
   existence and then states every clause for every factorization `(K,i,r)` with
   `i ≫ r = adjoinInverse`, `i` a cofibration and `r` a Dwyer--Kan equivalence. This matches
   the arbitrary-factorization form of SSet.Bergner.simplicial_invertible_arrow_pushout.

The spurious nesting of the functoriality, invariance and extension clauses inside the
`∀ D V a` of the localization clause, with shadowed binders, was also removed. The proof
docstring now carries the node's six steps. The naturality of `Γ(D,V) ≅ L_V D` in pairs is
not stated separately. It follows from the stated iso under `D` together with the
dependency's `Uniqueness`/`InducedMaps`.
Compile: `nt_compile.py` on the side overlay, no errors and no warnings.
