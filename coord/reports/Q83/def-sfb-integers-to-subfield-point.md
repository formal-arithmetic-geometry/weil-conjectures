## Worker report

This delivery records an exact existing construction and adds no Lean module.
The primary declaration is
`Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing` in
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` (lines 149–154).
The secondary declaration is the publicly imported
`CategoryTheory.Sheaf.isMonHom_sheafCompose_map` from
`WeilConjectures.CategoryTheory.RingObjects.RingPresheaf`.
Together these give the condensed-ring map and its underlying tensor-ring-object
morphism. The construction works for any embedded subfield, so its specialization
to the finite intermediate fields named by the node requires no new definition.
I also read the named finite specialization
`AlgebraicGeometry.ProEtale.padicIntegersRingObjToContinuousMapRingObj` in
`WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` (lines 92–105),
including its full docstring, signature, body, surrounding binders and adjacent
`IsMonHom` instance, and confirmed that larger module
using `scompile.py --source`. The smaller owning module is recorded to avoid
its unrelated derived-category import closure.

Hypothesis and clause correspondence:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]` in the surrounding variable declaration.
- The finite embedded extension is represented by
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)` and the recorded construction
  is applied to its underlying field `E.1`.
  In `WeilConjectures.CategoryTheory.RingObjects.EllAdic`, this abbreviates
  `{E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) // FiniteDimensional ℚ_[ℓ] E}`.
  Thus both the embedding and the finiteness hypothesis are present, with no
  arbitrary extra norm or topology. The recorded map needs only `(E : Type) [Field E]
  [Algebra E (PadicAlgCl ℓ)]`; the finite subtype supplies all of these.
  Finiteness is a restriction of the definition's domain, not missing data
  or an additional property needed to construct the map. No scheme parameter
  is present.
- The ring of integers is `PadicAlgCl.integers ℓ E.1`, defined in
  `WeilConjectures.NumberTheory.Padics.Extension` as the valuation subring of
  `valuationOfAlgebra`. Its membership lemma is exactly the absolute-value
  bound `‖algebraMap E.1 (PadicAlgCl ℓ) x‖₊ ≤ 1`.
- The continuous ring inclusion is `(PadicAlgCl.integers ℓ E.1).subtype` together
  with `continuous_subtype_val`. The condensed-ring map is the primary
  declaration above, defined using `continuousMapRingSheafMap` after installing
  `PadicAlgCl.normedFieldOfAlgebra ℓ E.1`, the restricted norm and topology.
- The section formula `f ↦ f`, with inclusion into E understood, is literally
  postcomposition: `continuousMapRingSheafMap` is the sheaf map whose presheaf
  component is the ring homomorphism `φ.compLeftContinuous _ hφ`, conjugated
  by `ULift.ringEquiv`. The existing lemma
  `Profinite.continuousMapRingPresheafMap_app_apply` displays this formula.
  The lifts implement `RingCat.{u + 1}` on `Profinite.{u}` and change no sections.
- The underlying condensed abelian group map is the image of the primary map:
  `(sheafCompose (coherentTopology Profinite.{u})
  (forget₂ RingCat.{u + 1} Ab.{u + 1})).map` applied to that same ring-sheaf map.
  Its source is `Profinite.padicIntegersRingObj.{u} ℓ E.1` and its target is
  `Profinite.continuousMapRingObj E.1`.
- The final ring-object-morphism clause follows from the recorded
  `CategoryTheory.Sheaf.isMonHom_sheafCompose_map`. It also appears as the
  adjacent existing instance
  `IsMonHom (padicIntegersRingObjToContinuousMapRingObj.{u} ℓ E)`.
  It is obtained from the same forgotten sheaf map, using
  `CategoryTheory.Sheaf.isMonHom_sheafCompose_map`; this preserves tensor
  multiplication and the integer unit, rather than merely additive structure.

Dependency declarations read and used:

- `sk-def-sfb-condensed-ring`: `Profinite.CondensedRing` in
  `Sheaf.Topology.ProfiniteCondensedRing` is the transparent abbreviation
  `Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})`.
  I followed its public imports and read the continuous-map constructors in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap` and
  the subfield/integer constructors in `...Condensed.EllAdic`. These give the
  actual objects and canonical map used here. This existing binding reuses
  that exact ring-object encoding; it does not introduce another construction.
- `sk-def-sfb-ring-object`: `CategoryTheory.Functor.monObjCompForget₂` in
  `WeilConjectures.CategoryTheory.RingObjects.RingPresheaf` gives objectwise
  ring multiplication after forgetting to Ab. I also read the recorded
  `Sheaf.monObj_sheafCompose_obj`, `Sheaf.sheafifyRingPresheafIso` and
  `Sheaf.isMonHom_sheafCompose_map`: the sheaf structures use the counit
  transport from sheafified objectwise tensor. The existing inclusion uses
  precisely these instances.

Edge cases checked by reading the construction: the trivial finite extension
E = Q_ell is admitted (`⊥` in `FiniteIntermediateField`); every prime, including
2, is admitted; arbitrary profinite S, including the empty set, is admitted
and the postcomposition formula still applies to its unique function.
Zero and unit are preserved because every component is a RingHom. Restriction
along any continuous map u commutes with postcomposition by associativity of
function composition, as witnessed by the presheaf map's `naturality := rfl`.
The site universe u is arbitrary, and the embedded subfield of the fixed
Type-0 PadicAlgCl loses no extension named in the source. No completeness,
Noetherian scheme, uniformizer or nonempty-S hypothesis is added.

Searches performed (the exact wrapper summaries are in sandbox searches.jsonl):

- LeanFinder: “The continuous inclusion of the ring of integers of a finite
  p-adic field induces a morphism of condensed rings by postcomposition”.
  Eight hits, headed by `PadicInt.Coe.ringHom`, then completion comparisons;
  no full Mathlib match.
- LeanSearch: “A continuous ring homomorphism induces a morphism of condensed
  ring objects by postcomposition”. Eight hits, headed by
  `TopCat.continuousFunctions.map`; these give component maps or unrelated
  completions, not the full inclusion and tensor-morphism assertion.
- Loogle: `TopCat.continuousFunctions.map, Subring.subtype`: zero hits.
- Mathlib grep via msearch: `padicIntegersRingObjToContinuousMapRingObj|continuousFunctions.map|commRingYoneda`
  in `Topology/Sheaves`: three hits in `CommRingCat.lean`. I read lines 208–252;
  these are generic commutative-ring-valued presheaf constructions.
- Project rg on `lean/WeilConjectures`: the exact primary name found its
  definition in `CategoryTheory/ModuleObjects/EllAdicRationalization.lean`;
  related inclusion searches found the exact condensed-ring map in
  `CategoryTheory/RingObjects/Condensed/EllAdic.lean`.
- Project rg on `lean/Sheaf`: the name occurs as a consumer in
  `AlgebraicGeometry/ProEtaleCoefficientComparisonsPullback.lean` and in an
  UpstreamExtra module docstring; no competing definition was found.
- The blueprint-id search on `lean/WeilConjectures` and the exact-name search
  in `dag/lean_names_upstream.json` returned no hits. Direct source inspection
  and the live-source read above establish the existing binding nonetheless.

No statement correction, disputed statement, new node or dependency repair is
needed. Only the item's `lean` field changes. No existing Lean file is edited
and no new proof is supplied.

## Second reading by Q83

I made a separate second pass with the node, blueprint statement/proof and both
existing definitions open; no second agent was started, as the dispatch brief
forbids it. The maintainer supplies the independent review of this delivery.
The important checks were that the primary map is on the point (the unused X
is not retained), that E is a *finite intermediate field* rather than an
arbitrary field, and that the target topology is inherited from PadicAlgCl.
The primary declaration supplies the ring-sheaf map; applying the
forgetful sheaf functor supplies exactly its underlying abelian map. The
recorded generic IsMonHom instance supplies the final clause, and the named
finite specialization inspected in the larger module confirms this is the
same construction. The ULift wrappers account only
for the site convention. Each hypothesis and clause is accounted for above;
no mismatch or change to the statement was found.

## Validation

The first dry run tried the larger rationalization module and failed while
compiling `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat`: its
imported `WeilConjectures.Mathlib.Algebra.Homology.Localization.olean` was
missing from the published build. The record was repaired by importing the
smaller owning `RingObjects.Condensed.EllAdic` module and recording the
canonical ring-sheaf map together with the general IsMonHom instance.
No source, definition or mathematical statement was changed.

The revised existing-declaration probe compiled cleanly through scompile.py;
`deliver2.py --no-push` returned OK with preflight and compile both passing.
The earlier exploratory probe importing the broader dependency closure was
cancelled after the smaller validated binding was selected.
