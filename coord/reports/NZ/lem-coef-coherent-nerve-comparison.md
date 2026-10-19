## Worker report

Repair of returned immutable head `23874fdc7710`, H5/H3. This delivery replaces
its hollow clauses and false replacement interface. The item JSON was refreshed
from the current shared node, preserving its statement, source, proof and proof
edges; only `lean` and the added definition dependency change. No Git command or
direct edit was performed in either read-only checkout. The final delivery wrapper
rebases its temporary worktree on current `newtargets-dag`.

The statement is `CategoryTheory.coherent_nerve_comparison` in
`Sheaf.CategoryTheory.CoherentNerveComparison`, with proof exactly `by sorry`.
Its conclusion is `Nonempty CoherentNerveComparisonStatement.{u}`. Every field
now has an actual mathematical type. No field is a bare `Prop` or a function
whose result is an unconstrained `Prop`.

The source read is HTT §§1.1.5, 2.2.2, 2.2.4, 2.2.5 and §1.2.5, including
the project server, the project server and the project server, and Kerodon §3.3.6, particularly Example
the project server (discrete sets), Proposition the project server (finite products), and Propositions
the project server and the project server (weak equivalence and Kan replacement). The mapping formula
uses HTT's maximum-subset map `Q^n → Δ^n`, rather than selecting an arbitrary
weak equivalence between the two mapping sets.

Hypothesis and clause matching:

- Small simplicial categories: `CoherentNerve.SCat.{u}` is Mathlib's
  `EnrichedCat.{u, u+1, u} SSet.{u}`, with enriched functors as the arrows of its
  ordinary `sCatCategory`. The object set and every mapping simplex are in a
  common sufficiently large `u`. Every pair of smaller object/morphism universes
  embeds into such a common universe. No finite, inhabited, skeletal, or locally
  Kan restriction is placed on the input categories.
- Mapping sets, composition, identities and the component category: the existing
  `EnrichedCategory` data, `eId`, `eComp`, `ForgetEnrichment`, and
  `SimplicialCategory.homEquiv'` give these. The retained `PiZeroEquivalence`
  demands bijectivity of every `SSet.mapπ₀` and essential surjectivity with inverse
  equations in `SSet.π₀`. `DwyerKanEquivalence` adds the actual local weak homotopy
  equivalence predicate from the recorded enhancement dependency.
- The Bergner model structure: `BergnerModelData.model : ModelCategory SCat`
  imposes Mathlib's CM1--CM5, including two-out-of-three, retract closure of all
  three classes, the two diagonal lifting axioms and both factorizations.
  `complete` and `cocomplete` require all small limits and colimits, beyond the
  finite ones in Mathlib's model axioms. `weak_iff_dwyer_kan` identifies the
  actual model weak equivalences.
- Bergner fibrations: `fibrations_iff_local_kan_lifting` is an iff with
  `(∀ x y, SSet.modelCategoryQuillen.J.rlp (F.map x y)) ∧ HasPiZeroIsoLifting F`.
  The latter quantifies over a target isomorphism component with source `F x`,
  produces `x'`, an inverse component `g : x → x'`, an equality `F x' = y`,
  and equality of the transported image of `g` with the prescribed component.
  `IsPiZeroIso` states both inverse equations in components. Local horn lifting
  is the existing Mathlib class, including both one-dimensional horns.
- Cofibrations: `cofibrations_iff_left_lifting` is the diagonal lifting property
  against every actual Bergner fibration which is also a weak equivalence.
  The old `trivial` and `cofibrant` proposition parameters have been removed:
  these notions have their existing Mathlib meanings for this model structure,
  namely intersection with weak equivalences (`trivialCofibrations` and
  `trivialFibrations`) and the initial-map condition (`IsCofibrant`). There is
  no additional unconnected predicate that could replace these meanings.
- Replacement: `LocallyKanReplacement.R : SCat ⥤ SCat` and its natural
  `unit : 𝟭 SCat ⟶ R` give genuine functoriality and naturality. Each `R.obj A`
  has its own enrichment. `objects` identifies its object type with that of A,
  and `unit_objects` makes the unit the identity on those objects.
  `local_weak_equivalence` and `locally_kan` concern the new target mapping sets.
  In particular no Kan hypothesis is demanded of A itself.
- Discrete normalization: `CoherentNerve.IsDiscrete` tests bijectivity of the
  degeneracy map from vertices to every degree of each mapping set. It allows
  arbitrarily many vertices. `discrete_objects`, `discrete_unit` and
  `discrete_maps` fix the category, the unit and every enriched map between
  discrete categories. `HEq` expresses equality after the recorded type
  identifications, without choosing arbitrary identifications or automorphisms.
- Coherent simplices and operators: `CoherentNerve.nerveFunctor` uses the existing
  `SimplicialNerve (ForgetEnrichment SSet A)` in every degree, and maps an
  enriched simplex by postcomposition. Mathlib's `SimplicialThickening` uses
  precisely endpoint-containing subsets and union composition.
  `simplex_realization` and `simplex_maps` identify the rigidification on both
  objects and monotone maps; `colimit_extension` requires preservation of small
  colimits. Thus it is the simplex-colimit extension of this construction.
- Adjunction: `adjunction : rigidification ⊣ CoherentNerve.nerveFunctor` is the
  existing categorical adjunction type with natural Hom bijections, unit,
  counit and triangle equations.
- Joyal structure: `JoyalModelData.model` imposes the model axioms;
  `cofibrations_iff_mono`, `weak_iff_categorical` and
  `fibrant_iff_quasicategory` identify the three specified classes. The
  categorical-equivalence test uses restriction on the cores of full coherent
  functor objects into every quasicategory.
- Quillen equivalence: `left_quillen` preserves cofibrations and trivial
  cofibrations; `quillen_equivalence` is the adjoint-map weak-equivalence iff
  for each X and locally Kan A. Every Joyal object is cofibrant, so there is
  no extra cofibrancy hypothesis excluding an X.
- Derived identification: `derived_nerve_objects` is the equality
  `RN(A) = N(R A)` and `derived_nerve_maps` is equality on every map. The
  target `QCats` is the full ordinary category of quasicategories and all
  simplicial maps. `catInfinity_universal` localizes it at coherent functor
  equivalences using the already recorded whole coherent-functor universal
  property. `simplicial_localization_universal` does the same for actual
  Bergner weak equivalences. `derived_equivalence` is a coherent functor
  equivalence between these localizations. Its natural normalization is
  `q_sCat E ≃ N(derived_nerve) q_QCat`, including all simplices of naturality.
- Homotopy pushouts: `homotopy_pushout_preservation` quantifies over each
  coherent span and each specified universal cocone in the simplicial
  localization. It supplies a universal target cocone with exactly the image
  apex and image coherent transformation under the derived equivalence.
  It preserves the diagram and cocone, not just the equivalence class of an apex.
- Ordinary nerve: `discrete_nerve` gives the actual simplicial isomorphism;
  `discrete_nerve_objects` and `discrete_nerve_arrows` fix its value on every
  object and arrow in each simplex. The arrow is evaluation on the minimal
  endpoint-containing subset. `discrete_naturality` uses those same specified
  isomorphisms for every enriched functor, rather than new unrelated witnesses.
- Locally Kan nerve: `locally_kan_quasicategory` explicitly concludes the
  existing `SSet.Quasicategory (N A)` from `IsLocallyKan A`.
- Mapping spaces: `CoherentMappingComparison.comparison` is an actual
  simplicial map `A(x,y) → SSet.Enhanced.mappingSpace (N A) (vertex x) (vertex y)`.
  Its `weak_equivalence` has exactly the locally Kan hypothesis. Vertex maps
  are fixed by `vertex_eval` and `vertex_inverse`, so objects cannot be relabeled.
- Canonical comparison and coherent composition: `objects`, `initial_mapping`,
  `final_identity` and `final_mapping` fix the comparison on EVERY simplex:
  an enriched `(n+1)`-simplex has initial vertices x and final vertex y;
  initial maps are identities; a chain of endpoint-containing subsets is
  evaluated by σ at the monotone sequence of its maximal nonfinal elements.
  This is the HTT `Q^n → Δ^n` comparison under the coherent-nerve adjunction.
  These values are enriched functors, so their `map_comp`, `map_id` equations
  retain the composition coherences in every degree. `composition_naturality`
  additionally states the actual two-simplex witnessing the composite of the
  two corresponding edges. `CoherentMappingComparison.naturality` gives the
  equality of simplicial mapping-space maps for every enriched functor. It
  holds as an equality in every degree, not merely on components.
- Groupoid case: `groupoid_nerve_kan` assumes local Kan fibrancy and that EVERY
  arrow is invertible in `π₀`, and explicitly concludes `SSet.KanComplex (N A)`.
  The groupoid condition is imposed on components, not on strict ordinary arrows.

Dependency declarations read and used:

- `def-weil-pbc-simplicial-set`: the Mathlib match for `SSet`, degeneracies,
  subcomplexes and finiteness; the statement here uses `SSet`, standard simplices,
  operators, nerve and the existing coherent simplicial thickening.
- `def-cbc-enhanced-diagrams-cones`, module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `IsWeakHomotopyEquivalence`,
  `core`, `mappingSpace`, `mappingSpaceMap`, `IsFunctorEquivalence`,
  `AreNaturallyEquivalent`, `coconeCategory` and `IsColimiting`. Their signatures
  and definitions were opened, including the entire initial-face pinching.
- `def-coef-coherent-localization-interface`, module
  `Sheaf.CategoryTheory.FiniteReedyLocalization`: `largeNerve`, `Inverts`,
  `localDiagrams` and `IsLocalization`. This imports and uses its already
  recorded definitions only; it does not use the downstream finite-Reedy theorem
  and introduces no DAG cycle.
- Mathlib `EnrichedCat`, `EnrichedCategory`, `EnrichedFunctor`,
  `ForgetEnrichment`, `SimplicialCategory`, `SimplicialNerve`,
  `ModelCategory`, `HasLiftingProperty`, and `SSet.modelCategoryQuillen.J.rlp`.
- The currently recorded proof input
  `Sheaf.AlgebraicTopology.KanQuillenRightProper` is imported non-publicly.
  Other proof inputs lack recorded modules, so no speculative imports were made.

Edge cases checked: the empty category; empty mapping sets; a discrete mapping
set with TWO vertices (the previous subsingleton test fails this example);
ordinary categories with nonidentity arrows; `n=0` and the identity component;
a category whose mapping set is a non-Kan simplicial set (the replacement now
changes that mapping set); and a locally Kan one-object monoid with noninvertible
components (the final Kan conclusion still requires the groupoid hypothesis).
The maximum-subset formula is defined even at `n=0`: the nonfinal initial
endpoint supplies a maximum candidate. The universe lifts of finite ordinals
are explicitly `ULift.up.{u, 0}` throughout these formulas, including inside
heterogeneous equalities, so those equalities do not compare different lifts.

Searches actually run in this repair: msearch LeanSearch query “The category of
simplicial categories and the Bergner model structure” returned enrichment,
`SimplicialNerve` and ordinary quasicategory primitives; LeanFinder query
“A model category with coherent localization at its weak equivalences” returned
Mathlib's model and ordinary localization APIs; msearch grep
`EnrichedCat|QuillenEquivalence|Bergner` in `CategoryTheory` returned enrichment
and bicategory files, no Bergner or Quillen comparison. Their exact logged
results are in the new node. Direct `rg` over Mathlib, `WeilConjectures` and
`lean/Sheaf` found the existing coherent-localization helper and no normalized
replacement or Bergner statement. Blueprint searches for “Bergner” and
“coherent localization” found zero blueprint nodes; the ancestor search returned
`prop-coef-integral-exceptional-adjoint`. The whole DAG search found and reused
`def-coef-coherent-localization-interface`; it was not copied.

The module docstring and theorem proof docstring identify the source and the
stepwise proof route. All proofs remain postponed in the single named theorem;
new definitions have real data and the category/functor instances contain only
their actual structural equations. No statement correction or disputed statement
is needed. Both delivered modules were compiled separately in dependency order
through `scompile.py`; the dry run passed compilation and preflight, with the independent second reading
left to the second reader, as required by the delivery wrapper. A temporary
`#check` probe also verified that SCat, replacement, both model records, mapping
comparison and the complete statement each have exactly their one declared
universe parameter; the probe was removed from the sandbox afterward.

## New nodes

`def-coef-coherent-nerve-infrastructure`, module
`Sheaf.CategoryTheory.CoherentNerveInfrastructure`, defines the ordinary category
of Mathlib's bundled simplicial categories, the nerve functor, local Kan and
actual discrete predicates, the categorical-equivalence test, the ordinary
quasicategory category, the large-nerve map and normalized replacement data.
Its primary declaration is `CoherentNerve.LocallyKanReplacement`; all helpers
are listed in `lean.declarations`. The source is HTT §§1.1.5, 2.2.5 and Kerodon
§3.3.6. This is a specification of data, not a hidden replacement existence theorem.
It reuses Mathlib model axioms and the already recorded coherent-localization
interface. The searches above found no existing ordinary strict category plus
normalized replacement interface. The item gains just this new definition node
in `stmt_deps`; its two original dependencies are unchanged.

## Repair audit

1. Nine hollow comparison fields: replaced by the actual adjunction, Quillen
   criterion, coherent localization equivalence with normalization, universal
   cocone image, normalized ordinary-nerve isomorphisms, Quasicategory and Kan
   conclusions, canonical mapping-space maps and full naturality/formula data.
2. Unconstrained Bergner classes and model axioms: replaced by `ModelCategory`,
   the actual weak-equivalence iff, local horn plus equivalence-lifting iff,
   and cofibration iff against the actual trivial fibrations. Bare retract,
   factorization, triviality and cofibrancy propositions are gone.
3. False replacement and inadequate normalization: replaced by a functor into
   new enriched categories and a natural unit, with unchanged object sets,
   new Kan mapping sets and local weak equivalences. Discrete normalization
   covers every degree, the entire category, its unit and all its maps.

The former report's second-reading paragraphs certified the returned version,
including its invalid endofunctor description. They have been removed rather
than presented as a review of these repaired files. This repair is to be read
independently by the second worker; this worker has not written that reading.

## Validation

`deliver2.py NZ lem-coef-coherent-nerve-comparison --no-push` printed OK
for the repaired packet. Both delivered modules compile cleanly. The only
remaining preflight item is the independent second reading, which the wrapper
explicitly assigns to the second reader. No delivery was pushed.

## Second reading by NZ

I read the node statement, its HTT source places (the project server, the project server,
the project server, the project server, the project server and the project server), the infrastructure node, and both
Lean files independently. The item-by-item list is as follows.

- The input is an arbitrary small simplicial category in a fixed sufficiently
  large universe. `CoherentNerve.SCat` is the bundled `EnrichedCat` over
  `SSet`; its existing enrichment supplies objects, mapping simplicial sets,
  units and associative composition. No finiteness, nonemptiness, skeletal,
  or local-Kan hypothesis is added.
- The component category and Dwyer--Kan equivalence are rendered by
  `CoherentNerve.underlying`, `PiZeroEquivalence`, and
  `DwyerKanEquivalence`. The latter has a weak homotopy equivalence on every
  mapping set and bijective component maps plus the explicit inverse equations.
  Thus the empty category and empty mapping sets remain allowed.
- `BergnerModelData` introduces one model category, all small limits and
  colimits, and iff characterizations of weak equivalences, fibrations and
  cofibrations. `HasPiZeroIsoLifting` is the source-object/equality-on-
  components lifting clause, while the mapping condition is the full
  Kan--Quillen horn lifting property. Cofibrations lift against maps that are
  both characterized fibrations and characterized weak equivalences, exactly
  the node's trivial-fibration condition. There are no independent tautological
  `trivial` or `cofibrant` predicates.
- `LocallyKanReplacement` supplies a functor, natural unit, unchanged object
  types, local weak equivalences, locally Kan targets, and discrete-category,
  unit, and map normalization. It does not assume the input is locally Kan;
  its object and map equalities use `HEq`, so the empty and discrete cases are
  included.
- The simplex thickening used by Mathlib has endpoint-containing subset paths
  and union composition. `rigidification`, `simplex_realization`,
  `simplex_maps`, and `colimit_extension` state the prescribed simplex
  construction, operators, and colimit extension. `adjunction` is the actual
  categorical adjunction. The Joyal model data gives model axioms,
  monomorphism cofibrations, categorical weak equivalences, and precisely the
  quasicategory fibrant objects. `left_quillen` and `quillen_equivalence`
  state the two Quillen claims with the standard cofibrant-source/fibrant-
  target criterion; every simplicial set is cofibrant.
- `vertex`, its evaluation and inverse equations, `discrete_nerve`, its
  object and arrow formulas, and `discrete_naturality` cover ordinary nerves
  on all degrees and all arrows. The formulas are meaningful at `n = 0` and
  do not collapse a discrete category with two or more objects.
- `locally_kan_quasicategory` gives the node's quasicategory conclusion.
  `CoherentMappingComparison` gives an actual map of mapping simplicial sets,
  its locally-Kan weak equivalence, all vertex values, initial identities,
  final identity, the maximum-subset formula on every simplex, and naturality.
  `composition_naturality` supplies the required two-simplex for composites.
  These are stronger data specifying the canonical comparison, rather than an
  arbitrary weak equivalence.
- `groupoid_nerve_kan` assumes local Kan mapping sets and invertibility of
  every arrow in the component category, then concludes a Kan coherent nerve;
  it does not impose strict invertibility of ordinary arrows.
- `derived_nerve`, its object and map equations, the two enlarged localized
  simplicial sets, both `IsLocalization` universal properties,
  `derived_identification`, its functor-equivalence assertion, and the
  normalization identify the derived nerve with the localization comparison.
  `homotopy_pushout_preservation` quantifies over a span and a specified
  colimiting cocone and preserves its apex, transformation, and colimiting
  property. This is the node's pushout clause, rather than only an assertion
  about an equivalence class.

I found no mismatch between the node and the Lean signature. The only issue
encountered was procedural: the first dry run correctly rejected the report
because this independent section was absent; no Lean or node repair was
needed. I added this section and retained the worker's modules unchanged.

Edge cases checked again were the empty simplicial category, empty mapping
sets, a discrete category with two objects, `n = 0`, identity components,
non-Kan mapping sets requiring replacement, and a locally Kan one-object
category whose component monoid has a noninvertible arrow. Universes are fixed
at the common `u` with the enrichment universe `u + 1`, and all finite-order
lifts in the formulas are explicit.

Searches were repeated with `msearch.py` LeanSearch, LeanFinder, and grep for
`EnrichedCat|SimplicialNerve|Bergner|QuillenEquivalence` in Mathlib and
`WeilConjectures`, plus `rg` over `lean/Sheaf` and the DAG. Mathlib provides
the simplicial thickening/nerve and model-category primitives, but no Bergner
model structure, normalized locally-Kan replacement, or complete comparison
statement. The infrastructure notion is therefore genuinely new and is cited
as `def-coef-coherent-nerve-infrastructure`; the other two dependencies use
their recorded declarations exactly.

## Maintainer fix (independent review, 2026-10-17)

`homotopy_pushout_preservation` was replaced. The delivered field only said that the
infinity-equivalence `derived_identification` carries universal infinity-cocones in the
localization of `SCat` to universal cocones. This follows from `derived_equivalence`, and it
never mentions a model homotopy pushout in `SCat`. The node, its proof step 11, and the citer
`lem-coef-hammock-infinity-localization` (step 4) say more: a model homotopy pushout of
simplicial categories becomes a pushout in `Cat∞` under the derived nerve. Here a model
homotopy pushout is a cocone whose comparison from the pushout of a projectively cofibrant
replacement is a weak equivalence, as in `lem-coef-model-colimit-localization-comparison`.

The field now quantifies over a strict span `D` in `SCat`, a cocone `c` on it, a span `D'`
with Bergner-cofibrant apex and cofibrant legs (the projective cofibrancy of a span), an
objectwise Bergner weak equivalence `r : D' ⟶ D`, and a colimit `c'` of `D'` whose comparison
`hc'.desc ((Cocone.precompose r).obj c)` is a weak equivalence. Its conclusion is
`FiniteReedy.IsColimitEdge` for the image of `D`, the apex `c.pt` and the cocone transformation
`c.ι` under `largeNerveMap derived_nerve ≫ qcat_localization`, which is `RN_hc` followed by the
localization of quasicategories. These are the recorded `def-coef-coherent-localization-interface`
declarations, imported through `def-coef-coherent-nerve-infrastructure`. The cocone's maps are
kept as well as its apex. The theorem docstring's step (6) now gives this route. The
signature of `coherent_nerve_comparison` and every node record are unchanged.
