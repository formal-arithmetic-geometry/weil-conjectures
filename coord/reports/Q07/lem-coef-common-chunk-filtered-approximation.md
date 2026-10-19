## Worker report

Item: `lem-coef-common-chunk-filtered-approximation`, group Q07, stage 2,
2026-10-17 UTC. Module:
`lean/Sheaf/CategoryTheory/CommonChunkFilteredApproximation.lean`.
Main declaration:
`CategoryTheory.CommonChunkApproximation.common_chunk_filtered_approximation`.
The only postponed theorem is this declaration, with proof `sorry`. Its docstring
carries all fourteen proof steps and their prerequisite node names. Every helper
is a concrete definition or a structure expressing an inline clause of this item;
no helper theorem, axiom, hollow construction, or independent new notion is added.

The source was opened online: Lurie, HTT,
https://people.math.harvard.edu/~lurie/papers/HTT.pdf,
Definition A.3.4.1 (printed p.885), Lemma A.3.4.15 and proof (pp.890–891),
and Corollary A.3.6.18 and proof (p.905). In particular the latter proof chooses a
small regular cardinal depending on the shape and the enriching model, invariant
under universe enlargement, and then takes a filtered union of common chunks.

### Hypotheses and clauses, individually

1. The two universes are `u` and `max u w`. `M : Type w` has `Category.{u}` and
   `SimplicialCategory` mapping sets in the small universe. All simplicial index
   categories are `SCat.{u}`, and their family index is `A : Type u`. The poset of
   subcategories is `Λ : Type (max u w)`. No equality of the small and ambient
   universe is imposed.
2. The combinatorial simplicial model category hypotheses are exactly
   `[ModelCategory M]`, `T : SimplicialTensorCotensor M`,
   `CombinatorialModelCategory.{w,u,u} M`, and
   `SimplicialModelLocalization.SatisfiesSM7 M`, using the recorded dependency
   notions. The underlying ordinary category and enrichment are compatible via
   the existing `SimplicialCategory` interface.
3. Small cofibrant simplicial index categories are `I : A → SCat.{u}` with
   `IsCofibrant (I a)` for the characterized Bergner model `B₀`. The supplied
   finite-colimit structure is `B₀.model.cm1b.out`; it supplies the empty colimit
   needed by Mathlib's initial-map definition of cofibrancy, not an extra
   mathematical hypothesis.
4. A chunk is the existing `CategoryTheory.SimplicialChunk M`, never a private
   replacement. Its `carrier` is an `ObjectProperty`, hence denotes a full
   simplicial subcategory. Its `product_factorization n` and
   `coproduct_factorization n` give exactly the finite fan/cofan factorizations,
   actual enriched middle-object functors, the required four model classes,
   middle-object membership, and enriched naturality equations. They quantify
   over every `n : ℕ`, including zero. Ambient finite products/coproducts need not
   lie in the carrier.
5. An I-chunk is precisely the landed `CategoryTheory.IsIChunk`: the ambient
   chunk plus a chunk in the supplied projective diagram model, whose carrier
   consists of diagrams with every value in the ambient carrier. We use the
   dependency's genuine `SimplicialDiagramEnrichment`, with enriched end mapping
   sets and genuine enriched natural transformations, and its
   `ProjectiveSimplicialModelStructure`.
6. The fixed small partially ordered set is `(K : Type u) [PartialOrder K]`.
   The theorem first chooses `κ : Cardinal.{u}` and `Fact κ.IsRegular`. Mathlib's
   `Cardinal.IsRegular` includes infinitude. This quantifier precedes *all*
   choices of model category, index family, Bergner-model data, and localization
   system. Thus the bound is independent of M and the I-family.
7. The same `κ` is used in `HomotopyLimitClosure.{u,u}` and
   `HomotopyLimitClosure.{u,w}`: closure is asserted simultaneously in the small
   universe and the independently enlarged ambient universe. The statement is
   universe-polymorphic in `w`. It uses Bergner-derived limits directly and does
   not use an infinity-category interpretation of simplicial categories.
8. `Approximation` quantifies over every `μ : Cardinal.{u}` with
   `[Fact μ.IsRegular]` and `κ ≤ μ`. It supplies a `PartialOrder Λ` and
   `IsCardinalFiltered Λ μ`. For a poset this is Mathlib's documented equivalent
   of every subcollection of cardinality below μ having an upper bound.
   Taking μ = κ gives the κ-filtered clause. Filteredness includes nonemptiness.
9. `U : Λ → SimplicialChunk M`, with
   `l ≤ m ↔ (U l).carrier ≤ (U m).carrier`, makes this an actual collection of
   subcategories ordered by inclusion. Antisymmetry excludes duplicate indices
   for equal carriers. `ObjectProperty.Small.{u} (U l).carrier` is exactly
   smallness of each full subcategory's object set; mapping simplicial sets
   already lie in u. `∀ X : M, ∃ l, (U l).carrier X` says the union is all of M.
10. For every a and its projective model, `∀ l, IsIChunk (U l) ...` makes every
    member a common I_a-chunk. Quantifying over the dependency's representations
    E and P does not change the mathematical property: their enriched mapping
    object is the represented enriched end, and the projective model classes
    are characterized objectwise, so different presentations are canonically
    isomorphic. Their existence is already asserted by the recorded projective
    calculus theorem.
11. `diagramPair T E (U l).carrier` is literally the full relative subcategory
    of `fibrantPair E.Diagrams` consisting of diagrams valued in U_l. The latter
    records ambient projective fibrant objects and actual ambient weak
    equivalences. Their projective characterization is objectwise. `subpair`
    uses the inherited full mapping simplicial sets, and its marking is exactly
    the ambient marking evaluated on the included vertex arrow. Thus no other
    distinguished maps or bifibrancy hypotheses are substituted.
12. `LocalizedDiagram.objects` fixes every diagram object to that exact pair;
    `legs` fixes its augmentation to `diagramInclusion`, whose object map is
    inclusion and whose enriched mapping map is identity. Augmentation
    naturality then forces transition maps to be the actual full inclusions.
    `cocone` and `isColimit` supply the colimit of this diagram after applying
    the existing functorial enriched localization system L. The displayed
    comparison is `isColimit.desc (localizedAugmentation L augmentation)`,
    where `localizedAugmentation` applies L to those inclusion legs. Its
    `equivalence` field asserts `DwyerKanEquivalence` for this canonical map.
    No arbitrary map or mere unspecified equivalent target is used. L is
    supplied with its dependency's derived-pushout presentations; no localization
    object is chosen from an unproved existence theorem.
13. `RestrictionNaturality` quantifies over every enriched `v : I a ⟶ I b`.
    It supplies an actual enriched functor R on the projective diagram
    categories, fixes its objects to enriched precomposition, and fixes its
    maps by the end projections to those at `v.obj i`. It asserts preservation
    of fibrant objects and their weak equivalences. The stage transformation τ
    satisfies the square with the full augmentations and `fibrantMap R hF hW`;
    hence its stage maps are restrictions of this same R. Finally it states the
    square of the canonical colimit comparisons using colimit descent. It does
    not demand preservation of cofibrant or bifibrant diagrams, nor require v
    to be a DK equivalence.
14. In `HomotopyLimitClosure`, `H : Λ ⥤ (Kᵒᵖ ⥤ SCat)` is the family of
    diagrams, `Z : Λ ⥤ SCat` its vertices, and `η : Z ⋙ const Kᵒᵖ ⟶ H` its
    compatible cones. Every stage cone is tested by the dependency's
    `IsDerivedLimit` for the actual Bergner weak-equivalence/cofibration classes.
    A cocone h is required to be a colimit at every k, and z is a colimit of Z.
    The conclusion supplies the induced cone with vertex exactly `z.pt`, with
    the leg equations relating η, h and z, and asserts `IsDerivedLimit` for it.
    Thus both the diagram and vertex colimits are pointwise ordinary colimits,
    and the output is a homotopy-limit cone, as required. No chosen fibrant
    replacement or arbitrary comparison morphism is substituted in the statement.

### Dependency declarations read and used

- `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`:
  `CategoryTheory.SimplicialDiagramEnrichment` (including `Diagrams`, `value`
  and the end `projection`), `ProjectiveSimplicialModelStructure`, and
  `simplicial_projective_model_calculus`. Its signature and helper docstrings
  were read in the shared source. Model hypotheses use its imported canonical
  `HomotopicalAlgebra.CombinatorialModelCategory`,
  `SimplicialTensorCotensor`, and
  `SimplicialModelLocalization.SatisfiesSM7`.
- `Sheaf.CategoryTheory.SimplicialLocalizationComparisonCalculus`:
  `CategoryTheory.SimplicialLocalizationCalculus.Pair`, `PairHom`,
  `LocalizationSystem`, `IsDerivedLimit`, `fibrantPair`,
  `PreservesFibrantWeakEquivalences`, `fibrantMap`, and the recorded
  `simplicial_localization_comparison_calculus`. The signatures and docstrings
  fix localization as functorial derived pushout and derived limit through
  injectively fibrant replacement.
- `Sheaf.CategoryTheory.SimplicialSmallChunks`:
  `CategoryTheory.SimplicialChunk`, `IsIChunk`, and their fan/cofan factorization
  structures. Its node and whole module were read. Only its definition interface is reused to render the chunk notions given
  inline in this item. Its theorem node is not a mathematical prerequisite: the
  first server dry run confirmed that adding that edge creates a cycle back to
  this item. The chunk existence theorem is not an assumption. No dependency is
  repaired or redefined.
- `Sheaf.CategoryTheory.CoherentNerveComparison` and
  `CoherentNerveInfrastructure`, publicly visible through dependencies:
  `SCat`, `underlying`, `BergnerModelData`, `DwyerKanEquivalence`. We use only
  these explicit enriched-category/model definitions, not the coherent-nerve
  comparison theorem. `BergnerModelData` characterizes all model classes.
- Mathlib `CategoryTheory.IsCardinalFiltered`, `ObjectProperty.Small`,
  `FullSubcategory`, enriched functors, cones, cocones, `IsColimit.desc`, and
  `Functor.whiskerRight` render the categorical clauses directly.

Every stated proof prerequisite is imported with a non-public import. The two
proof-only nodes `lem-coef-combinatorial-injective-diagram-model` and
`lem-coef-scat-diagram-factorization-uniform-bound` have no Lean record on the
read base, so there is no module to import for them; they remain explicit proof
steps in the docstring, not new statement assumptions. Mathlib proof leaves use
`Limits.Types.Filtered`, `Cardinal.HasCardinalLT`, and `Order.RelClasses`.

### Edge cases checked

- Empty family A: there are still ambient chunks U_l, smallness, filteredness,
  and coverage; only the common-index and restriction clauses become vacuous.
- Empty I_a: the unique empty diagram satisfies the all-values predicate; its
  fibrant diagram category and localization are still present. No nonempty
  index hypothesis is imposed.
- Empty K: compatible cones are cones over the empty diagram. The statement
  still tests their derived terminal property and its filtered-colimit closure.
- Empty finite fan/cofan: the reused definitions include n = 0. They impose
  replacements on the distinguished object, not membership of the ambient
  initial/terminal object itself.
- Empty chunk carriers are permitted when mathematically possible. Coverage
  requires each actual object at some stage, without requiring each chunk to
  be nonempty. The filtered indexing poset itself is nonempty.
- κ = ℵ₀ and μ = κ remain expressible; regularity already includes infinitude.
  There is no countability assumption on the family or shape.
- Enriched restriction maps may identify objects and need not be DK
  equivalences. All naturality is for actual restriction on fibrant diagrams.
- Ambient universe w is independent of u; small carriers use `Small.{u}`, and
  the full categories and indexing collection use `max u w`.

### Searches and checks

Prescribed `msearch.py Q07 lem-coef-common-chunk-filtered-approximation` searches:

- leanfinder: `common chunks of simplicial model categories and filtered colimits
  of Dwyer Kan homotopy limit cones`: eight unrelated model-category axioms,
  cylinder/path-object existence and Kan-model instance hits; no exact statement.
- loogle: `SimplicialCategory, IsFiltered`: zero hits; service reports unknown
  identifier SimplicialCategory. No match claimed from that query.
- grep in Mathlib CategoryTheory: `Chunk|chunk|IsCardinalFiltered`: found the
  standard cardinal-filtered API, but no simplicial chunk or DK approximation.
- leansearch: `Common small chunks in simplicial model categories give filtered
  colimits of enriched localizations and homotopy limit cones`: eight hits,
  including ordinary `Limits.colimitLimitIso` for filtered colimits and finite
  limits and existence of filtered colimits for complexes; none concerns enriched
  localization, chunks, or Bergner-derived limits of arbitrary fixed small shape.
- `rg` over upstream WeilConjectures and shared lean/Sheaf for
  `Chunk|chunk|common_chunk|filtered.*homotopy.*limit`: found the already landed
  SimplicialSmallChunks module and uses in EnrichedDiagramRectification. Read
  and reused the former; neither states this filtered approximation/closure.
- The prescribed upstream node-id grep found no existing declaration. Exact
  searches for the new theorem/helper names found no collisions. No repair
  note for this item was present.

Validation: prescribed scompile.py compiled both the sandbox and library-named
file cleanly (2.8 s and 3.5 s), with no warning. All universe variables and
parameters are explicitly bound, all Lean lines are at most 100 characters,
there is one sorry, and the node's recorded signature is copied verbatim from
the theorem. The required deliver2.py --no-push dry run is run after this report.

No STATEMENT-DISPUTED flag or statement correction is needed. The item's only
change is `lean`. There are no new nodes or dependency modules. The initial dry
run rejected the proposed extra theorem dependency because it creates a cycle;
that edge was removed, retaining the existing definition interface for the
notions explicitly defined inline in this item. This follows the same
definition-interface treatment documented in the recorded projective-calculus
dependency. The first dry run also required a nonempty second-reading section,
so the section below explicitly records its pending state without claiming an
independent review.

## Second reading by Q07

I independently reread the node statement, its source place, the two recorded statement
 dependencies, and the complete Lean module. The item has no `statement_change`, and the
sandbox node copy is unchanged from the base node.

### Object and hypothesis matching

1. The node fixes universes \(\mathcal U\in\mathcal U'\), a model category \(\mathcal M\),
   a small family \((I_a)_{a\in A}\), and a small poset \(K_0\). Lean renders these as
   `u`, `w`, `M : Type w` with `Category.{u} M`, `A : Type u`, `I : A → SCat.{u}`,
   `K : Type u` with `[PartialOrder K]`. No universe equality is imposed.
2. The node's combinatorial simplicial, tensor-cotensor, and SM7 assumptions are the
   binders `T`, `CombinatorialModelCategory.{w,u,u} M →`, and
   `SimplicialModelLocalization.SatisfiesSM7 M →` in `Approximation`; the exact
   dependency interfaces were read and match the node.
3. The cofibrancy hypothesis for every `I a` is exactly the recorded Bergner-model
   `IsCofibrant` predicate, with `B₀.model.cm1b.out (Discrete PEmpty)` supplying the
   empty colimit. There is no added local Kan or nonemptiness assumption.
4. A chunk is the existing `SimplicialChunk M`; `SimplicialChunk.carrier` is an
   `ObjectProperty` (hence full), and its two factorization fields quantify every
   `n : ℕ`, including `n = 0`. `IsIChunk` is the recorded projective-diagram chunk
   notion; no private duplicate is introduced.
5. The arbitrary regular bound is `∃ κ, Fact κ.IsRegular`, before all model and family
   choices. `HomotopyLimitClosure` is asserted for both `BergnerModelData.{u}` and
   `BergnerModelData.{max u w}`, giving the required universe-enlargement invariance.
6. For every regular `μ` with `κ ≤ μ`, `Approximation` supplies a `PartialOrder Λ`,
   `IsCardinalFiltered Λ μ`, an order embedding by carrier inclusion, small carriers,
   and coverage `∀ X : M, ∃ l, (U l).carrier X`. Filteredness therefore includes the
   required nonempty/connected cases.
7. The common-chunk clause is `∀ a E P, (∀ l, IsIChunk ...) ∧
   Nonempty (LocalizedDiagram T E L U)`. `LocalizedDiagram` fixes each stage object
   definitionally to `diagramPair`, whose property is exactly “every diagram value lies
   in the carrier”, and fixes each augmentation leg to `diagramInclusion`.
8. `LocalizedDiagram.cocone`, `.isColimit`, and `.equivalence` give the canonical
   colimit and its `isColimit.desc (localizedAugmentation ...)` Dwyer--Kan equivalence;
   the map is induced by the actual full inclusions. `RestrictionNaturality` quantifies
   over every enriched `v : I a ⟶ I b`, fixes `R` on values and end projections to actual
   precomposition, preserves fibrancy and weak equivalences, and states the square for
   the canonical colimit comparisons. It does not add cofibrancy or DK-equivalence
   hypotheses on `v`.
9. `HomotopyLimitClosure` quantifies over every filtered `Λ`, diagram `H`, vertex
   diagram `Z`, compatible cone `η`, stage `IsDerivedLimit` cones, pointwise colimit
   cocone `h`, and colimit cocone `z`. Its conclusion supplies the exact vertex `z.pt`,
   leg equations, and `IsDerivedLimit` for the induced cone. Quantifier order and all
   conclusion clauses match the node.

### Edge cases and definition checks

The empty family `A`, empty index categories `I a`, empty shape `K`, empty finite fan or
cofan (`n = 0`), empty chunk carriers, and `κ = ℵ₀`/`μ = κ` are all expressible. The
recorded `SimplicialChunk` zero-ary factorizations handle the empty fan/cofan without
requiring ambient initial or terminal objects in a carrier. `IsCardinalFiltered` supplies
nonemptiness of the indexing poset. The ambient universe `w` remains independent of `u`.

I searched Mathlib, the shared `lean/Sheaf`, and the upstream `WeilConjectures` tree with
`rg` for `Chunk`, `IsIChunk`, `common_chunk`, and filtered homotopy-limit variants. I also
ran the prescribed `msearch.py` searches: LeanFinder returned only unrelated Dold--Kan
hits, Loogle returned zero hits (unknown `SimplicialChunk`), grep returned zero exact
matches, and LeanSearch returned only ordinary filtered-colimit/finite-limit results.
The two dependency modules were opened and their declarations match the interfaces used
here. No existing declaration or repair note applies, and no dependency module or new
node is needed.

### Mismatches and repairs

No statement, object, hypothesis, quantifier, conclusion, universe, edge-case, or
canonical-map mismatch was found. I made no Lean-code change. I replaced the earlier
pending placeholder with this completed second reading, reran
`scompile.py` on the module (sandbox and library overlays both clean, one postponed
`sorry` only), and verified the node's `lean.statement` remains verbatim equal to the
 theorem signature.

## Maintainer review correction (reviewer, 2026-10-17)

The two sentences above that say adding `lem-coef-simplicial-small-chunks` to the item's
dependencies "creates a cycle back to this item" do not hold on the delivery base
80105427dffe or on the current DAG. `check_dag`-style reachability over stmt_deps, proof_deps
and step `uses` finds no path from `lem-coef-simplicial-small-chunks` to this item. The
edge stays out of `stmt_deps` for a different reason: the item states the chunk and I-chunk
notions inline, and stage 2 lets the item's `stmt_deps` change only by new definition nodes.
The module reuses only the definitions `SimplicialChunk` and `IsIChunk` (one definition per
notion), not that node's theorem. `lean.note` is corrected to match. The Lean is unchanged.
