## Worker report

The delivery states `SSet.SegalSpace.simplicial_local_equivalences_accessible` in
`Sheaf.AlgebraicTopology.SimplicialLocalEquivalencesAccessible`. Its only postponed
proof is this theorem's `sorry`. The full twelve-step natural-language proof from
the reviewed node appears in its docstring. The statement reuses
`SSet.SegalSpace.localAcyclicMonomorphisms` from the already published bounded-lifting
module; this is exactly the object class in the present node. It adds no definition.
Only the item's `lean` field changes; there are no new nodes, dependency repairs,
or statement corrections.

Hypotheses and clauses, in order:

| Node text | Lean rendering |
| --- | --- |
| One fixed universe of small sets | Explicit `universe u`, existing `SimplicialSpace.{u} = SimplexCategoryᵒᵖ ⥤ SSet.{u}`. Small cardinal, generator family, diagram objects and diagram morphisms all use `u`. The simplicial-space and arrow objects themselves naturally live in `Type (u+1)`. |
| The original Reedy structure and simplicial mapping sets | Imported recorded Reedy-cartesian and Kan--Quillen modules; the existing local-acyclic-monomorphism predicate uses `IsReedyFibrant` and `mappingSpacePre`, rather than a localized structure or a chosen replacement. |
| A monomorphism is injective in every bidegree | Literally `∀ n q : SimplexCategoryᵒᵖ, Function.Injective ((f.app n).app q)` in `_hf`; the reused subcategory predicate uses the equivalent `Mono a.hom`. In this bisimplicial presheaf category, applying `CategoryTheory.NatTrans.mono_iff_mono_app` twice and the type-category injectivity characterization gives exactly the bidegreewise condition. |
| Fix `f : P ↪ Q` | `{P Q : SimplicialSpace.{u}} (f : P ⟶ Q)` followed by the displayed injectivity hypothesis. No extra condition on `P`, `Q`, or `f`. |
| `Z` is local exactly if Reedy fibrant and `Map(Q,Z) → Map(P,Z)` is weak | The locality antecedent in the existing `localAcyclicMonomorphisms f a.hom` definition is exactly `IsReedyFibrant Z ∧ Enhanced.IsWeakHomotopyEquivalence (mappingSpacePre f Z)`. The weak predicate is the dependency's actual realization predicate: a component bijection and positive based homotopy-group bijections. |
| The full subcategory on monomorphisms `a : X → Y` with the weak mapping test for every local `Z` | `fun a : Arrow SimplicialSpace.{u} ↦ localAcyclicMonomorphisms f a.hom` reuses the exact existing predicate: `Mono a.hom ∧ ∀ Z, (IsReedyFibrant Z ∧ Enhanced.IsWeakHomotopyEquivalence (mappingSpacePre f Z)) → Enhanced.IsWeakHomotopyEquivalence (mappingSpacePre a.hom Z)`. No source or target fibrancy assumption is introduced. |
| Arrow objects, commuting-square morphisms, and endpoint colimits | Mathlib `Arrow` and `J ⥤ Arrow SimplicialSpace.{u}`; a `Cocone X` with `IsColimit c` is an ambient arrow-category colimit. The existing arrow-category colimit implementation computes its endpoints separately. |
| Replete | `ObjectProperty.IsClosedUnderIsomorphisms (fun a ↦ localAcyclicMonomorphisms f a.hom)` means membership transports along every arrow-category isomorphism. |
| Some infinite regular small cardinal | `∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular)`. Mathlib `Cardinal.IsRegular` includes `aleph0 ≤ κ`, so infinitude is present. |
| Closed under all small `κ`-filtered ambient colimits | For every `(J : Type u) [SmallCategory J] [IsCardinalFiltered J κ]`, diagram `X`, membership of all `X.obj j`, and arbitrary colimit cocone `c`, conclude membership of `c.pt`. The instances are quantified as explicit anonymous binders, as in the recorded generic accessibility interfaces. |
| `κ`-filtered means every diagram with fewer than `κ` morphisms has a cocone | Existing `IsCardinalFiltered J κ` tests `HasCardinalLT (Arrow A) κ`; `Arrow A` is exactly the type of all morphisms, with endpoints. |
| Regularity means unions of fewer than `κ` sets of size below `κ` have size below `κ` | Existing `Cardinal.IsRegular` is the equivalent infinite cofinality formulation; no alternate regularity predicate is introduced. |
| A small family of objects of this full subcategory generates under those colimits | `∃ (S : Type u) (G : S → Arrow SimplicialSpace.{u})`, membership for every `G s`, and for each member `a` an arbitrary small `κ`-filtered diagram `X` with each stage isomorphic to some `G s`, a colimit cocone, and `c.pt ≅ a`. By repleteness those stages are members. The diagram lies in the full subcategory because all commuting squares between members are allowed. Isomorphic representatives do not alter generation. |
| The cardinal depends only on `f` and the universe | The existential cardinal and the entire family occur immediately after the fixed `f` hypothesis, before the universal quantification over tested arrows or diagrams. |
| No localized model structure is assumed | There is no `ModelCategory SimplicialSpace` binder, witness, or use of a localization theorem. |

Dependency declarations read and used:

- `Sheaf.AlgebraicTopology.SimplicialSpaceReedyCartesian`:
  `SSet.SegalSpace.mappingSpace`, `mappingSpacePre`, `IsReedyCofibration`,
  `IsReedyWeakEquivalence`, and `reedy_cartesian_simplicial`.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.weakEquivalenceStructure` and `right_proper_kan_quillen`;
  weak equivalences remain `SSet.Enhanced.IsWeakHomotopyEquivalence` from
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`.
- `Sheaf.AlgebraicTopology.SegalCartesianExponent`, publicly provided by the
  Reedy-cartesian module: `SSet.SegalSpace.SimplicialSpace`, `IsReedyFibration`,
  `IsReedyFibrant`, `constant`, and `discreteRepresentable`.
- The already published `Sheaf.AlgebraicTopology.SimplicialLocalBoundedLifting`:
  `SSet.SegalSpace.localAcyclicMonomorphisms`, solely as a definition. Its full
  source signature, body and source docstring were read. This prevents a second
  definition of the monomorphic local equivalence class. Its downstream theorem
  `bounded_local_lifting` is neither used nor assumed. Adding that downstream node
  as a DAG dependency would close the existing proof cycle through bounded
  generation, so `stmt_deps` remains unchanged. Future reverse proof imports that
  would close a module cycle must be omitted under stage 2 rule 7; factoring out
  the existing definition into a prior module can also resolve that issue.
- Proof imports: `Sheaf.CategoryTheory.AccessibleSmallObjectFactorization`,
  `CategoryTheory.MorphismProperty.exists_accessible_functorial_factorization`;
  `Sheaf.CategoryTheory.SmallRightLiftingAccessibility`,
  `CategoryTheory.small_right_lifting_accessibility`;
  `Sheaf.CategoryTheory.AccessibleFullInverseImage`,
  `CategoryTheory.accessible_full_inverse_image`;
  `Sheaf.CategoryTheory.ReedyModelStructure`,
  `HomotopicalAlgebra.Reedy.model_structure`;
  `Sheaf.AlgebraicTopology.KanWhiteheadInverse`,
  `SSet.Enhanced.kan_whitehead_inverse`;
  `Sheaf.CategoryTheory.SimplicialHomotopyEquivalenceWeak`,
  `SSet.Enhanced.simplicial_homotopy_equivalence_weak`.
- Mathlib proof leaves: `CategoryTheory.MorphismProperty.llp_isStableUnderRetracts`,
  `rlp_isStableUnderRetracts`, `llp_isStableUnderCobaseChange`, `llp_isMultiplicative`
  in `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`;
  `CategoryTheory.MorphismProperty.isStableUnderTransfiniteCompositionOfShape_llp`
  in `Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting`;
  `CategoryTheory.Presheaf.instIsLocallyPresentableFunctorOppositeOfHasPullbacks`
  in `Mathlib.CategoryTheory.Presentable.Presheaf`;
  `CategoryTheory.Types.instIsLocallyPresentableType` in
  `Mathlib.CategoryTheory.Presentable.Type`; `CategoryTheory.yonedaEquiv`,
  `yonedaEquiv_naturality`, `yonedaEquiv_comp` in `Mathlib.CategoryTheory.Yoneda`.
  Each cited source and its full relevant signature was opened.

Source check: opened [Barwick's paper](https://webhomes.maths.ed.ac.uk/~cbarwick/papers/complete.pdf),
Lemmas 4.5--4.6 on printed page 43. These establish accessibility before localization
existence; the monomorphism intersection remains explicitly identified as the
node's agent-formulated specialization. The twelve-step node proof supplies that
additional argument. No assertion that this specialization is verbatim Barwick is made.

Edge cases checked before writing:

- `f = id`, including the identity on the empty space: locality reduces to the
  original Reedy fibrancy test and no nonemptiness condition appears.
- `f : ∅ → 1`: locality imposes its actual mapping-space test, without assuming
  pointedness, connectedness, or a preferred vertex.
- Empty sources and targets of tested arrows: the presheaf Mono condition handles all
  empty-domain cases. There is no independent surjectivity or inhabitedness clause.
- Disconnected local objects and mapping spaces are allowed by the realization
  component condition; no global basepoint is chosen.
- Degree zero and the empty zero-simplex boundary occur in the proof plan; no
  positive-degree restriction was introduced in the monomorphism hypothesis.
- A `κ`-filtered category is nonempty (the empty test diagram must have a cocone).
  Thus closure under an empty indexing diagram is not accidentally required.
  Small generating families themselves are allowed to be empty.
- `κ = aleph0` is permitted. Both the generator family and diagrams use the same
  small universe `u`; no independent smaller universe makes a test vacuous.

Searches for existing statements and notions (2026-10-17):

- `msearch.py ... leanfinder` query: “Monomorphisms of simplicial spaces that are
  homotopy local equivalences form a replete accessible subcategory of the arrow
  category”. Eight hits on Kan cofibrations and filtered-colimit stability of
  simplicial-set monomorphisms; none states this accessibility theorem.
- `msearch.py ... loogle` query:
  `CategoryTheory.IsAccessibleCategory, CategoryTheory.IsCardinalFiltered`:
  zero hits.
- `msearch.py ... leansearch` query: “Homotopy local equivalences of simplicial
  spaces form an accessible full subcategory closed under sufficiently filtered
  colimits”. Eight hits, including `MorphismProperty.isCardinalAccessible_ι_isLocal`
  and generic accessible-category APIs; none gives the homotopy-local equivalence
  statement. Mathlib's `isLocal` in OrthogonalReflection is strict Hom-set
  orthogonality, unlike the mapping-space weak-equivalence test here.
- `msearch.py ... grep` query
  `local.*equival.*accessib|accessib.*local.*equival`, subdirectory `CategoryTheory`:
  zero hits.
- `rg` on the source `WeilConjectures` and side `lean/Sheaf` with that expression
  and `localEquivalence|IsLocal.*Equivalence` found unrelated localizer-equivalence
  APIs; an additional locality-name search found the exact existing `IsLocalFor`
  and `localWeakEquivalences` definitions. A further file-name and predicate search
  found the exact `localAcyclicMonomorphisms` definition in
  `SimplicialLocalBoundedLifting`, which is now reused directly instead of adding
  any definition. No accessibility theorem
  for this monomorphism subcategory was found.
- `grep -rn` for the item id in upstream `WeilConjectures` found no occurrence;
  `rg` in `dag/lean_names_upstream.json` found no corresponding accessibility name.
- Exact-name collision search for `simplicial_local_equivalences_accessible` across Mathlib, upstream source, side
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no existing declaration.

Validation: `scompile.py NW lem-coef-simplicial-local-equivalences-accessible`
compiled the dependency overlay, the sandbox file, and the final module separately
with exit code 0 and no warnings. All universe and variable binders are explicit;
`autoImplicit` is false. No statement dispute or mathematical correction was needed.
The final delivery dry run is recorded below. The second reading is left to the
independent reader, as required.

## Second reading by NW

I read the node statement, the two recorded statement dependencies, the source place,
and the complete Lean signature. The item-by-item rendering is:

1. The fixed universe is `universe u`; `SimplicialSpace.{u}` is the existing
   `SimplexCategoryᵒᵖ ⥤ SSet.{u}` abbreviation. All simplicial spaces, arrows, test
   diagrams, generator families, and cardinals use this one universe.
2. The original Reedy model structure and mapping simplicial sets are supplied by
   `SimplicialSpaceReedyCartesian`; the theorem uses the existing
   `mappingSpacePre` through `localAcyclicMonomorphisms`, with no localized-model
   structure binder.
3. The node's bidegreewise monomorphism condition on the fixed `f : P ⟶ Q` is rendered
   exactly by `_hf : ∀ n q, Function.Injective ((f.app n).app q)`. The dependency theorem
   identifies this with categorical `Mono` in the bisimplicial presheaf category; no
   stronger condition is assumed.
4. The objects `P`, `Q`, and the fixed map `f` are explicit, with no assumptions on
   source, target, fibrancy, pointedness, or inhabitedness.
5. `f`-local objects are exactly the antecedent in the reused definition:
   `IsReedyFibrant Z ∧ Enhanced.IsWeakHomotopyEquivalence (mappingSpacePre f Z)`.
   The weak-equivalence predicate is the recorded realization-based one from
   `KanQuillenRightProper`.
6. The full subcategory is rendered by the object property
   `fun a : Arrow SimplicialSpace.{u} ↦ localAcyclicMonomorphisms f a.hom`.
   Unfolding the existing definition gives `Mono a.hom` and the required mapping
   weak-equivalence test for every `f`-local `Z`, with no extra fibrancy hypothesis.
7. `ObjectProperty.IsClosedUnderIsomorphisms` is exactly repleteness in the arrow
   category, whose objects and commuting-square morphisms are Mathlib `Arrow`s.
8. The conclusion quantifies `∃ κ : Cardinal.{u}, Fact κ.IsRegular`; Mathlib's
   `IsRegular` entails `aleph0 ≤ κ`, so this is the node's infinite regular small
   cardinal. The cardinal occurs before all tested arrows and depends only on `f`
   and `u`.
9. Closure is rendered for every `J : Type u` with explicit `SmallCategory J` and
   `IsCardinalFiltered J κ`, every diagram `X : J ⥤ Arrow ...`, every stage member,
   and every cocone together with `Nonempty (IsColimit c)`, concluding membership of
   `c.pt.hom`. This is ambient arrow-category colimit closure, hence componentwise
   source/target colimits.
10. The node's definition of κ-filtered is the dependency's
    `IsCardinalFiltered J κ`, which tests fewer than κ morphisms via `Arrow J`; the
    regularity convention is the existing cardinal regularity predicate, not a
    second local definition.
11. Small generation is rendered by `∃ (S : Type u) (G : S → Arrow ...)`, membership
    of every `G s`, and for every member `a` a κ-filtered diagram, colimit cocone,
    stagewise isomorphism to some `G s`, and `c.pt ≅ a`. Repleteness supplies the
    stage membership implicit in the node's wording.
12. The final clause has no localized model-structure assumption and no omitted
    quantifier or conclusion; all theorem proofs remain `sorry` as required.

Source check: Barwick, *On left and right model categories and left and right Bousfield
localizations*, Lemmas 4.5--4.6, printed p. 43, states accessibility of local objects
and local equivalences for an X-combinatorial model category. The node explicitly marks
the monomorphism intersection as its specialization; the Lean statement preserves that
specialization and does not claim Barwick proves the extra intersection verbatim.

Edge cases checked: identity and empty fixed maps (including `∅ → ∅` and `∅ → 1`),
empty tested sources or targets, zero and empty simplicial spaces, disconnected mapping
spaces, outer and inner degree zero, `κ = aleph0`, empty generating family, and the
nonempty requirement supplied by `IsCardinalFiltered`. No case is excluded by the
universe binders or by `_hf`; no basepoint, surjectivity, or positive-degree condition
was added.

Independent searches found no existing declaration: LeanFinder/LeanSearch and Loogle
queries for accessible homotopy-local equivalences of simplicial-space arrows returned
only generic accessibility, Kan, or monomorphism APIs; grep over Mathlib, upstream
`WeilConjectures`, side `lean/Sheaf`, and `dag/lean_names_upstream.json` found no
`simplicial_local_equivalences_accessible` or equivalent theorem. The existing
`localAcyclicMonomorphisms` definition was read and is reused, so no duplicate notion or
new node is needed.

Mismatch audit: none. In particular, the apparent difference between the node's phrase
“monomorphism” and `_hf` is intentional and exact because the node itself defines that
phrase as injectivity in every bidegree; categorical `Mono f` is not silently substituted.
The node copy and its `lean.statement` remain unchanged and verbatim. The sandbox module
compiled cleanly with the required `scompile.py` command (exit code 0, no warnings).
