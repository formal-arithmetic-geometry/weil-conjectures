## Worker report

The module `Sheaf.CategoryTheory.SimplicialLocalizationExistence` states Kerodon
Proposition the project server (Tag 05ZP), read at https://kerodon.net/tag/05ZP on
2026-10-17. The source explicitly asserts existence, functoriality and commutation
with filtered colimits. The node statement is unchanged. The only postponed
proof is `SSet.Enhanced.exists_simplicial_localization`; it is `sorry` and its
docstring carries all eight DAG proof steps (the last two are combined).

`SimplicialLocalizationChoice` is a structure packaging the data and exact laws
already asserted by this node. It constructs no chosen localization, and there
is no definition obtained by choosing an undetermined object from a mere
existence theorem. No independent notion or new node is needed. In particular,
ordinary marked simplicial sets require degenerate edges to be marked; this
node permits arbitrary subsets W, including the empty subset. We therefore
bind W directly and do not impose a marking closure hypothesis.

Hypothesis and clause correspondence:

- Small simplicial sets and collections of edges are `C : SSet.{u}` and
  `W : Set (C _⦋1⦌)` in the structure. All output objects remain in `SSet.{u}`.
- A choice for every pair is the single existential `choice`, whose fields
  `L` and `F` are indexed by C and W. The choice is outside the quantification
  over all filtered diagrams.
- Quasicategory and localization clauses are `isQuasicategory` and
  `isLocalization`. The latter is the recorded `IsLocalizationAtEdges.{u,v}`,
  testing against every target in `SSet.{max u v}`, without assuming that C
  is itself a quasicategory. Universe v is explicit and unrestricted.
- A simplicial map a preserving W is the argument of `choice.map`, with
  `∀ w, w ∈ W → a.app _ w ∈ W'`. The preservation witness is a proposition,
  so proof irrelevance prevents any extra choice of action on witnesses.
- The commuting square L(a) F = F' a is `map_F` in Lean's left-to-right
  composition order. Strict identity and composition are `map_id` and
  `map_comp`, equalities of the actual simplicial maps.
- The index category is `(I : Type u) [SmallCategory I] [IsFiltered I]`;
  Mathlib's IsFiltered includes nonemptiness and is equivalent to existence
  of cocones on all finite diagrams. No injectivity of transitions is assumed.
- The strict diagram of pairs is `D`, `W`, `hW`. Functor D supplies all
  simplicial identity and composition laws, and hW is precisely preservation
  of the specified edge subsets on every transition.
- The resulting localized diagram is `K`, with objectwise isomorphisms `e`.
  Its first equation identifies EVERY transition with `choice.map (D.map f)`.
  This is a presentation of the strictly induced diagram, allowing the
  harmless transport of its objects along explicit isomorphisms. It is not
  an arbitrary unconnected diagram. Taking K.obj i literally equal to L_i
  makes e identities; conversely e transports the entire diagram to that one.
- C is `colimit D`. Simplicial colimits are the existing Mathlib pointwise
  presheaf colimits. The exact union marking is
  `⋃ i, (colimit.ι D i).app (op ⦋1⦌) '' W i`.
- The comparison is `r : colimit K ⟶ choice.L (colimit D) Wcolim` and
  `IsIso r` asserts an isomorphism of simplicial sets. The equation for every
  `colimit.ι K i ≫ r` characterizes the actual canonical comparison induced
  by the colimit structure maps; it is not merely some isomorphism.
- q is the colimit of the F_i, specified by its equation after EVERY
  `colimit.ι D i`. The final `q ≫ r = choice.F ...` says that the comparison
  carries the colimit universal maps to F for the colimit pair.

Dependencies read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: Mathlib `SSet`, internal hom,
  quasicategory, and `SSet.Enhanced.IsFunctorEquivalence` (its full definition
  uses a quasi-inverse and two coherent natural equivalences).
- `Sheaf.CategoryTheory.UniversallyLocalizingSimplicialMap`:
  `SSet.Enhanced.IsLocalizationAtEdges`, with its actual restriction-map
  factorization into `edgeInvertingDiagrams` and coherent inverse property.
  The module and complete signature and docstring were read.
- Proof-only imports: `Sheaf.AlgebraicTopology.JoyalModelStructure`,
  `SSet.exists_joyal_model_structure`, and
  `Sheaf.AlgebraicTopology.JoyalFunctorEquivalenceTest`,
  `SSet.joyal_functor_equivalence_test`; signatures and proof docstrings read.
  The two other proof prerequisites (edge-inversion pushout and filtered
  inner-horn factorization) currently have no recorded Lean module, so no
  import is invented for them; they remain explicitly cited in the proof plan.
- Mathlib `CategoryTheory.Filtered.Basic` and
  `CategoryTheory.Limits.FunctorCategory.Basic` supply the index convention
  and existing simplicial colimit infrastructure.

Edge cases checked: C empty, W empty, W all edges, and C a point with W empty
or containing its degenerate edge are all admitted, without nonemptiness
assumptions on C or W. No quasicategory assumption on input is added. A
one-object identity indexing diagram specializes to the same pair and the
comparison of its identity colimit. Arbitrary noninjective transitions and
identifications of distinct marked edges remain allowed; the union marking
uses images rather than an injective-union construction. An empty index is
excluded exactly by IsFiltered. Both the input and output universes remain u;
only localization tests enlarge to max u v.

Searches performed afresh through msearch.py:

- LeanFinder: `Functorial simplicial localization at marked edges preserving
  filtered colimits` returned 8 ordinary category/model-category localization
  hits, including `CategoryTheory.Functor.q_isLocalization` and
  `CategoryTheory.LocalizerMorphism.localizedFunctor`. Their objects are
  ordinary categories, not the asserted quasicategorical construction.
- Loogle: `"SSet", "localization"` returned zero hits.
- Mathlib grep: `MarkedSSet|MarkedSimplicial|localization.*filtered|filtered.*localization`
  restricted to AlgebraicTopology returned zero hits.
- LeanSearch: `Functorial simplicial localization of a simplicial set at
  selected edges preserves filtered colimits` returned general preservation
  predicates and accessibility implications, including
  `CategoryTheory.Limits.PreservesFilteredColimits`; no localization construction.
- Mathlib grep: `SimplicialLocalizationChoice|exists_simplicial_localization`
  returned zero hits.
- rg of the source WeilConjectures tree for the item id, localization with
  filtered colimits, and the proposed declaration names found no match.
- rg of the side library found hammock/simplicial-category comparison
  constructions and `LocalizationFilteredColimit.lean`. The latter is the
  downstream theorem for colimits of already-given localizations and uses
  this item in its proof, so is not this existence statement. The proposed
  declaration names do not occur in the side library or upstream name index.

No STATEMENT-DISPUTED issue, correction, dependency repair, or new node.
The final module compiled cleanly using the prescribed scompile.py wrapper,
including both its sandbox and library-module forms. No global build was run.

## Second reading by Q71

No second reading by a worker: under the 2026-10-17 direct-delivery procedure,
the maintainer supplies the independent review. The worker's clause check above
records the representation of K, the canonical comparison equations and all
edge cases for that review. The initial draft was replaced before delivery;
the final statement asserts existence of the comparison and IsIso, with all
structural-map equations as conclusions.
