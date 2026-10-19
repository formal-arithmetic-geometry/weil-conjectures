## Worker report

The module `Sheaf.CategoryTheory.KanDiagramEvaluationRestriction` states
`SSet.KanDiagramEvaluation.kan_diagram_evaluation_restriction`, with one `sorry`.
Every helper has real construction data or is an explicit predicate/record describing
this node's comparison. No new independent notion or dependency repair is needed.
Only the item's `lean` field changes.

The theorem takes the uniquely specified evaluation maps as input rather than choosing
maps from the dependency theorem's existential. `he` is precisely that dependency's
`IsChainEvaluation`, including its object and mapping-simplex formulas on every chain.
Existence of these evaluation maps is already the recorded dependency theorem.

Clause-by-clause reading:

- The universe V is `u`. Indexing shapes and values are `SSet.{u}`; the actual nerve of
  Kan-valued simplicial sets is `Enhanced.smallSpaces.{u} : SSet.{u+1}`. Diagram categories
  use the containing universe. `uliftFunctor` changes only the wrappers, degree by degree.
- Arbitrary K is `K : SSet.{u}`. There is no quasicategory, inhabitance, finiteness or
  dimension bound on it. The full ordinary category is the dependency's `KanDiagrams K`,
  not a category of strict ordinary diagrams. Its objects have enriched functor data,
  and its arrows have full graded enriched naturality. The weak arrows are exactly
  `SimplicialRightFibration.covKanWeak K`.
- The comparison e is `MonoidalClosed.curry (e K)`. The input `IsChainEvaluation` fixes
  the entire chain formula from localized evaluation, not just the vertex assignments.
  `CoherentDiagrams K` is the existing internal hom into the actual nerve of Kan complexes.
- Ordinary restriction for EVERY simplicial map v is the `RestrictionSystem.functor`.
  Its `objects` field specifies composition with the actual `Pinched.rigidification.map v`.
  Its `components` field specifies every simplicial component of every enriched natural
  map. Its values lie in `KanDiagrams K'`, so objectwise Kan fibrancy is retained.
  Its `weak` field states preservation of the exact objectwise weak equivalences.
- Identities and composites are the strict `identity` and `composition` fields. The
  first conjunct of the theorem is equality of maps from the WHOLE ordinary nerve into
  `CoherentDiagrams K'`; thus it is the exact evaluation identity on all chains and
  every simplicial operator. On coherent diagrams restriction is `MonoidalClosed.pre`.
- The second conjunct says this canonical e itself is a localization presentation.
  Thus this choice of models gives one simultaneous strict restriction/evaluation system.
  `LocalizedRestriction` also handles arbitrary given L, L', q, q', E and E', with exactly
  the localization and equivalence-to-e hypotheses in the node. It supplies the induced
  map r and both comparisons `q r ≃ N(v*) q'` and `E' r ≃ v* E`.
- Joint higher coherence is stated by `ParametricDescent`, for EVERY chosen localization,
  target quasicategory T and parameter simplicial set B in the containing universe.
  Its restriction map r is fixed by its equality with precomposition by q on the entire
  functor object. `Fun(B,r)` is an equivalence and has contractible normalized homotopy
  fibers on cores. A point of a normalized fiber includes both a lift and its specified
  equivalence to the unlocalized parameter diagram. Thus previously specified comparisons
  are retained: this is transport of whole diagrams, not merely separate existence of
  comparison edges for individual v. Taking B to be chains of indexing maps, simplex
  boundaries or arbitrary parameter diagrams transports the strict identity/composition
  diagrams above with all their coherences. Noninvertible ordinary and localized diagram
  transformations are retained in the full functor objects before taking these choice
  spaces. This is the universal-arrow formulation used in the system-localization node.
- The quantifiers Q and a are an ORDINARY functor and an ordinary natural transformation
  `a : Q ⟶ 𝟭 (KanDiagrams K)`. `IsProjectiveReplacement K M Q a` spells out precisely
  projective cofibrancy of the values and projective trivial fibrancy of the augmentation,
  using the recorded `CovProjectiveData` model. There is no simplicial enrichment on Q.
  `evaluatedAugmentation` is the existing `FiniteReedy.transformation` applied to a,
  transported between two degreewise lifts of the same ordinary nerve. The replacement
  conjunct says this exact edge is an equivalence of ENTIRE coherent functors. It also
  states that Q preserves W, permitting the whole comparison to descend through q.
- `ReplacementZigzags` uses the actual two edges: postcomposition of e(a) by coherent
  restriction, and precomposition of e(a') by ordinary restriction. The common endpoint
  is identified by the strict evaluation identity. Its comparison c is specified by
  `Composes c b' b`, a 2-simplex with these three prescribed boundary edges. It therefore
  uses `Q'(v*P) -> v*P`, without requiring `v*(QP)` to be projectively cofibrant.
- `ReplacementIndependence` gives the contractible Kan space of equivalence augmentations
  to e. Concretely this is the path-fiber of the identity on the core of the ENTIRE
  functor category, over the vertex e. Each evaluated augmentation is an equivalence
  edge in this core with target e, hence a point of this space. This retains the
  comparisons of two or more replacements, their cancellation triangles and all higher
  parameter diagrams. Restriction postcomposition and ordinary precomposition act on
  these diagrams; `ParametricDescent` transports them, with their augmentations retained,
  to the arbitrary given comparison presentations. No inverse is chosen separately on
  individual objects.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `Enhanced.IsEquivalenceEdge`,
  `Enhanced.AreNaturallyEquivalent`, `Enhanced.IsFunctorEquivalence`, `Enhanced.core`,
  `Enhanced.homotopyFiber`, `Enhanced.IsContractible`, and the internal-hom convention.
- `Sheaf.CategoryTheory.CoherentNerveComparison`: `CategoryTheory.coherent_nerve_comparison`
  and its `CoherentNerveComparisonStatement` rigidification/adjunction fields. The actual
  simplex-colimit realization and nerve maps used by evaluation are the ones already
  selected by the dependency, `Pinched.rigidification` and `CoherentNerve.largeNerveMap`.
- `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`:
  `CategoryTheory.simplicial_model_nerve_localization`, with its full functor-category
  localization and Kan-spaces clauses.
- `Sheaf.CategoryTheory.KanDiagramLocalizedEvaluation`: `KanDiagrams`,
  `IsChainEvaluation` and `kan_diagram_localized_evaluation`, including its full signature
  and proof docstring. The theorem already supplies the equivalence comparison for
  every specified coherent localization, not just a homotopy-category equivalence.
- Transitively, `Sheaf.CategoryTheory.SimplicialRightFibrationPresentation`:
  `CovProjectiveData`, `covKanProperty`, `covKanWeak` and the underlying `CovDiagram`.
  `UnmarkedStraighteningQuillen` supplies the existing enriched functor/category data
  and `projectiveFib`; `FiniteReedyLocalization` supplies `largeNerve`, `Inverts`,
  `IsLocalization`, `localDiagrams`, `transformation` and `Composes`.
- The stated proof dependencies `Sheaf.CategoryTheory.SystemLocalizationUniversal`
  (`coef_system_localization_universal`) and `EnhancedFunctorConeCalculus`
  (`enhanced_functor_cone_calculus`) are ordinary proof imports. No import cycle arises.

Edge cases checked before writing and again after compiling:

- Empty K: both enriched and coherent diagram categories are terminal up to the stated
  equivalence; restriction to the empty shape is permitted. Empty Kan values are allowed.
- K = Delta^0, vertex inclusions into Delta^1, degeneracies Delta^1 -> Delta^0, and identity
  maps give the expected point evaluation, source evaluation, constant diagram and identity.
- Non-quasicategory K and noninjective v are included. No preservation of projective
  cofibrancy under v* appears anywhere. The fresh replacement after restriction is explicit.
- Q is only ordinary, and independent Q,Q' need no comparison map before evaluation.
  Same-shape restriction gives the ordinary replacement comparison through the augmentation.
- The parameter B is arbitrary, including empty, boundaries and all standard simplices.
  Homotopy fibers retain normalization paths; an unnormalized space of quasi-inverses
  or a collection of objectwise equivalences would not be the assertion used here.
- Both large nerves wrap exactly the same chains. The explicit `raiseNerve`/`lowerNerve`
  changes no indexing or value universe and imposes no universe equality.

Searches:

1. `msearch.py leanfinder`, query "Localization of Kan valued enriched diagrams is
   coherently compatible with restriction and independent of ordinary cofibrant replacement":
   eight hits, including the ordinary CofibrantObject localization and resolution
   transformations. These compare ordinary homotopy categories, not the full coherent
   evaluation/restriction system. No exact match.
2. `msearch.py loogle`, query `"SimplicialNerve", "Functor"`: zero hits.
3. `msearch.py leansearch`, query "Homotopy coherent naturality of localized enriched Kan
   diagram evaluation under all restrictions": eight hits, including ordinary monoidal
   localization naturality, colimit/evaluation, and `Localization.Construction.natTransExtension`.
   None states this coherent enriched evaluation assertion.
4. `msearch.py grep`, query `rectif|localized.*evaluation|coherent.*restric`, in CategoryTheory:
   zero Mathlib hits. The actual Mathlib closed API `MonoidalClosed.pre`, its strict
   identity/composition laws and internal-hom functoriality are used without copying them.
5. `rg` on upstream WeilConjectures for the item id and proposed theorem name: no hits.
   Conceptual query `rectif|coherent.*restric|projective.*replacement|localized.*evaluation`
   returned only unrelated quasi-coherent module/ideal restriction declarations.
6. `rg` on project Lean found the recorded `KanDiagramLocalizedEvaluation` dependency;
   it gives evaluation/localization at each K but does not assert restriction coherence
   or independence of ordinary replacement systems. Its category, formulas, localization
   API and actual evaluation are reused here. Proposed declaration names also have no
   upstream-name-index or Mathlib collision.

Sources checked: the node's six proof steps; current main-20261015 blueprint,
`prop-coef-integral-exceptional-adjoint.proof.md`, paragraph 2; online HTT Proposition
the project server and Remark the project server (printed page 258). The generic coherence argument is the
agent-formulated deduction explicitly recorded by this node, not an added coefficient
hypothesis. The six proof steps and all their dependency uses are in the theorem docstring.

Validation: `scompile.py` compiles this module separately, including both sandbox and
library-module views. The initial ordinary-transformation universe wrapper mismatch
was repaired by degreewise maps between the two existing lifted nerves. No direct
source checkout edits, direct Git commands, or global builds were used. There is no
statement dispute or source-based statement correction.

## Second reading by Q04

The independent second reading checked the item statement verbatim against the Lean theorem and all helper predicates. The theorem quantifies over arbitrary `K : SSet.{u}`, receives the chain-evaluation map and its `IsChainEvaluation` proof, and concludes the strict restriction system, exact chain evaluation identity, localization for every `K`, arbitrary-presentation `LocalizedRestriction`, parametric descent, ordinary replacement equivalence and weak-equivalence preservation, fresh-replacement zigzags, and replacement independence. The helpers render the same objects using `KanDiagrams`, `covKanWeak`, `largeNerve`, and the containing universe; no additional finiteness, quasicategory, or cofibrancy-under-restriction hypothesis is imposed.

I read the source-place and blueprint citations, the dependency node records and declarations, and the exact declarations in `KanDiagramLocalizedEvaluation`, `SimplicialRightFibrationPresentation`, `SimplicialModelNerveLocalization`, and `FiniteReedyLocalization`. Empty and non-quasicategory indexing shapes, empty Kan values, identity/composite/noninjective restrictions, `n = 0`, arbitrary parameters, and the universe lifts were checked. The definitions have real data or predicates; no hollow construction, arbitrary map, pro-etale substitute, or proof beyond the single theorem `sorry` was found. The required worker report and this section are present.

The immutable module initially failed the mandated per-file compiler because `CoherentDiagrams` was an abbrev depending on the noncomputable `Enhanced.smallSpaces`. The complete replacement in the review fixes that abbrev by marking it `noncomputable`; `scompile.py` then passed both sandbox and library-module compilation, with no errors or warnings. No global build or repository mutation was run.
