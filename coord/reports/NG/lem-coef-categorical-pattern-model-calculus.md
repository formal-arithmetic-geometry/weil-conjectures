## Worker report

This is the stage-2 statement of `lem-coef-categorical-pattern-model-calculus`, in
`lean/Sheaf/CategoryTheory/CategoricalPatternModelCalculus.lean`. The single theorem
`SSet.Enhanced.CategoricalPattern.categorical_pattern_model_calculus` has proof `sorry`.
All helper definitions have explicit data; no existence theorem is used to choose an object.
The item copy changes only `lean`. There are no new nodes, dependency repairs or statement
corrections.

The dispatch sandbox initially contained only `.brief2` through `.brief5`. It had no
`report.md`, node packet, citations or citation revalidation. The route note concerns the
older NO stage-1 packet; I read the landed NO report, its fibrancy citation repair and the
current seventeen-step split. That split is preserved. This task is now stage 2; I have not
reconstructed or redelivered the stage-1 split or represented its historical checks as
checks of this statement. The delivery wrapper supplies the direct-worker second-reading
notice; the maintainer performs the independent review, as the current brief requires.

Source read: Higher Algebra, Theorem B.0.20, Remark B.0.25, Definition B.2.1, Lemma B.2.4,
the proof of B.0.20 and Remarks B.2.5--B.2.6; Gepner--Haugseng arXiv:1312.3178,
Definitions 3.2.1 and 3.2.3, Theorem 3.2.5 and Remark 3.2.12. These are the small fully
scaled quasicategory patterns of the definition dependency. There is no Stacks analogue.
The theorem docstring follows each of the node's seventeen proof steps, including the
sufficiently filtered argument for infinite cones, without proving them in this stage.

Clause-by-clause correspondence:

- The only input is `P : SSet.Enhanced.CategoricalPattern.{u}` for arbitrary universe `u`.
  This is exactly the recorded pattern, including its small base, chosen marking, all
  scaled triangles and arbitrary small cone family. `Object P` and its recorded category
  are the pattern's marked slice. No new closure condition on the marking, finiteness of
  cones, nonemptiness or universe equality is imposed.
- The existential `K : SSet.Marked.CartesianModelStatement.{u}` is the dependency's
  categorical marked point model. `ModelStatement P K` extends `Enrichment P` and contains
  the actual `ModelCategory (Object P)`. Completeness and cocompleteness use
  `HasLimitsOfSize.{u,u}` and `HasColimitsOfSize.{u,u}`. Local presentability and the two
  small generating morphism properties, together with both functorial factorizations,
  give exactly the stipulated combinatorial model convention.
- `cofibrations` identifies the model class with `cof`, defined as injectivity of
  `f.map.app n` for every `n : SimplexCategoryᵒᵖ`. It includes marking-only inclusions.
- `fibrant_objects` states the equivalence between fibrancy of the map to any terminal
  object and **the existing** `IsCategoricalPatternFibered P X`. I reread its current
  source through `scompile.py --source`, and checked the classifying-functor whole-diagram
  comparison and the relative-limit clause for every cocartesian section. Both are used
  by this exact predicate, without unfolding, dropping, modifying or privately copying it.
  Its inner-fibration and exact cocartesian marking clauses are retained as well.
- `left_proper` is `weak.IsStableUnderCobaseChangeAgainst cof`, namely preservation of
  weak equivalences under pushout along the stipulated cofibrations.
- `expand` and `expandMap` retain the original object, marking and base map, regarded over
  the sharply marked underlying base solely to use the established relative mapping API.
  Since source and target already lie over the original marking, their over-base Hom sets
  are unchanged. No object of `Object P` is enlarged to a different category for the model.
- `hom A B` has underlying simplicial set `SSet.Marked.Over.mapFlat (expand A) (expand B)`.
  Its n-simplices are exactly maps with flat simplex parameter and the equation over the
  fixed base. Its marking tests every marked source edge against **every** edge of the
  interval, precisely preservation with the sharp interval parameter.
- `Enrichment.curry` is the marked representing bijection between maps from the actual
  product `A × L` over the base and maps `L → hom A B`. `curry_formula` fixes evaluation
  for every parameter simplex and its every face/degeneracy, so this is the canonical
  adjunction, including its naturality, rather than an arbitrary equipotence.
  `composition_formula` fixes actual composition in every simplex.
- `mapSharp` is the existing relative sharp mapping complex; `mapSharpPre` is actual
  precomposition with the given map. `weak` quantifies its weak homotopy equivalence
  against every existing pattern-fibered `Z`. `weak_equivalences` identifies exactly this
  class with the model class. `mapping_kan` makes these same complexes Kan for fibrant
  targets, without requiring the source fibrant.
- `Enrichment.simplicial` is a genuine `SimplicialCategory (Object P)`.
  `sharp_mapping`, `sharp_ordinary` and `sharp_composition` identify its mapping objects,
  ordinary maps and composition with the specified sharp complexes in every degree.
  `tensor_adjunction` and `tensor_formula` identify the sharp-parameter tensor with those
  complexes. `simplicial_tensor_cotensor` is the existing enriched representing
  tensor/cotensor structure; its two object equations identify its tensors and cotensors
  with the stipulated product and the marked cotensors at sharp parameters.
  `simplicial_model` asserts the actual SM7 corner-map property for this enrichment and
  this model. `simplicial_pushout_product` also gives its displayed tensor axiom with
  monomorphisms and Kan weak homotopy equivalences in the parameter variable.
- `productLeft` and `tensor` have actual marked products as objects and the actual product
  maps as their action. Their base map is projection onto the first factor followed by
  that object's structure map, as required. `Enrichment.cotensor` is a right adjoint to
  this exact tensor functor. Combined with the normalized `curry`, this is precisely the
  requested representing cotensor. `enriched_cotensor` additionally gives its marked
  internal-Hom representing identity.
- `restriction` and `postcomposition` are the actual marking-preserving maps on relative
  Hom objects. `marked_model_axiom` quantifies every pullback of the displayed cospan
  and its uniquely characterized corner map, fixing **both** composites with the
  projections. For every model cofibration `i` and fibration `r`, this map is a fibration
  in `K`; the disjunction of their weak-equivalence conditions makes it trivial. The
  latter uses `SSet.Marked.weak`, exactly `K.weak_equivalences`' class.
- `IsPushoutProduct` specifies the universal pushout of the actual product maps and
  fixes the outgoing map by its two restrictions. `marked_pushout_product` states that
  it is a pattern cofibration, trivial when **either** `i` or `j` is a weak equivalence,
  with `j` a cofibration of the same point model. No arbitrary map replaces this arrow.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CategoricalPatternFibrancy`: `SSet.Enhanced.CategoricalPattern`,
  its `Object`, `Hom`, category, and `SSet.Enhanced.IsCategoricalPatternFibered`.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`: `SSet.Marked`, marked maps,
  products, `sharp`, `internalHom`, `cof`, `weak`, and `CartesianModelStatement`; its
  complete model theorem signature and docstring were read.
- `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`: the recorded ordinary model
  category convention (`HomotopicalAlgebra.ModelCategory` from Mathlib), its weak
  factorization systems and trivial-map convention. I read the full recorded
  `quillenAdjunctionInfinityLocalization` signature and docstring; no unrelated
  infinity-localization conclusion is assumed here.
- The existing public relative mapping API from
  `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`, reached through the fibrancy
  dependency: `SSet.Marked.Over.mapFlat`, `mapSharp`, `mapSharpPre` and `productMapLeft`.
  Their full definitions and the relevant product helpers were read. These are reused,
  with no new underlying notion of relative mapping simplex.
- The existing `CategoryTheory.SimplicialTensorCotensor` and
  `CategoryTheory.SimplicialModelLocalization.SatisfiesSM7` (including its actual
  canonical corner-map definition) express the simplicial axiom. Their modules are
  public imports. The other nine non-public imports are exactly available stated proof
  dependencies. The two proof dependencies without recorded modules, anodyne lifting
  products and fibered edge detection, are named in the proof docstring; no nonexistent
  import was invented.

Edge cases checked before writing: the empty base admits only empty total spaces and all
mapping tests stay meaningful; empty source or parameter products are allowed; the empty
cone family imposes no cone conditions, whereas an empty individual cone still invokes
both clauses of the recorded fibrancy predicate. The point pattern gives the dependency's
categorical marked model. Partially marked bases retain the original `map_marked` condition.
Neither fibrancy nor the model asserts a vertex-only equivalence test. Infinite cones stay
small in `u` and are not made finite. Dimension zero is included in `cof`; all parameter
formulas quantify every simplex. The Hom axiom allows both triviality cases, empty sources,
nonfibrant general endpoints and arbitrary cofibrations/fibrations of the pattern model.
No STATEMENT-DISPUTED issue or node correction was found.

Searches actually run via `msearch.py`, with literal records in `searches.jsonl`:

- LeanFinder: `categorical patterns marked simplicial sets left proper combinatorial
  simplicial model structure enriched Hom`; eight hits, including the Kan horn/boundary
  classes, Quillen cofibrations/fibrations, ordinary QCat enrichment and simplicial Hom.
  Their displayed signatures and the relevant sources were read; none is the general
  marked-pattern theorem.
- Loogle: `"ModelCategory", "Simplicial"`; no hits.
- Mathlib grep: `CategoricalPattern|categorical.pattern|marked.*model.structure`; no hits.
- LeanSearch: `There is a left proper combinatorial simplicial model structure for every
  categorical pattern with marked enriched Hom`; eight hits on the general model axioms
  and the unmarked Kan classes, not this model. In particular `ModelCategory.mk'` only
  constructs a model from already supplied weak factorization systems.
- `rg` of upstream `WeilConjectures/` for the exact item id and categorical-pattern names,
  and the upstream name index: no existing statement. `rg` of current `lean/Sheaf` finds
  the current definition dependency and the ordinary/generalized **operadic** model.
  I read `MarkedOperadicModelStructures.lean`: its fixed inert simplex base and two
  special fibrancy predicates are not every small categorical pattern. Its slice Hom
  implementation informed the same explicit construction here. The relative Cartesian
  model requires full base markings and likewise does not state this node.

Validation is through the prescribed per-file compile and current `deliver2.py --no-push`;
results are recorded below once complete. All edits are in the assigned sandbox. No global
build, direct Git operation or modification of a live source file was performed.

The final file compiled cleanly through `scompile.py`: sandbox check 6.1 s and server
library confirmation 21.7 s, with no error or warning. A local packet audit found exactly
one changed item key (`lean`), one theorem with its single `sorry`, a verbatim recorded
signature, and no Lean line over 100 characters. The first compile also succeeded; only
the final compile above is used as validation of the complete statement.

The retained Q79 dry run was only a prior validation of the same packet. This NG packet
must be validated again with the prescribed current `deliver2.py` invocation.

## Second reading by NG

I reread the current item node and all three statement dependencies. The theorem signature
is verbatim and has exactly one explicit input `P`; its existential `K` and `Nonempty`
conclusion match the node without added hypotheses or weakened clauses. The fibrancy
dependency is the current four-clause definition: inner fibration, cocartesian lifts and
exact marking, classifying relative-limit condition, and relative limits for every
cocartesian section. The module uses that declaration directly through
`IsCategoricalPatternFibered`; it does not copy or specialize it. The marked-point model
and model-infinity dependencies supply exactly the marked model conventions used in
`ModelStatement`. All helper definitions have real data, and the theorem alone has
`sorry`. Empty base, empty cone family and empty individual cones remain allowed, and no
finite-cone or universe-equality hypothesis was introduced. The current `scompile.py`
compile succeeded with no errors or warnings. No statement correction, dependency repair,
new node, or dispute is present.
