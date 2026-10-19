## Worker report

States `SSet.Enhanced.contravariant_fibration_iff_rightFibration` in
`Sheaf.CategoryTheory.ContravariantFibrationsBetweenRightFibrations`. Its single
proof is `sorry`, as required for stage 2. There are no definitions, new nodes,
dependency repairs, statement corrections, disputed statements, or node faults.
The node copy changes only `lean`.

Source checked: [HTT Corollary the project server](https://www.math.ias.edu/~lurie/papers/HTT.pdf),
printed pp. 86–87 (the currently served PDF has the statement on zero-based page 103
and the proof continues on page 104). It assumes two right fibrations over an
arbitrary simplicial set and identifies precisely these two fibration conditions.
The node is a supporting lemma, not the statement of its blueprint unit.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- A fixed arbitrary universe is `universe u`; all three simplicial sets are bound
  by `{S X Y : SSet.{u}}`. No independent size restriction occurs.
- The contravariant model from the presentation dependency is supplied as
  `D : SimplicialRightFibration.RightData S`. The dependency theorem gives
  `Nonempty Presentation`, and `Presentation.right S` has exactly this type.
  This binder names that existing model data; it does not assume an arbitrary
  model or add a mathematical condition on the simplicial sets. The conclusion
  holds for every realization of the dependency's presentation. In particular
  `D.weak_test` fixes the mapping-test weak equivalences in the node, and
  `D.slice.cof` fixes monomorphic cofibrations. `D.slice.fib` is the right lifting
  characterization. No model is chosen from an unspecified existence theorem.
- The two structural maps are `(p : X ⟶ S)` and `(r : Y ⟶ S)`.
- Their right-fibration hypotheses are `(hp : rightFibration p)` and
  `(hr : rightFibration r)`. The existing predicate quantifies over `n ≥ 1`,
  `i : Fin (n+1)`, `0 < i`, so includes exactly the horns `0 < i ≤ n`.
- The simplicial map is `(f : X ⟶ Y)`; the commutative triangle is
  `(comm : f ≫ r = p)`. Composition order is Mathlib's left-to-right convention.
- Regarding it as a slice morphism is
  `(Over.homMk f comm : Over.mk p ⟶ Over.mk r)`, whose underlying map is `f`.
- The left side of `↔` is that arrow's membership in
  `D.slice.simplicial.model.categoryWithFibrations.fibrations`. This explicit
  projection uses the contravariant model of the named dependency, with no
  instance search that might select the inherited Kan model on a slice.
- The right side is precisely `rightFibration f`. Both implications are stated.
- No `Quasicategory` or `KanComplex` instance is required on `S`, `X`, or `Y`.

Statement dependencies read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: the recorded declaration
  `SSet.Enhanced.coneCategory` and the full source interface were read. This node
  supplies the underlying Mathlib `SSet`, standard simplices and horn conventions.
  Only those primitives are needed here; its cone construction is not duplicated.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`: the recorded
  `SSet.Enhanced.cocartesianFibrationOver` publicly reexports
  `Sheaf.CategoryTheory.InfinityFibrations`, whose exact
  `SSet.Enhanced.rightFibration` signature and docstring were read and used.
  The generalized cocartesian predicate is immaterial to this right-horn statement.
- `Sheaf.CategoryTheory.SimplicialRightFibrationPresentation`:
  `SSet.SimplicialRightFibration.simplicial_right_fibration_presentation`,
  `Presentation`, `RightData`, `SliceData`, and `SimplicialModel`; the full
  `RightData.weak_test`, `SliceData.cof`, `SliceData.fib`, and model signatures were
  read. The theorem accesses the actual model's fibration class.

Proof-dependency modules are imported without `public`:
`RightAnodyne`, `RightFibrationSpaceFiber`, `ContravariantSliceModel`,
`RightAnodyneProduct`, `KanFibrationArbitraryBaseFibers`,
`ModelStructureDeterminedByFibrantObjects`, and
`RightAnodyneLiftingCharacterization` (under their recorded Sheaf topic paths).
The public presentation import already covers the other two proof dependencies.
The theorem docstring records all seven proof steps, including the comparison of
the two model structures, strict-fiber argument over `Y`, homotopy orientation,
and endpoint correction. No proof dependency is omitted for an import cycle.

Edge cases checked mathematically before writing:

- Empty base forces empty total spaces; the assertion has no nonemptiness binder
  and remains valid. An empty source over a nonempty right-fibration target is
  also included; all right-horn lifting tests with an empty upper map are vacuous.
- For `S = Δ[0]`, the two structural maps are Kan complexes, and the result is the
  known equivalence of right fibrations and Kan fibrations over a Kan target.
- For the identity map of any right fibration, both sides hold; the base can be
  an arbitrary simplicial set that is not a quasicategory.
- Dimension zero imposes no lifting requirement. Dimension one includes precisely
  the right horn with missing face 1. Neither endpoint orientation nor all-horn
  Kan-fibration lifting has been silently substituted.
- All objects and arrows in the signature live in the same arbitrary universe,
  matching the fixed-universe statement and including its smallest cases.

Searches on 2026-10-17, via the prescribed `msearch.py Q17 <item>` wrapper:

- LeanFinder: `A map between right fibrations over an arbitrary simplicial set is
  a contravariant model fibration if and only if it is a right fibration`.
  Eight hits, including `SSet.modelCategoryQuillen.fibrations_eq`, `fibration_iff`,
  the all-horns lifting instance, and general model-category fibrancy facts.
  None states the right-horn/contravariant comparison.
- Loogle: `"RightFibration"`: zero hits.
- LeanSearch: `Fibrations between fibrant objects in the contravariant model
  structure on simplicial sets are right fibrations`: eight hits, general
  `Fibration`, `IsFibrant`, and Kan-model facts; no exact match.
- Mathlib grep: `contravariant.*model|right[Ff]ibration|right_fibration` in
  `AlgebraicTopology`: zero hits. Read
  `SimplicialSet/CategoryWithFibrations.lean` and `ModelCategory/Over.lean`:
  the former tests all positive-dimensional horns and the latter inherits a
  given model's fibrations, rather than identifying contravariant fibrations.
- `rg` of `contravariant.*fibration|rightFibration|right_fibration` in upstream
  `WeilConjectures`: no hits. The item-id grep in that tree and the upstream
  declaration-name index search also returned no hits.
- The same concept search in `lean/Sheaf/CategoryTheory` and
  `lean/Sheaf/AlgebraicTopology` found the dependency predicates and presentation,
  fiber theorems, and a docstring reference in `RelativeConePresheafFibers`.
  Reading these found no declaration with this equivalence. No duplicate was added.

Validation: prescribed `scompile.py` compiled both the sandbox and destination
module successfully, each in 1.4 seconds, with no warnings. The source has no
unbound implicit variables, local notation, local instance, hidden `let` statement,
or lines over 100 characters. Its only postponed declaration is this DAG theorem.

## Second reading by Q17

Author's self-check under the direct-delivery brief; independent review is left
to the maintainer, and no second agent was started. Reopened the node and the
written signature. The three arbitrary simplicial sets, both structure maps,
both right-fibration hypotheses, the triangle equation, the slice arrow and both
sides of the equivalence match as listed above. Explicitly rechecked that the
fibration projection belongs to `D`, not the ambient Kan model. The package
parameter merely names the model already supplied by the statement dependency;
its mapping-test and cofibration fields specify the required model. No mismatch
or correction was found. The source is exactly HTT the project server and no extra base
hypothesis, construction, or postponed helper theorem has been introduced.
