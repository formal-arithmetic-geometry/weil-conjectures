## Worker report

Item: `lem-coef-pattern-anodyne-generators`, group Q114, stage 2.
Module: `Sheaf.CategoryTheory.PatternAnodyneGenerators`.
Declaration: `SSet.Enhanced.CategoricalPattern.pattern_anodyne_generators`.
The only new declaration is this theorem, with proof `sorry`.

The statement is unchanged. Its explicit family and saturation already exist in
`Sheaf.CategoryTheory.PatternAnodyneLiftingProducts`, so they are reused rather
than defined a second time. The already landed node
`lem-coef-pattern-anodyne-lifting-products` is added to `stmt_deps` under the
permission to add landed statement dependencies. No new nodes, dependency
repairs, statement corrections or disputed assertions are required.

Hypotheses and conclusions, clause by clause:

- A small, fully scaled categorical pattern is `P : CategoricalPattern.{u}`.
  Its `carrier`, `quasicategory`, `marked`, `marked_degenerate`, `index`, `cone`,
  `cone_quasicategory`, `left_cone` and `left_cone_marked` fields retain exactly
  the dependency's objects and assumptions. `scaled_all` records full scaling.
- A marked object over the marked base is `X : Object P`; a morphism `D ⟶ X`
  already includes its underlying simplicial map, the equality over the base,
  and preservation of marked edges. No extra arbitrary maps or lifting data
  are supplied as hypotheses.
- The seven-way disjunction `PatternAnodyne.generators P` is the displayed
  family `J_P`. Each alternative is an `overGenerator`, including every
  permitted base map and requiring that the target's marked edges land in
  `P.marked`. Its family-by-family correspondence is given below.
- `IsCategoricalPatternFibered P X ↔ ...` retains both implications with exactly
  the recorded four-clause fibered-object predicate.
- `∀ (D E : Object P) (j : D ⟶ E), generators P j → ∀ a : D ⟶ X, ...`
  quantifies over every generator and every marked map from its domain over
  the base. `∃ b : E ⟶ X, j ≫ b = a` is exactly the extension, including its
  marking and base-map requirements. The equality has the correct direction;
  it does not impose uniqueness.
- `∀ (D E : Object P) (j : D ⟶ E), PatternAnodyne.anodyne P j → ...`
  covers the entire weak saturation, not only the generators. The reused
  `anodyne` is the intersection of classes containing the family and
  isomorphisms, stable under cobase change, universe-u transfinite composition
  and arrow retracts. This is the standard weak saturation, including
  length-zero composites. It uses `IsStableUnderTransfiniteComposition.{u}`.
- `cof j ∧ weak j` renders precisely trivial cofibration. These are the
  `CategoricalPattern.cof` and `CategoricalPattern.weak` classes fixed by
  `ModelStatement.cofibrations` and `ModelStatement.weak_equivalences` in the
  model-calculus dependency. Thus no choice of a model witness is necessary.
- The universe `u` is explicit and arbitrary. Neither the signature nor the
  reused generator definitions impose `Finite`, finite presentability or any
  cardinal bound on a cone shape beyond the dependency's universe-smallness.

The exact seven families, read in the generator definition:

| Node type | Reused Lean construction | Marking and base condition |
| --- | --- | --- |
| A0 | `Marked.triangleMarkingMap` | Underlying two-simplex, degeneracies and the image of horn 1 marked in the source; all edges marked in the target; every base edge lands in `P.marked`. |
| A1 | `Marked.flatToMarked (Marked.sharp inverseTetrahedron)` | `inverseTetrahedron` is the successive pushout collapsing edges 02 and 13, keeping the two attached vertices distinct; flat to sharp, all base edges marked. |
| B0 | `PatternAnodyne.b0` | The constant initial vertex 0 maps to the sharp interval; all target base edges lie in `P.marked`. |
| B1 | `Marked.sharpMap (leftJoinConeInclusion (P.cone α))` | Both sides sharp; `b = P.left_cone α` fixes the exact specified base map. |
| C0 | `Marked.initialMarkedHorn (n + 1)` | Dimension `n + 2`, hence exactly all dimensions greater than 1; the simplex marks edge 01 and degeneracies, the horn has its intersection marking, and the first base edge is marked. |
| C1 | `Marked.flatMap (horn n i).ι` | Exactly `0 < i.val ∧ i.val < n`, flat source and target, and unrestricted base map. |
| C2 | `PatternAnodyne.c2 n (P.cone α)` | Dimension `n + 1`, hence exactly all positive dimensions; `boundaryJoin` and `finalCone` use the recorded ordered join, and equality of the final-cone composite with `P.left_cone α` fixes the prescribed restriction. |

For A0 and C0 a marked pushout changes only the marked edge subset, which is
exactly the degenerate edges together with the indicated edge images. C2 uses
`markImage (finalCone n K)` on the target and its induced intersection marking
on the boundary join; the entire final cone lies in that boundary for positive
dimension. These are the same pushout markings as in the node. The horns,
boundaries and joins are the existing simplicial constructions, not newly
axiomatized operations. Full scaling makes the source's scaling constraints
automatic; being a marked object supplies the first-edge constraint in C0.

Dependency declarations read and used (full signatures and docstrings inspected):

- `Sheaf.CategoryTheory.CategoricalPatternFibrancy`:
  `SSet.Enhanced.CategoricalPattern`, its `Object`, `Hom` and category instance,
  and `SSet.Enhanced.IsCategoricalPatternFibered`.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`: `SSet.Marked`, `Hom`,
  `flat`, `sharp`, `flatMap`, `sharpMap` and `marked_point_cartesian_model`;
  the marked primitives occur through the reused generator constructions.
- `Sheaf.CategoryTheory.CategoricalPatternModelCalculus`:
  `SSet.Enhanced.CategoricalPattern.cof`, `weak`, `mapSharpPre`,
  `ModelStatement` and `categorical_pattern_model_calculus`.
- `Sheaf.CategoryTheory.PatternAnodyneLiftingProducts`:
  `SSet.Enhanced.PatternAnodyne.generators`, `anodyne`, `overGenerator`,
  `finalCone`, `boundaryJoin`, `c2`, `toTerminal`, and
  `pattern_anodyne_lifting_products`. Its sources for triangle markings,
  induced markings, initial horns and the inverse tetrahedron were also read.
- Proof-only import `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen`, especially the boundary-lifting
  characterization of trivial Kan fibrations. All recorded proof-dependency
  modules are imported; no import cycle was introduced.

Edge cases checked by inspecting the definitions and all quantifiers:

- Empty `P.index` removes B1 and C2, leaving exactly the other five families.
- An empty cone is allowed: its left cone is the point, B1 is the empty-to-point
  inclusion, and C2 becomes a boundary-to-simplex inclusion with the final
  vertex marked (only a degenerate edge there). Empty-cone limit conditions
  remain in `IsCategoricalPatternFibered`.
- C2 starts at dimension 1, represented by parameter 0; C0 starts at dimension
  2, also represented by parameter 0. No dimension-zero C2 or dimension-one
  C0 is introduced. C1 has no case below dimension 2.
- For C0 in dimension 2, edge 01 belongs to horn 0, so its induced marking
  equals the displayed source pushout marking.
- Empty base and the cone-free point pattern are included by the same binder.
  In particular, there is no nonemptiness hypothesis on the base or the index.
- Infinite small cone shapes are not replaced by finite approximations.
- Equality `j ≫ b = a` is equality of actual slice morphisms, so an extension
  cannot silently change either its base map or its marking preservation.

Searches performed for an exact existing statement:

- `msearch.py ... leanfinder "Categorical pattern anodyne marked inclusions
  characterize fibered objects and are trivial cofibrations"`: 8 hits, headed
  by `SSet.modelCategoryQuillen.fibrations_eq`, `fibration_iff` and generic
  model-category lifting results. No exact marked-pattern result.
- `msearch.py ... leansearch "Categorical pattern fibered marked simplicial
  objects detected by marked anodyne generators"`: 8 hits, unmarked Kan
  fibrations and ordinary fibered categories; no marked-pattern theorem.
- `msearch.py ... loogle "HomotopicalAlgebra.trivialCofibrations"`: 12 generic
  definitions and lemmas. Read the source definition, which is the intersection
  of the cofibration and weak-equivalence classes; none specializes to patterns.
- `msearch.py ... grep "CategoricalPattern|pattern.anodyne|MarkedSSet"`:
  zero Mathlib hits. The relevant Mathlib Kan horn declarations in
  `AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean` were read and do
  not include markings or prescribed cones.
- `rg` over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, including the
  item id, `pattern_anodyne_generators` and `CategoricalPattern`: zero hits.
  The upstream-name index has no item-id or proposed-declaration match.
- `rg` over shared `lean/Sheaf` found `PatternAnodyneLiftingProducts` and its
  consumers, including `FinitePatternUniverseComparison`; their definitions
  are reused. Its theorem has the recognition criterion and mapping-space
  lifting results but does not literally state the second conclusion about
  the pattern model's weak equivalences. No existing exact declaration of
  this two-clause theorem was found.

Source verification: read [Higher Algebra, Appendix B](https://people.math.harvard.edu/~lurie/papers/HA.pdf),
Definition B.1.1, Proposition B.1.6, Proposition B.1.14 and Example B.2.2 online.
The seven constructions, extension criterion and mapping-space argument agree
with those source places. The node is the fully scaled specialization over the
recorded quasicategory base.

Validation: the required `scompile.py Q114 lem-coef-pattern-anodyne-generators`
run compiled the delivered module successfully, with no diagnostics (sandbox
2.1 seconds; library check 13.3 seconds). Explicit `autoImplicit false`; all
variables and the universe are bound. The recorded signature is exactly the
file's signature through the point immediately before `:=`; all Lean lines
are at most 100 characters.

## Second reading by Q114

A separate self-review pass reopened the completed module and the node; this
is not represented as an independent agent review. The dispatcher explicitly
prohibits starting other agents; the maintainer supplies the independent
review of this direct delivery.

The pass matched the pattern binder to all fields of `CategoricalPattern`,
read every alternative of `PatternAnodyne.generators` against A0--C2, and
checked the positive-dimension shifts and first/last vertex choices. Both
conclusions have exactly the requested quantifier order: an iff for each X,
then every anodyne j is a cofibration and a weak equivalence. There is no
restriction to fibrant domains or codomains. `cof` and `weak` resolve in the
model-calculus namespace, not to the similarly named `PatternAnodyne.cof`.
The saturation's explicit small-composition universe is u. The relative Hom
constructions used in the proof agree on the nose: `PatternAnodyne.toOver`
and model-calculus `expand` retain the same objects and maps. No mismatch
was found and no statement change was made. The sole dependency-list addition
records the already landed definitions used in the signature.
