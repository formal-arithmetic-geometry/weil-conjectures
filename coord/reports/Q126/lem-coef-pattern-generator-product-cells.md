## Worker report

`Sheaf.AlgebraicTopology.PatternGeneratorProductCells` states
`SSet.Enhanced.PatternCells.pattern_generator_product_cells`. Only its proof is
`sorry`. All helper definitions have real data. The item statement and proof plan
are unchanged; the node copy changes `lean` and adds already-landed statement
nodes owning reused constructions. No new nodes or dependency repairs are needed.

Source read: Higher Algebra, Definition B.1.1, Proposition B.1.9 with its fourteen
cases, and Lemmas B.1.11--B.1.13, at the source URL in the node. The final theorem
has three independently quantified conjuncts, so (c) needs no supplied generator,
monomorphism, cone, or nonempty family. All fourteen DAG proof steps are explained
in its docstring. The module retains plain imports for each recorded proof
module; the unstated `lem-coef-pattern-marking-cancellation` has no module to import.

The exact rendering of the hypotheses and each generator is as follows:

- `P : SSet.Enhanced.CategoricalPattern.{u}` is the recorded small fully scaled
  pattern: its carrier is a quasicategory, its marking contains degeneracies,
  its scaling contains every triangle, its cone index has type `Type u`, and
  every edge of each specified left cone maps to the marking. `P.Object` and
  its existing category are precisely the marked slice in the node.
- `IsDisplayedOver f g b` requires the marked source and target to be exactly
  those of `g`, the underlying arrow to be `g.val`, and the target base map to
  be exactly `b`. Its heterogeneous equalities transport only along the
  endpoint equalities. The source base map is forced by `f.over`. Thus the
  predicate does not replace the specified structural map by a mere existence
  of some map to the base.
- (A0) is `Marked.triangleMarkingMap`, whose source has degeneracies and the
  image of all edges of the inner two-horn marked. This is the marking-pushout
  source in the node. The first disjunct quantifies over every triangle `b`
  carrying every edge to `P.marked`.
- (A1) is `Marked.flatToMarked (Marked.sharp inverseTetrahedron)`. The existing
  `inverseTetrahedron` is constructed by the two successive simplicial pushouts
  collapsing exactly edges `02` and `13` of the tetrahedron, to separate points.
  The second disjunct quantifies over every `b` carrying all its edges to the
  marking. It marks every edge of this quotient, without assuming it Kan.
- (B0) is `initialVertex`, namely `Marked.sharpMap (stdSimplex.δ 1)`. Omitting
  vertex 1 selects vertex 0, so this is the required initial endpoint. The
  third disjunct requires its base edge to belong to `P.marked`.
- (B1) is `Marked.sharpMap (leftJoinConeInclusion (P.cone α))` over exactly
  `P.left_cone α`. The fourth disjunct quantifies over every `α : P.index`.
- (C0) is the existing `Marked.initialMarkedHorn (n + 1)`, in dimension `n + 2`.
  It marks exactly the first edge and degeneracies, restricting this marking
  to the horn. These are all dimensions greater than one, including dimension
  two. The fifth disjunct imposes only that the image of the first edge of `b`
  belongs to `P.marked`.
- (C1) is `Marked.flatMap (horn n i).ι` with both inequalities
  `0 < i.val` and `i.val < n`, over every simplex `b`. This excludes outer
  horns and dimension zero, and adds no marking on nondegenerate edges.
- (C2) is `coneCell (n + 1) (P.cone α)`. `finalSubcone` is the ordered-join map
  induced by the last vertex of the simplex and the identity on the cone
  shape. `coneTarget` marks the images of every edge of this subcone and all
  degeneracies. The source uses its induced marking along the boundary-join
  inclusion. Since the final vertex lies in the boundary for every positive
  dimension, this is exactly the displayed source marking pushout. The
  seventh disjunct imposes the actual restriction equation
  `finalSubcone (n + 1) (P.cone α) ≫ b = P.left_cone α`, in every dimension.
  All positive dimensions occur and no finiteness condition is imposed on `Kα`.
- `generators P` is the disjunction of these seven families.
  `pointGenerators` uses exactly (A0), (A1), (B0), (C0), and (C1) in marked
  simplicial sets, using the existing `MorphismProperty.ofHoms`. It is
  independent of `P`, as the cone-free point pattern must be. In particular,
  an empty cone family removes (B1)/(C2), but never (B0).
- `anodyne P` is the intersection of all classes in the actual pattern slice
  containing these generators and isomorphisms and closed under pushouts,
  `u`-small transfinite compositions, and arrow retracts. `pointAnodyne` uses
  the existing `Marked.markedWeakSaturation` on `pointGenerators`.
- `markedPushoutProduct f g` is an actual map from the existing marked pushout
  of `f × id` and `id × g` to the product target. It uses
  `Marked.markedPushoutDesc` and the two canonical product maps. The existing
  pushout has the degreewise simplicial pushout and images of input markings.
  `productObject`, `pushoutProductSource`, and `pushoutProduct` give this same
  construction over `P`, with base map the first projection. No arbitrary map,
  arbitrary pushout representative, or unproved existence choice is used.
- In (a), `generators P j` is exactly generator membership and `Marked.cof v`
  is injectivity of `v.val.app n` for every simplicial degree. The conclusion
  is `anodyne P (pushoutProduct j v)`.
- In (b), `f` is a morphism of `P.Object`, hence already over the base;
  `Marked.cof (markedMap f)` states its degreewise injectivity.
  `pointGenerators h` is the point generator hypothesis. The conclusion is
  `anodyne P (pushoutProduct f h)`.
- In (c), `a : U ⟶ V` is an arbitrary ordinary simplicial map and
  `SSet.leftAnodyneExtensions a` is the already-landed closure of the initial
  horn inclusions with isomorphisms, pushouts, small transfinite compositions,
  and retracts. The conclusion is exactly
  `pointAnodyne (Marked.sharpMap a)`.

Reused declarations and owning dependency modules:

- `Sheaf.CategoryTheory.CategoricalPatternFibrancy`:
  `SSet.Enhanced.CategoricalPattern`, `.Object`, `.Hom`, and the existing category.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`:
  `SSet.Marked`, its category, `flat`, `sharp`, `sharpMap`, `flatMap`, `cof`,
  `product` and `productMap`.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`: the recorded standard
  simplices, boundaries and horns, with Mathlib's definitions unchanged.
- `Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus`:
  `Marked.triangleMarkingMap`, `flatToMarked`, `inducedMarking` and
  `inducedMarkingMap` (available through `MarkedCoanodyne`).
- `Sheaf.AlgebraicTopology.MarkedCoanodyne`:
  `Marked.initialMarkedHorn`, including its exact first-edge marking.
- `Sheaf.AlgebraicTopology.FiniteInverseTetrahedron`:
  `SSet.Enhanced.inverseTetrahedron` and its genuine two-pushout construction.
- `Sheaf.AlgebraicTopology.MarkedTriangleCancellation`: `Marked.withEdges`
  (available through `MarkedEndpointPrismGeneration`).
- `Sheaf.AlgebraicTopology.MarkedEndpointPrismGeneration`:
  `Marked.markedPushout`, `markedPushoutDesc`, and `markedWeakSaturation`.
- `Sheaf.CategoryTheory.LeftAnodyne`: `SSet.leftAnodyneExtensions`.

The six added statement dependencies are already landed and have usable recorded
Lean declarations. Their definitions are used as recorded; no dependency file is
changed. I checked that none of these nodes reaches this item, so the additions
introduce no dependency cycle. The remaining helper definitions belong to the
notions explicitly introduced by this item's statement and are all listed in
`lean.declarations` with source and blueprint docstrings.

Edge cases checked: empty `P.index`; empty cone shapes; empty simplicial sets;
zero-dimensional boundary in the proof reduction; `n = 1` for (B0)/(C2);
`n = 2` for (A0)/(C0)/(C1); arbitrary positive dimensions; identity and
marking-only injections; and infinite small cone shapes. In particular the last
vertex is in the boundary exactly where (C2) uses it, and the initial horn in
dimension one is the initial endpoint. Clause (c) is independent of the first
two inputs. No nonemptiness, finite-dimensionality, finite cone family, Kan
condition on a cone shape, or extra universe equality is assumed.

Searches actually run with `msearch.py Q126 lem-coef-pattern-generator-product-cells`:

- `leanfinder "Pushout products of marked categorical pattern generators with degreewise injective marked maps"`:
  eight generic small-object and `AttachCells` hits; none has markings or a pattern.
- `loogle '"MarkedSSet", "anodyne"'`: zero hits.
- `grep 'categorical.?pattern|pattern.?anodyne|marked.*anodyne' AlgebraicTopology`:
  zero hits.
- `leansearch "Marked simplicial sets categorical pattern anodyne generators pushout product sharp left anodyne"`:
  eight ordinary Kan-model and horn-colimit results; no marked-pattern theorem.
- `rg` for `PatternGenerator`, `generator.*product`, `left.?anodyne`, and
  `CategoricalPattern` in the read-only upstream `WeilConjectures/` found no
  matching theorem. `grep -rn` for the item id there returned no occurrence.
  `rg` in the shared `lean/Sheaf` identified the above reusable definitions,
  including the exact inverse tetrahedron, initial marked horn, marked pushout,
  and ordinary left-anodyne class. `rg` for this module's namespace and theorem
  in Mathlib/project name records found no name collision. Existing siblings
  `lem-coef-pattern-anodyne-generators` and
  `lem-coef-pattern-anodyne-lifting-products` have no recorded Lean module and
  their further conclusions differ; this delivery supplies this item's explicit
  generators for those later consumers. No existing declaration states the item.

No statement correction or `STATEMENT-DISPUTED` is needed.

## Second reading by Q126

This is the author's fresh self-check; the dispatcher prohibits starting another
agent, and the maintainer performs the independent review. I reopened the node
and the final module and checked each of the seven families and three clauses.
The initial draft had omitted (A1), used incorrect sharp targets for (C0), lost
the (C2) restriction equation, and forgotten structural maps by using an
unsliced closure. I replaced those helpers in full before delivery. I also
removed the draft's redundant copy of the left-anodyne class and its
universal pushout-product predicate, using the existing left-anodyne definition
and an actual canonical marked pushout product. The final statement quantifies
its three clauses independently. Its generator disjuncts now have the exact
markings, dimensions, underlying arrows, codomain base maps and cone equation
listed above. All helper data are constructed, the only theorem proof is
`sorry`, and every declaration is recorded in the item's `lean.declarations`.

Validation: `scompile.py Q126 lem-coef-pattern-generator-product-cells
lean/Sheaf/AlgebraicTopology/PatternGeneratorProductCells.lean` completed with
exit code 0 and no warnings or errors, in both sandbox and library-mode checks
(5.1 seconds and 4.3 seconds). Explicit source names and the `joinBoundary`
helper resolved elaboration ambiguities; the final helper list and signature
were extracted again from the final file. Every line is at most 100 characters.
