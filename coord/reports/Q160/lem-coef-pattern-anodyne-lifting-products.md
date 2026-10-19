## Worker report

The module `Sheaf.CategoryTheory.PatternAnodyneLiftingProducts` states
`SSet.Enhanced.PatternAnodyne.pattern_anodyne_lifting_products`. Its proof is `sorry`.
All other declarations are constructions with real data, owned by this node: its seven
generator families, weak saturation, point pattern, external product and canonical slice
conversions. No independent mathematical notion or missing prerequisite is substituted.
The definitions have no postponed proofs. No node statement is corrected or disputed.

Source read: Lurie, Higher Algebra, https://people.math.harvard.edu/~lurie/papers/HA.pdf,
B.1.1, B.1.6, B.1.9, B.1.13--B.1.14, B.0.21 and B.2.2. The online PDF was inspected
at printed pp. 1469--1482. As already recorded in the node, the final sentence of B.1.14
has the P0/P typo; its proof and B.2.2 give the P-anodyne clause stated here.

Clause correspondence (names below are in `SSet.Enhanced.PatternAnodyne` unless qualified):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Any small fully scaled pattern, with its given cones | `P : CategoricalPattern.{u}` from the recorded dependency; no new structure or base hypotheses |
| Marked objects and morphisms over `(C,S)` | `P.Object` and its recorded category instance |
| All possible indicated base maps | `overGenerator P g condition` quantifies over `b` and its marking-preservation proof; `liftMap` equips the canonical source with its composite base map |
| (A0), all triangle edges in S | `Marked.triangleMarkingMap` and the first disjunct of `generators` |
| (A1), collapse opposite edges 02 and 13, all Q edges in S | `Marked.flatToMarked (Marked.sharp inverseTetrahedron)` and the second disjunct; the recorded Q is the two successive actual simplicial pushouts |
| (B0), initial vertex of an S edge | `b0` uses the vertex 0 constant map into the sharp interval; all its image edges must lie in S |
| (B1), each prescribed cone | `Marked.sharpMap (leftJoinConeInclusion (P.cone α))`, with transported target base map equal to `P.left_cone α` |
| (C0), n greater than 1, just edge 01 marked | `Marked.initialMarkedHorn (n + 1)` in dimension `n+2`; its marking is precisely degeneracies and the first edge, with that base edge explicitly required in S |
| (C1), exactly inner horns and arbitrary base simplex | `Marked.flatMap (horn n i).ι`, `0 < i.val` and `i.val < n`; `True` here means no additional base restriction, not a theorem hypothesis |
| (C2), n at least 1, exact final cone restriction | `c2 n (P.cone α)` in dimension `n+1`, with `finalCone n (P.cone α) ≫ b = P.left_cone α` |
| Marking pushouts in (C2) | `markImage (finalCone n K)` marks its edge image and degeneracies; `Marked.inducedMarking` restricts this to `boundaryJoin n K`; the final cone is contained in the boundary join because n+1 is positive |
| Ordered join and its simplices, including degree minus one | Existing `orderedJoinFunctor`, reexported by `CategoricalPatternFibrancy` through `RelativeInfinityCone`; its terminal augmentation gives the empty-degree singleton and its ordered concatenation gives exactly the node formula |
| No further scaling conditions | No such predicate is imposed; `P.scaled_all` is already a field of the recorded pattern |
| Small set J | `(generators P).IsSmall.{u}`; `overGenerator` uses literal arrow equality of canonical representatives, not the large class of all isomorphic copies |
| Weak saturation, including isomorphisms | `anodyne P` quantifies over every containing morphism property closed under isomorphisms, Mathlib cobase change, u-small transfinite composition and arrow retracts; this is the intersection defining the least such property |
| Every anodyne map is degreewise injective | `anodyne P ≤ cof P`, where `cof P f = Marked.cof (forgetMap f)`; this includes the generators by the definition of the closure |
| Fibered iff terminal map lifts J | `IsCategoricalPatternFibered P Z ↔ (generators P).rlp (toTerminal Z)`; `terminal P` is exactly `(C,S)` over itself |
| Cone-free point pattern | `pointPattern` has carrier Δ[0], all edges marked, all triangles scaled and index `PEmpty` |
| Exactly naturally marked quasicategories over the point | `IsCategoricalPatternFibered pointPattern (overPoint X) ↔ Marked.IsNaturallyFibrant X`; the latter is the existing predicate giving both Quasicategory and exact equivalence marking |
| Both input maps degreewise injective | `cof P i → Marked.cof j → ...`; no other conditions on their markings or domains |
| Form the external pushout product | An explicit existential `B,p` satisfying existing `Marked.IsPushoutProduct (forgetMap i) j (forgetMap p)`; `product A' L'` carries its base via the first projection |
| Either input anodyne implies the product anodyne | For every such pushout representative, `anodyne P i ∨ anodyne pointPattern (mapOverPoint j)` implies `anodyne P p` |
| Map-sharp over C in degree n | Existing `Marked.Over.mapSharp (toOver A) (toOver Z)`; `toOver` retains the actual marked domain, codomain and underlying base map, merely changing the base marking to sharp |
| Why this retains exactly the slice Hom set | Its degree-n maps preserve the same markings on A times sharp Δ[n] and Z and satisfy the same underlying equation over C; since both objects are already over `(C,S)`, the sharper base adds no morphisms between them |
| Every A and every fibered Z give Kan mapping sets | `∀ Z, IsCategoricalPatternFibered P Z → ∀ A, KanComplex (...)` |
| Restriction along any injective i is Kan | `HomotopicalAlgebra.Fibration (Marked.Over.mapSharpPre (toOverMap i) (toOver Z))`, using the scoped Kan--Quillen fibrations |
| Restriction is trivial Kan for P-anodyne i | The same restriction belongs to `SSet.modelCategoryQuillen.I.rlp`, the recorded exact boundary-lifting characterization, including dimension zero |
| No pattern-slice model structure assumed | The theorem has only the binder P; no model, factorization, fibrancy witness or extra lifting assumption is passed in |

Dependencies used, with the recorded declarations opened and read:

- `Sheaf.CategoryTheory.CategoricalPatternFibrancy`: `SSet.Enhanced.CategoricalPattern`,
  its `Object`, `Hom` and category, and `IsCategoricalPatternFibered`; its reexports
  provide `leftJoinCone`, `leftJoinConeInclusion` and `orderedJoinFunctor`.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`: `SSet.Marked`, its maps,
  `flat`, `sharp`, `sharpMap`, `flatMap`, `product`, `cof`, `IsNaturallyFibrant`,
  `toPoint` and `IsPushoutProduct`. No new model structure is selected.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`: the recorded theorem
  `SSet.KanQuillen.right_proper_kan_quillen`, including the Kan-fibration and
  boundary-RLP identifications. The Lean terms use Mathlib's `KanComplex`,
  scoped `HomotopicalAlgebra.Fibration`, and `SSet.modelCategoryQuillen.I.rlp`.
- Added already landed dependency `lem-coef-finite-inverse-tetrahedron`, module
  `Sheaf.AlgebraicTopology.FiniteInverseTetrahedron`: `SSet.Enhanced.inverseTetrahedron`.
- Added already landed dependency `lem-coef-marked-anodyne-lifting-calculus`, module
  `Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus`: `SSet.Marked.flatToMarked`,
  `triangleMarkingMap`, `inducedMarking`, `inducedMarkingMap`.
- Added already landed dependency `def-coef-infinity-marked-coanodyne`, module
  `Sheaf.AlgebraicTopology.MarkedCoanodyne`: `SSet.Marked.initialMarkedHorn`.
- Added already landed dependency `lem-coef-marked-relative-cartesian-model`, module
  `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`: `SSet.Marked.Over`,
  `mapSharp`, and `mapSharpPre`. This is reused through a canonical conversion,
  rather than defining a second mapping object.

The added dependencies have no path back to the item. Their node records are unchanged.
All published proof-dependency modules are imported (with non-public imports when used
only in the proof). The proof-only nodes `lem-coef-cocartesian-cone-limit-section-test`
and `lem-coef-pattern-generator-product-cells` have no recorded Lean module in the
current DAG, so no nonexistent imports are added. Their precise use is retained in the
nine-step proof docstring. They are not prerequisites for typing this statement.

Edge cases checked before and during drafting:
empty cone index and empty K are not excluded; for empty K, C2 still marks the final
vertex cone and B1 still adjoins that vertex. C0 starts at dimension two; C1 excludes
all horns in dimensions zero and one; C2 starts at dimension one. Empty sources and
empty mapping sets are permitted. The trivial Kan clause includes boundary dimension
zero, so it includes vertex surjectivity. A0 and A1 are marking-only maps with identity
underlying maps. Non-cone base edges have only their stated S restrictions. All small
simplicial sets and all cone indices have the same arbitrary universe u, and the
existing pattern definition retains the larger universe for Cat-infinity.

Searches (full machine results are in the sandbox `searches.jsonl`):

- `msearch.py ... leanfinder`: "Categorical pattern anodyne marked simplicial maps
  characterize fibered objects by lifting and are stable under external pushout
  products". Eight hits, all ordinary Kan lifting/model-category declarations,
  including `SSet.modelCategoryQuillen.J`, `.I`, `.fibration_iff` and the Joyal trick;
  none supplies a categorical-pattern generator family or this theorem.
- `msearch.py ... loogle`: "SSet, HasLiftingProperty". Zero hits (unknown unqualified
  HasLiftingProperty in that service). The qualified second query
  "CategoryTheory.MorphismProperty.IsStableUnderCobaseChange" returned twelve hits;
  its actual Mathlib class and the transfinite/retract classes are used.
- `msearch.py ... grep`: "CategoricalPattern|patternAnodyne|MarkedSSet". No Mathlib hits.
- `msearch.py ... leansearch`: "Weakly saturated closure of a class of maps under
  pushouts transfinite compositions and retracts". Eight hits for model structures,
  retract closure and small-object-argument characterizations; none defines the
  pattern-specific closure. The closure uses the existing Mathlib closure classes.
- `rg` in upstream `WeilConjectures` for the item id, `CategoricalPattern`,
  `PatternAnodyne`, `patternAnodyne`, `MarkedSSet`: no matching statement.
- `rg` in `dag/lean_names_upstream.json` for pattern-anodyne names: no match.
- `rg` in `lean/Sheaf` first found the categorical pattern definition. Broader marked
  source inspection found existing triangle marking, induced marking, initial horn,
  relative sharp mapping and marked pushout-product definitions. They replaced draft
  local copies before delivery. No existing declaration states the present result.

Validation: the source is compiled through the prescribed `scompile.py` wrapper; the
final dry run and delivery also compile this file. The module contains precisely one
`sorry`, as the complete proof of this node's named theorem.

## Second reading by Q160

Author's second reading, not an independent review; the maintainer supplies that review.
I reopened the node and the final declaration and matched each of its clauses in the
table above. This found and repaired a size defect in the draft (all isomorphic
representatives of J were replaced by the small displayed set) and removed duplicated
marking and mapping definitions found by the broader searches. The product clause now
asserts existence of its actual pushout representative as well as the assertion for
every representative. The mapping conversion preserves exactly the over-C equation,
without forgetting either marking or replacing it by an arbitrary comparison map.
The point pattern has no cone data, and the C2 final-cone equation fixes the prescribed
base cone exactly. There is no added hypothesis and no dropped generator or edge case.
