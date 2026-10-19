## Worker report

The module `Sheaf.CategoryTheory.TriangularCofibrantResolution` states
`SSet.TriangularResolution.triangular_cofibrant_resolution`. Its sole theorem has
proof `sorry`. It asserts `Nonempty (FunctorialResolutions Bergner)` for the
Bergner structure of the recorded comparison dependency. The auxiliary records
unpack this one statement; they are not assumptions replacing any conclusion.
`InputMap.id`, `InputMap.comp`, `mixedIndex`, and `mixedAction` contain actual data.
No data are selected from a postponed existence theorem. The theorem docstring
contains all five DAG proof steps and their dependencies.

Source checked: Lurie, HTT, Appendix A.3.3, Definition A.3.3.1, Proposition
A.3.3.2 and Remark A.3.3.5, printed pages 870–871,
https://www.math.ias.edu/~lurie/papers/HTT.pdf; Bergner, math/0406507,
Section 1 generators (C1),(C2) and Section 2 Definition 2.1,
https://arxiv.org/pdf/math/0406507. These supply the projective lifting class,
free cells and Bergner generators, rather than a quoted collage theorem.
The node's explicit five-step proof supplies this auxiliary collage construction.

Hypotheses and conventions, clause by clause:

| Node | Lean |
| --- | --- |
| Fix a universe containing the small object sets and mapping simplices | Explicit `universe u`; `U V : Type u`, `Fixed`, `SCat.{u}`, `SSet.{u}`. The categories of such data live one universe higher. |
| Small simplicial categories, Bergner model structure | Existing `Fixed`, `bundle`, `EnrichedFunctor`, and `BergnerModelData.{u}`. The latter is a parameter selecting the structure already asserted by the comparison dependency, not an extra mathematical condition. |
| Disjoint small sets U,V | `Input.U`, `Input.V`, and the labelled disjoint union `U ⊕ V`. No separate pairwise-disjointness hypothesis is needed for labelled blocks. |
| D on U⊔V | `Input.D : Fixed (U ⊕ V)`. |
| Reverse mapping sets empty | `Input.reverse_empty`, with `IsEmpty` in every simplicial degree. This is precisely the empty presheaf condition, allowing any representation of the empty simplicial set. |
| Diagonal categories C_U,C_V | `Input.A : Fixed U`, `Input.B : Fixed V`. |
| q_U,q_V identity on the objects of D_U,D_V | `qU : bundle A ⟶ bundle D`, `qV : bundle B ⟶ bundle D`, with `qU_obj = Sum.inl` and `qV_obj = Sum.inr` pointwise. A functor with this object map uniquely factors through the indicated full subcategory; writing it into D does not add or remove data. |
| Each q is a local trivial Kan fibration | `qU_trivial`, `qV_trivial`, each `∀ x y, modelCategoryQuillen.I.rlp (q.map x y)`. The recorded Kan–Quillen theorem identifies this all-boundary lifting class, including dimension zero, with trivial Kan fibrations. |
| C_U,C_V Bergner cofibrant | `A_cofibrant`, `B_cofibrant`: the Bergner cofibration predicate on the actual maps `fromEmpty (bundle A/B)`. No arbitrary initial map is assumed. |

Conclusions, clause by clause:

| Node | Lean |
| --- | --- |
| Enriched bimodule M : C_Uᵒᵖ×C_V → sSet | `Resolution.M`, on `mixedIndex d`, the existing coordinatewise product `MarkedCone.productIndex (oppositeCategory (bundle d.A)) (bundle d.B)`. |
| M projectively cofibrant | `M_cofibrant`: for every initial diagram X and its map i to M, `projectiveCof (mixedIndex d) i`. This reuses the existing class defined as the left lifting class of objectwise weak equivalences and Kan fibrations. The established diagram category has an initial object; quantifying over its presentations avoids making an arbitrary initial-object choice. |
| Mixed mapping objects of the collage are M | `mixed_value : M.obj x = C.Hom (inl x.1.unop) (inr x.2)`. These are equalities of whole simplicial sets. |
| Retain exactly C_U,C_V on the diagonals | `diagonalU`, `diagonalV` identify the diagonal Hom objects with the prescribed ones; `iU_obj`, `iV_obj` fix object labels, and `iU_map`, `iV_map` identify each inclusion mapping map with the identity (heterogeneous equality only transports the fixed endpoints). Their enriched functor axioms therefore identify the units and compositions as well, not just the Hom objects. |
| Reverse Hom objects empty | `Resolution.reverse_empty` in every degree. |
| Composition given by the two commuting module actions | `mixedAction` is explicitly precomposition followed by postcomposition in C, with only equality transports on its diagonal factors. `mixed_action` identifies the uncurried full simplicial M action with that map. Because C is an actual enrichment, its associativity and unit laws impose the commuting unital actions. Conversely all composable words have at most one mixed arrow, so these equations specify exactly the collage. |
| Natural augmentation M(u,v) → D(u,v), with target actions restricted along q_U,q_V | It is the explicit composite `eqToHom (mixed_value (op u,v)) ≫ q.map (inl u) (inr v)`. `q : C ⟶ d.D` fixes objects by the existing fixed-object category; its enriched functor laws and `q_left`, `q_right` impose naturality for exactly the two prescribed restricted actions. `q_trivial` applied to the mixed pair, transported by `mixed_value`, makes this composite a trivial Kan fibration. Thus neither a freely chosen map nor an independently chosen action is substituted for the augmentation. |
| C Bergner cofibrant | `C_cofibrant`, the Bergner cofibration class evaluated on `fromEmpty (bundle C)`. |
| Both full inclusions are Bergner cofibrations | `iU_cofibration`, `iV_cofibration` for those same inclusions; the preceding identity-on-Hom conditions make them full. |
| C → D extends q_U,q_V and is local trivial | `q_left`, `q_right` are equalities of enriched functors; `q_trivial` quantifies over every pair of sum objects. |
| Each covariant row M(u,-) projectively cofibrant | `row`, `row_value`, `row_action` specify the whole row functor with postcomposition by C_V; `row_cofibrant` uses the same projective lifting class. The value equations identify its objects with the mixed module, and its action equations identify it with the restriction of M. |
| Each contravariant column M(-,v) projectively cofibrant | `column` is indexed by `oppositeCategory (bundle d.A)`; `column_value`, `column_action` specify precomposition, including the necessary braiding; `column_cofibrant` is the projective initial-map condition. |
| Choices functorial for compatible block-preserving maps | `InputMap` gives the base functor and both diagonal functors with block-object equations and the two commuting triangles. `FunctorialResolutions.obj` chooses an actual Resolution simultaneously for each input; `map` extends its diagonal maps (`map_left`, `map_right`) over the base (`map_over`); `map_id`, `map_comp` require strict identity and composition laws. The mixed components of these enriched functors give the required natural maps of bimodules. |
| Object functions within blocks need not be injective | `InputMap.left`, `InputMap.right` have arbitrary object functions; there are no injectivity binders. |
| Empty blocks, empty mixed mapping sets, no local Kan condition | No `Nonempty`, nonemptiness of mapping sets, `KanComplex`, `IsLocallyKan`, or fibrancy assumptions occur. |

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.CoherentNerveComparison`:
  `CategoryTheory.BergnerModelData`, whose actual model-category structure and
  weak-equivalence/fibration/cofibration characterizations were read. The main
  comparison statement and its other definitions are imported through this module.
- `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`:
  `CategoryTheory.simplicial_projective_model_calculus`,
  `SimplicialDiagramEnrichment`, `ProjectiveSimplicialModelStructure`, and their
  enriched diagram and evaluation/free-diagram signatures and docstrings were read.
  The statement uses the identical projective lifting class in the concrete existing
  enriched-functor category below, rather than copying this model structure.
- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`:
  `SSet.Bergner.Fixed`, `FixedHom`, `fixedCategory`, `bundle`, `bundleMap`,
  `emptyCat`, `fromEmpty`; these keep fixed-object maps literally identity on objects.
- `Sheaf.AlgebraicTopology.UnmarkedStraighteningQuillen`:
  `SSet.UnmarkedStraightening.Diagram`, `DiagramHom`, `DiagramHom.app`,
  `diagramCategory`, `projectiveWeak`, `projectiveFib`, `projectiveCof`,
  `oppositeCategory`. Arrows are genuine unit-graded enriched transformations,
  not merely natural transformations of underlying ordinary functors.
- `Sheaf.AlgebraicTopology.MarkedConeExternalProduct`:
  `SSet.MarkedCone.productEnrichment`, `productIndex`; the full coordinatewise
  enrichment and its laws were read. No marked cone comparison is assumed here.
- Proof-only imports are exactly the recorded modules for
  `SSet.Bergner.fixed_object_free_arrow_adjunction`,
  `SSet.Bergner.fixed_object_simplicial_free_calculus`,
  `SSet.KanQuillen.right_proper_kan_quillen`, and
  `CategoryTheory.SmallObject.functorialFactorizationData` (Mathlib match), with
  its `IsCardinalForSmallObjectArgument` assumptions and cellular/retract conclusions.

The three additional statement dependencies are already-landed owning nodes
`lem-coef-simplicial-interval-lifting`,
`lem-coef-unmarked-straightening-quillen`, and
`lem-coef-marked-cone-external-product`. This records reuse of the fixed-object
category, enriched transformations/projective class, and enriched product. A
read-only traversal of their statement/proof dependencies found no path back to
this item, hence adding them creates no cycle. Their files and records are not changed.
No new independent notion, dependency repair module or statement correction is needed.

Edge cases checked before writing and in the final reading:

1. If either block is empty, the mixed index is empty, its diagrams have the
   unique empty family, and the row/column conditions indexed by the empty block
   are empty families. C has only the other prescribed diagonal. If both blocks
   are empty, C and D have no objects. No hypothesis excludes these cases.
2. If a mixed Hom is empty, its inverse image under an augmentation to it must
   also be empty. Boundary lifting has no forbidden existence condition: for
   dimension zero the lower simplex into the empty target does not exist.
3. Singleton blocks retain arbitrary endomorphism simplicial sets, not just their
   identity vertices. The mixed action formula uses the two complete Hom factors
   in the order `C_U(u',u)`, mixed arrow, `C_V(v,v')`.
4. Noninjective block maps are permitted by all InputMap fields. Identities and
   compositions are formed with their actual object functions, so repeated
   endpoint images do not create an artificial injectivity requirement.
5. The use of degreewise emptiness, all-boundary lifting and full enriched
   functor equations requires no mapping object to be Kan.

Searches for existing declarations:

- `msearch.py leansearch`, query “Simplicial category two block collage cofibrant
  replacement relative to full diagonal categories”: eight hits, including
  `CategoryTheory.SimplicialCategory` and Kan–Quillen monomorphism/cofibration
  facts; none states the relative two-block resolution.
- `msearch.py leanfinder`, query “A cofibrant simplicial bimodule has a Bergner
  cofibrant two-block collage”: eight generic bifibrant/cofibrant-object and
  coproduct-inclusion results; none has the mixed-module, row/column, relative
  diagonal and change-of-object-set clauses.
- `msearch.py loogle`, query `EnrichedFunctor, EnrichedNatTrans`: no hits;
  the service reported unknown identifier `EnrichedFunctor`. Directly reading
  Mathlib `CategoryTheory/Enriched/Basic.lean` and `Enriched/Opposite.lean`
  supplied the actual signatures instead.
- `msearch.py grep`, query `collage|Bergner|bimodule`, subdirectory
  `CategoryTheory/Enriched`: zero hits.
- `rg` of upstream `WeilConjectures` for the item id, `collage`, `Collage`,
  `triangular_cofibrant_resolution`, and `TriangularResolution`: no matching
  simplicial resolution. Searching Mathlib enriched sources and project sources
  for enriched products located the existing `MarkedCone.productIndex`, used here.
- `rg` of `lean/Sheaf` for `collage|Collage|triangular_cofibrant` and enriched
  cofibrancy found ordinary Grothendieck collages, join-cone weights and the
  projective classes. The ordinary collages have different objects and actions;
  join-cone cofibrancy is a special case. The concrete enriched diagram category
  and its general projective class were reused. A final name search of Mathlib,
  upstream sources, project sources and `dag/lean_names_upstream.json` found no
  existing `SSet.TriangularResolution` declarations.

Validation: `scompile.py NN lem-coef-triangular-cofibrant-resolution` compiled
both its sandbox form and module-path form successfully, with no errors or
warnings. Every variable and universe is explicitly bound; no line exceeds 100
characters. The only postponed theorem is the named main theorem. The original
natural-language statement, proof steps and proof dependencies are unchanged.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
