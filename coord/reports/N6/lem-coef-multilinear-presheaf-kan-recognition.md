## Worker report

N6 states `lem-coef-multilinear-presheaf-kan-recognition` in
`lean/Sheaf/CategoryTheory/MultilinearPresheafKanRecognition.lean`, namespace
`SSet.Enhanced.MultilinearKan`. The node's natural-language statement is unchanged.
All definitions have actual data. All four theorems have `sorry` as their whole proof.
The three auxiliary theorems are the well-definedness proofs for the external product
already defined in this node: `product_kan`, `productSimplexMap_laws`, and
`productSimplex_naturality`. Their docstrings give their complete coordinate proofs.
The main theorem's docstring carries all seven proof steps and names their DAG dependencies.
No helper is an independent mathematical notion added to the DAG: these declarations
spell out this node's external product, its canonical representable restriction, and
its mapping-space comparison, as authorized by the helper-interface update.

Clause-by-clause correspondence:

- The small universe is explicit `u`. Each `A i` and `D` is `SSet.{u}`, with
  `[∀ i, Quasicategory (A i)]` and `[Quasicategory D]`. `r : ℕ` and `Fin r` include
  every finite arity, including zero. The presheaf categories and coherent parameter
  categories live in `u + 1`; space values stay in `u`. There is no identification
  of the small universe with the presheaf universe.
- `product A` assembles the existing Mathlib `Types.productLimitCone` degreewise;
  `projection` uses that cone's actual projection. `t : product A ⟶ D` is an
  arbitrary simplicial map. Thus it is the node's coherent functor, with no condition
  concerning preservation of limits or colimits in the small categories.
- `infinityPresheaves` and `infinityYoneda` are the dependency's actual constructed
  definitions, unchanged. `yonedaTuple A` is the tuple of these maps after the canonical
  degreewise universe lift. `E` has domain the product of these presheaf categories and
  codomain `infinityPresheaves D`.
- `hE : SeparatelyCocontinuous A E` quantifies over each variable, every choice of other
  input presheaves, every small simplicial indexing shape `K : SSet.{u}`, each coherent
  diagram on its lift, and every colimiting cocone. Its conclusion uses the existing
  `mappedCocone` construction, fixing the entire image cocone, not just its apex.
  `insertCoordinate` has identity projection in the variable coordinate and the prescribed
  constant presheaves in the other coordinates. Empty `K` is included.
- `e` is a vertex of the full right-pinched transformation space from `E` on the tuple
  of representables to `y_D` after `t`. `he` asserts it is an equivalence edge in the
  entire functor simplicial set. Its orientation is exactly `E(y(a)) ≃ y_D(t(a))`.
- `kanProduct`, `productSimplexMap`, `productSimplex`, and `spaceProduct` construct the
  finite product of small spaces on every coherent simplex. The maps are the tuples
  of the uncurried factor maps. `coordinateEvaluation` evaluates `F_i` at `x_i`, and
  `externalProduct` curries their finite product. Its value is literally the degreewise
  product of the `F_i(x_i)`, with the actual factor action on all enriched maps.
- `restriction t` is actual internal-Hom precomposition by the lift of `t.op`.
  It is not an assumed functor or an arbitrary map.
- `transformations` is just an abbreviation of the dependency's right-pinched
  `mappingSpace` in the internal functor simplicial set. The unit is the source
  coordinate `z.val.1` of the concluded homotopy-fiber vertex. Its type is exactly a
  coherent transformation from `externalProduct A` to `E ≫ restriction t`.
- The specified restriction is `b`. `HasRepresentableAction A t b` fixes its full
  coherence through a triangle `y_C → externalProduct(y(a)) → t*y_D(t(a))` whose
  long edge is the actual Hom action of `t`. `HasProductHomFormula` specifies the
  first edge by the tuple of actual rigidification maps of the projections.
  `HasHomFormula` specifies the long edge by the actual rigidification map of `t`,
  followed by singular realization on Hom objects. `BridgeFormula` fixes every object
  and every enriched map of every cylinder simplex, for all `n,s,a,l`. The 0-to-1 maps
  are `mixedMap`, applying the actual Hom map followed by target pre/postcomposition.
  The 1-to-0 path simplicial set is empty by monotonicity of `l`, hence its map is unique.
  In particular the restriction sends each tuple `u_i` to `t(u_i)`. The formulas also
  specify higher simplices; there is no replacement by equality on components.
- `restrictionMap` is the existing `mappingSpaceMap` of actual precomposition by
  `yonedaTuple`. `normalizedRestrictionMap` then postcomposes with the actual image
  of the specified `e`, using the already recorded canonical composition class.
  `IsContractible (homotopyFiber ... b)` is precisely the space of extensions with a
  specified restriction homotopy. The concluded vertex `z` gives an extension and
  that homotopy; the latter is not discarded. Contractibility is weak contractibility
  in the dependency's exact convention.
- `unitComponent` evaluates the same unit, using the existing counit/evaluation identity
  `PointwiseYoneda.evaluation_diagramVertex` for its endpoint transports. `comparison`
  sends `v` to `restriction(t)(v)` composed with that component, using `HC.composition`.
  The latter equals the recorded canonical composition by the field of `HomBifunctorData`.
  The first conjunct of `IsCoherentKanUnit` asserts this actual map is a weak equivalence
  for every input tuple `F` and every `H`, giving the displayed whole mapping-space
  equivalence and therefore the mapping-space definition of the left Kan extension.
- The second conjunct of `IsCoherentKanUnit` supplies an equivalence edge `α` in the full
  functor simplicial set on `X.op ⊗ P(D)`, between the two actual Hom bifunctors.
  Its transported components are homotopic to `comparison` through the recorded
  `valueComparison` maps. Thus the equivalence is coherent in both `F` and `H`, including
  every mixed higher simplex; an unrelated equivalence of spaces would not satisfy it.
- `hC,hD,hF,HC,HD` are existential conclusions giving intrinsic quasicategory and
  normalized Hom structures of the already constructed presheaf categories. They are
  not hypotheses. They allow use of existing canonical mapping composition without
  introducing a second construction or asking callers for stronger assumptions.
- For `r=0`, the degreewise product of an empty family is the one-element function type.
  `spaceProduct 0` has the point Kan complex as every object, `externalProduct` is the
  point presheaf on the terminal product source, and `hE` has no variable to quantify
  over. The specified `e` still asserts `E(*) ≃ y_D(t(*))`. `HasProductHomFormula` uses
  the empty tuple into the point. No `r>0` or nonempty-index premise is present.
- There are no hypotheses of filteredness, existence of small-category colimits, or
  nonemptiness of any input presheaf. Zero/empty-valued Kan complexes and empty density
  shapes are retained by every construction and every colimit quantifier.

Dependency declarations actually used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `mappingSpace`, `mappingSpaceMap`,
  `diagramVertex`, `evaluation`, `coconeCategory`, `IsColimiting`,
  `IsWeakHomotopyEquivalence`, `IsEquivalenceEdge`, `homotopyFiber`, `IsContractible`.
- `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`: `Kan`, `infinityCategory`,
  `singularRealization`, `mappedCocone`; the actual Kan enrichment is reused.
- `Sheaf.CategoryTheory.InfinityPresheafYoneda`: `infinityPresheaves`, `infinityYoneda`,
  `YonedaSimplex`, `yonedaReverse`, `yonedaPairSimplex`, `yonedaRigidSimplex`.
  The last definitions already use the published subset-poset rigidification;
  `SSet.Pinched.rigidification` is reused for the normalized Hom action.
- `Sheaf.CategoryTheory.InfinityHomBifunctorFunctoriality`: `HomBifunctorData`,
  `canonicalHomComposition`, `homSpaceCategory`, `homValue`, `homSpaceEdgeSource`,
  `homSpaceEdgeTarget`, `homSpaceEdgeTransport`. Its landed node is added to `stmt_deps`.
- `Sheaf.CategoryTheory.InfinityPointwiseYonedaEvaluation`:
  `PointwiseYoneda.evaluation_diagramVertex`. Its landed node is added to `stmt_deps`
  solely to reuse this existing endpoint identity rather than duplicate it.
- Mathlib `Types.productLimitCone`, the simplicial and cartesian closed constructions,
  the existing enriched-functor structure, and the ordinary `Quasicategory` predicate.
- Proof-only imports: `Sheaf.CategoryTheory.SpaceYonedaDensity` and
  `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`, both recorded proof dependencies.
  The other proof dependency nodes have no recorded Lean module in the inspected DAG;
  none is invented or copied merely to import a nonexistent theorem.

Edge checks: `r=0`; `r=1,t=id`; terminal `D`; an empty `A_i`; empty-valued inputs;
empty colimit shapes; degree-zero and degenerate coherent simplices; and varying small
universe `u`. The product Kan filler proof works for empty factors and empty index
sets. In the cylinder formula monotone parameters exclude 1-to-0 nonempty paths.
No field is vacuous beyond the explicitly intended empty arity.

Searches actually run with `msearch.py N6 lem-coef-multilinear-presheaf-kan-recognition`:

- LeanFinder: "A separately colimit preserving extension of Yoneda presheaves is left
  Kan extension of external products for quasicategories". Eight hits, headed by
  `CategoryTheory.Presheaf.isLeftKanExtension_of_preservesColimits` and the ordinary
  external-product Kan-extension lemmas; no quasicategorical mapping-space statement.
- Loogle: `"yoneda", "IsLeftKanExtension"`. Five hits, the ordinary `Type`-valued
  presheaf/Yoneda Kan-extension instances and characterizations.
- Mathlib grep in `CategoryTheory`:
  `multilinear|externalProduct.*[Kk]an|presheaf.*[Kk]an`. One import hit in DayConvolution;
  no declaration of this theorem.
- LeanSearch: "Multilinear extension of space valued Yoneda presheaves is left Kan
  extension with contractible space of coherent units". Eight hits, ordinary functor
  Kan-extension universal properties and `CategoryTheory.Presheaf` extension lemmas.
- Read `Mathlib/CategoryTheory/Limits/Presheaf.lean:361` and
  `Mathlib/CategoryTheory/Monoidal/ExternalProduct/KanExtension.lean:50` with full
  signatures/docstrings: they require ordinary categories and ordinary presheaves,
  and do not specialize to this quasicategorical statement.
- Direct `rg` in `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for multilinear presheaf Kan recognition, external products, the node id, and the
  proposed full namespace/declaration. No match for this theorem or coherent external
  product. Upstream `AlgebraicGeometry.ProEtale.externalProduct` is a different derived
  sheaf construction. Existing pointwise-Yoneda and intermediate-presheaf Kan modules
  were read and reused where they supply interfaces.
- Mathlib's product source was inspected: `Types.productLimitCone` gives the literal
  function-type product; `Limits.piObjIso` concerns the abstract chosen categorical
  product. The former is reused directly in this degreewise simplicial model.

Sources read online: [HA, Remark the project server, printed p. 711](https://www.math.ias.edu/~lurie/papers/HA.pdf)
and [HTT, Lemmas the project server--the project server, Theorem the project server, and Proposition the project server,
printed pp. 321--324 and 413--414](https://www.math.ias.edu/~lurie/papers/highertopoi.pdf).
The latter proof explicitly treats zero factors. The node is correctly described as
an agent-formulated recognition lemma, not a verbatim theorem from those sources.
WANTED: archive HA and HTT in `literature/`; neither was found there by filename search.

No statement correction, disputed statement, new DAG node, or dependency-module repair
is needed. All writes are confined to the authorized sandbox; compilation and delivery
use only the prescribed wrappers.

## Second reading by N6

Author's final self-check, with the node and final module open; independent review is
left to the maintainer as required by this worker brief. No independent reader or
sub-agent was started.

The initial draft's representable normalization checked only arrow components. It was
replaced before delivery by `BridgeFormula`, `HasHomFormula`, and
`HasProductHomFormula` on every coherent simplex and the full triangle in
`HasRepresentableAction`. Thus the canonical restriction retains its higher coherence.
The product now explicitly reuses Mathlib's standard type-product cone, with its actual
projections. The final comparison uses the unit extracted from the same normalized
restriction fiber, and the natural equivalence is on the whole two-variable functor
category. The signature has no added mathematical premise, no omitted zero-arity case,
and no replacement of a canonical map by an arbitrary one. The node record lists every
helper declaration and reproduces the main signature verbatim.

Validation: `scompile.py` compiled the module cleanly as sandbox and library module;
the final delivery dry run and push results are recorded by the prescribed delivery tool.
