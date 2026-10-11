## Worker report

The module `Sheaf.AlgebraicGeometry.NagataMorphismDescent` defines the displayed
choice-dependent construction, not an arbitrary witness to morphism descent.
`NagataMorphismDescentData` records the choices. `stages` computes F, `stage` computes
u(F), `nagataMorphismDescentGluedMap` glues the transported local maps, and
`nagataMorphismDescent` bundles that map over the selected base stage. No definition
has sorry data. All five auxiliary theorem proofs are sorry, with natural-language
proofs and this definition node's blueprint identifier in their docstrings. They are
coefficient_le_stage, base_le_stage, charts_cover, charts_agree, and
nagataMorphismDescentGluedMap_over. They are the well-definedness proofs needed by
this definition, not proofs of the subsequent morphism-descends node.

Source read: the blueprint's original `def-nagata-morphism-descent.md`, order 353,
read from the server's literature copy (the local literature directory has only the
catalogues). Its construction chooses affine target charts, descends their opens
and ring maps, includes overlap equality stages, and glues through comparison maps.
The stage-1 expanded statement supplies the detailed choice data rendered here.
There is no statement correction or disputed statement.

Hypotheses and clauses, in the node's order:

- Nonempty directed index set: `I : Type u`, `[Preorder I]`, `[Nonempty I]`,
  `[IsDirected I (· ≤ ·)]`. Schemes and the index have the same universe u,
  as required by the project's inverse-limit convention.
- Inverse system with affine transitions and specified limit: `D : Iᵒᵖ ⥤ Scheme`,
  `c : Cone D`, `hc : IsLimit c`, and the instance for every `IsAffineHom (D.map f)`.
- Base index and qcqs base: `i₀`, `CompactSpace (D.obj (op i₀))`,
  `QuasiSeparatedSpace (D.obj (op i₀))`.
- Finite-presentation source and target: `p : X₀ ⟶ D.obj (op i₀)` and `q : Y₀ ⟶ ...`,
  each with `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated`.
  Explicit qcqs instances on X₀ are the consequence used by open descent, not an
  extra geometric restriction (finite presentation over a qcqs base implies them).
- X_lambda, Y_lambda, X, Y and their canonical maps: `baseChangeDiagram D p/q` and
  `baseChangeCone D c p/q`; no replacement definition of base change.
- The given S-morphism: `phi` between the two cone vertices and `data.limitOver`,
  the commuting equation for the two second pullback projections.
- Chosen finite affine base cover: `J`, `T`, `affineT`, `coverT`.
- Chosen finite affine target cover over it: dependent `K`, `V`, `affineV`, `coverV`,
  `targetToBase`, `targetOver`. `finitePresentation` is the ring-map finite-presentation
  predicate on the chart map's contravariant `appTop`.
- Chosen finite R_j-generators and defining relations: `n`, `m`, and
  `presentation : Algebra.Presentation ... (Fin n) (Fin m)`, with the algebra instance
  explicitly induced by targetToBase.appTop. `generators_eq` and `relations_eq`
  identify the displayed generator and relation families with this presentation.
  This is exactly Mathlib's finite polynomial presentation, including generation
  and generation of its kernel by the listed relations.
- W_jk^infinity and its compactness: `W`, `W_eq`, `compactW`. W_eq is the inverse
  image of the inverse image of V_jk under phi and the target's first projection.
- The chosen open-descent construction: `a`, `A`, `affineA`, `coverA`, `b`,
  `basicSection`, `basicPresentation`, `openLiftStage`, `openLiftGE`, `openLift`,
  `openLift_eq`. `openSelected` equates the whole dependent triple
  `(openStage, openGE, descended)` with the dependency `nagataQCOpenDescent`.
  Thus these are that construction's choices, not unrelated descended opens.
  Its compactness and inverse-image assertions are supplied by the recorded
  dependency `nagataQCOpenDescent_spec`, as explained in charts_cover's docstring.
- Intersection with the inverse image of T_j and finite affine refinement:
  `coverU` says the union of U is descended intersected with the inverse image of
  T_j along X_lambda → S_lambda → S_i₀; `L`, `U`, `affineU` supply the finite charts.
- Generator lifts at a later stage: `generatorStage`, `generatorGE`, `generatorLift`;
  `limitChart_eq`, `limitToGenerator_eq`, `limitMap_eq`, `generatorLift_eq` identify
  their limit images with phi's images of the target generators.
- A still later stage where all relations vanish: `coefficientStage`,
  `coefficientGE`, `coefficientLift`, `coefficientTransition_eq`, `coefficientLift_eq`,
  and `localRelations`. `localGenerators` says localMap.appTop sends the given
  generators to these transported lifts; `localOver` expresses base compatibility.
  `localMap` therefore is the map from the chosen affine ring data into V_jk.
  These are explicit witnesses selected using finite-data and colimit injectivity,
  just as the node selects witnesses before defining its final morphism.
- Rebase at lambda'=u(F₀): `F₀_eq` is the finite set of the base and all previously
  selected open, generator, and relation stages; `prime_eq` uses exactly
  `directedFiniteUpperBound i₀ d r F₀`. `primeGE` and `chartPrimeGE` are the
  upper-bound proofs. The chart `chart_eq` is exactly the inverse image of U under
  the base-change transition. `toCoefficient_eq`, `mapAt_fst`, `mapAt_snd` fix the
  canonical transport of localMap to every subsequent stage, by both projections.
  These comparison maps are unique by the open immersion and pullback universal
  properties; recording them does not add independent choices of morphisms.
- The finite union-cover equality stage: `unionOpen_eq` is the union of transported
  U (equal to the union of the W by coverU); `compactUnion` and `unionLimit_eq`
  provide the stated compactness and equality of limit inverse images.
  `unionSelected` sets unionStage to `nagataQCOpenEqualityStage` with base prime,
  source X_prime, and exactly unionOpen and top. The original D,c are retained:
  the dependency itself restricts to the indexing tail above prime by Over.
- Each overlap and its two maps: `overlap_eq` is the intersection of the two
  transported charts; `overlapLeft_eq`, `overlapRight_eq` identify the restricted
  chart maps. `overlapOverLeft/Right` give their base equations. Compactness,
  quasi-separatedness and finite presentation of this source open are recorded
  as the proof/instance fields needed by the dependency.
- The selected overlap-equality construction: `overlapData` has exactly the
  recorded `NagataMorphismEqualityStageData` type, with base prime, overlap source,
  Y_prime target, and the displayed two morphisms. In particular this dependency
  record includes their equal limit base changes and all its finite chart and
  coefficient equality choices. `overlapSelected` sets each overlapStage to
  `nagataMorphismEqualityStage overlapData`, not an arbitrary equality bound.
- F and lambda_phi: `stages` is F₀ union `{prime,unionStage}` union the finite image
  of every pair's overlapStage; `stage` is `directedFiniteUpperBound i₀ d r stages`.
  The node's fixed selected bounds and auxiliary order are `d`, `hd`, `r`.
- Covering and agreement at lambda_phi: `charts_cover` and `charts_agree` are the
  named postponed proof obligations, using the two eventual-equality dependencies
  and `le_directedFiniteUpperBound`. They are not assumed as choice-data fields.
- The resulting morphism: `nagataMorphismDescentGluedMap` calls
  `Scheme.openCoverOfIsOpenCover` and `Scheme.Cover.glueMorphisms` on those exact
  transported charts/maps at `data.stage`. `nagataMorphismDescent` returns the same
  stage and map as an `Over` morphism using the named over-base proof.
  Identification of its base change with phi is the subsequent
  `lemma-nagata-morphism-descends` node; the choices needed for that proof are all
  retained, notably generatorLift_eq, localGenerators and the comparison maps.
- Dependence on covers, lifts, relations and equality witnesses: they are explicit
  fields of the data argument and determine F and the local glued map.

Dependency declarations read (full signatures and docstrings):

- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`:
  `AlgebraicGeometry.baseChangeDiagram`, `baseChangeCone`.
- `Sheaf.Order.DirectedFiniteUpperBound`: `directedFiniteUpperBound`,
  `le_directedFiniteUpperBound`.
- `Sheaf.AlgebraicGeometry.NagataQCOpenDescent`: `nagataQCOpenDescent`,
  `nagataQCOpenDescent_limit_chart_le`; its full chosen-lift API is used in openSelected.
- `Sheaf.AlgebraicGeometry.NagataQCOpenDescentSpec`: `nagataQCOpenDescent_spec`.
- `Sheaf.AlgebraicGeometry.NagataQCOpenEqualityStage`: `nagataQCOpenEqualityStage`.
- `Sheaf.AlgebraicGeometry.NagataQCOpenEqEventually`: `nagataQCOpenEqEventually`.
- `Sheaf.AlgebraicGeometry.NagataMorphismEqualityStage`:
  `NagataMorphismEqualityStageData`, `nagataMorphismEqualityStage`.
- `Sheaf.AlgebraicGeometry.NagataMorphismEqEventually`: `nagataMorphismEqEventually`.
- `Sheaf.RingTheory.FilteredColimitFiniteData`: `CommRingCat.exists_finite_data_stage`;
  this theorem justifies choosing the generatorLift witnesses, rather than computing
  chosen witnesses from arbitrary classical choice in this definition.
- Mathlib `AlgebraicGeometry/AffineTransitionLimit`:
  `nonempty_isColimit_Γ_mapCocone`, `exists_appTop_π_eq_of_isLimit`,
  `exists_appTop_map_eq_zero_of_isLimit`: existence of generator/vanishing witnesses.
- Mathlib `CategoryTheory/Limits/ConcreteCategory/Basic`:
  `Concrete.isColimit_exists_rep`, `Concrete.isColimit_rep_eq_iff_exists`, with
  `CommRingCat.FilteredColimits.forget_preservesFilteredColimits` from
  `Algebra/Category/Ring/FilteredColimits`: the same elementwise existence/equality
  inputs. No private versions of these notions are introduced.

Edge cases checked: Fin 0 covers and Fin 0 generator/relation lists are permitted;
empty base, target or source imposes no Nonempty chart condition. An empty source
has the empty cover and its unique gluing map. Arbitrary cardinalities of I are
allowed within the schemes universe. Nonempty I is required even for empty schemes,
as in the node. The auxiliary order r remains explicit, separate from the preorder
on I; no commutativity or associativity of d is assumed. F always contains i₀, prime,
and unionStage, even if there are no overlaps. Relations use coefficients in the
actual chart ring R_j, not integer coefficients that would forget base compatibility.
The target morphism is explicitly bundled over S_stage. No separated-target or
Noetherian-base hypothesis has been added.

Searches made:

- leanfinder, `finite stage model of morphism by affine chart gluing generator lifts
  relations`: 8 hits, principally `ExistsHomHomCompEqCompAux.h𝒰S`, `.𝒰D`, open covers
  and affine-base-change infrastructure; no matching selected construction.
- loogle, `Scheme.Cover.glueMorphisms, AlgebraicGeometry.baseChangeDiagram`: no hits;
  the unqualified Scheme identifier was not resolved. Direct source reading located
  `AlgebraicGeometry.Scheme.Cover.glueMorphisms` in Mathlib Gluing.
- grep (msearch), `glueMorphisms|MorphismDescent|morphismDescent`, AlgebraicGeometry:
  25 hits on general gluing and its users; no morphism-descent construction.
- leansearch, `finite stage morphism descended by finite affine covers generator
  lifts and gluing`: unavailable, Internal Server Error.
- rg over upstream WeilConjectures, landed Sheaf and dag/lean_names_upstream.json:
  `morphismDescent|MorphismDescent|def-nagata-morphism-descent`: no declaration.
  A broader Nagata search found the existing equality/open-descent dependencies,
  which are used above. No upstream overlap applies to these new names.

Validation: local file compile passed with no warnings. The final server compile
and mechanical preflight are run by deliver2.py --no-push; the second reader supplies
its own independent reading and performs delivery.

## Second reading by H1

I reread the node statement, its source place (blueprint node order 353), and the
complete declaration in `Sheaf.AlgebraicGeometry.NagataMorphismDescent`.
The index data is rendered by the universe-`u` `I`, `[Preorder I]`,
`[Nonempty I]`, `[IsDirected I (· ≤ ·)]`, and explicit auxiliary `r : LinearOrder I`;
the latter is the required ordering argument of `directedFiniteUpperBound`.  The
inverse system, affine transition instances, cone and limit are `D`, `c`, `hc`, and
the displayed `IsAffineHom` instance.  The base stage and qcqs assumptions are
`i₀`, `CompactSpace`, and `QuasiSeparatedSpace`; the finite-presentation source and
target maps and their qc/qs instances are `p`, `q`, and the four morphism classes.
`baseChangeDiagram` and `baseChangeCone` render all six base changes and comparison
maps, while `phi` and `limitOver` render the given S-morphism and its compatibility.

The finite affine base and target covers are `J`, `T`, `affineT`, `coverT`, `K`,
`V`, `affineV`, `coverV`, `targetToBase`, and `targetOver`.  The finite-presented
algebra, generators, and relations are exactly `finitePresentation`, `n`, `m`,
`presentation`, `generators`, `generators_eq`, `relations`, and `relations_eq`.
`W`, `W_eq`, and `compactW` render the inverse-image opens and compactness.  The
full selected open-descent choices are the fields `a` through `openSelected`; `L`,
`U`, `affineU`, and `coverU` render the affine refinement over the base chart.
Generator and relation lifting, transport, and the local maps are rendered by
`generatorStage` through `localRelations`, including the displayed equations.
`F₀`, `prime`, `prime_eq`, `primeGE`, `chartPrimeGE`, `chart`, `mapAt`, and the
comparison equations render the rebase and canonical transports.  `unionOpen`,
`unionSelected`, and the compactness/equality fields render the finite union stage.
The overlap opens, restricted maps, over-base equations, and all required
compactness, separation, finite-presentation, quasi-compactness, and
quasi-separatedness hypotheses are rendered by `overlap` through `overlapData`;
`overlapSelected` fixes the exact equality-stage construction.  Finally `stages`
and `stage` compute the prescribed finite upper bound, `charts_cover` and
`charts_agree` are the named postponed proof obligations, and
`nagataMorphismDescentGluedMap`/`nagataMorphismDescent` perform precisely the
cover gluing and bundling over the selected base stage.

I found no mismatch in object identity, quantifier order, hypotheses, or conclusion
clauses.  In particular, the explicit qc/qs source instances and the auxiliary
linear order are the instances/choice data required by the recorded dependency
declarations and do not alter the finite-presentation or directed-system notions.
No edge case is excluded: `Fin 0` covers and generator/relation lists, empty
schemes and opens, `n = 0`, arbitrary allowed index cardinality, and the required
nonempty index are all admitted by the binders.  The searches recorded in the worker
report were independently checked against Mathlib, upstream `WeilConjectures`, and
landed `Sheaf` declarations; no existing declaration supplies this construction.
No file or node changes were necessary.
