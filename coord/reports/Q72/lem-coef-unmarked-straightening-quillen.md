## Worker report

Stage-2 statement of `lem-coef-unmarked-straightening-quillen` in
`lean/Sheaf/AlgebraicTopology/UnmarkedStraighteningQuillen.lean`. The final theorem
is `SSet.UnmarkedStraightening.unmarked_straightening_quillen`. Only the item's
`lean` field changes. No new nodes or dependency modules are delivered.

The stale stage-1 route note has already been fulfilled on the current base:
the item has the six-step proof, `status: split`, and the 2026-10-17 independent
stage-1 review by NT-cc-Q72-57ff3822f. The maintenance prerequisite repairs are
installed, as described in `coord/reports/maintenance/Q72-unmarked-straightening.md`.
This delivery leaves all three prerequisite nodes and all stage-1 fields alone.
The stage-1 dry-run instruction concerns that completed delivery; this packet is
the stage-2 statement requested by the dispatch brief and uses deliver2.py.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Small simplicial set `S`, small simplicial category `D`, and simplicial
  functor `φ : C[S] → Dᵒᵖ` are exactly `(S : SSet.{u}) (D : SCat.{u})
  (φ : rigidification.obj S ⟶ oppositeCategory D)`. The opposite is Mathlib's
  braided enriched opposite bundled as `SCat`, rather than an opposite of the
  ordinary category of coefficient diagrams. No quasicategory, local Kan,
  nonemptiness or cofibrancy hypothesis is imposed.
- The object `X → S` is `X : Over S`. `conePushout D φ X` is the categorical
  pushout of `C[X] → C[X ⋆ Δ⁰]` and `C[X] → C[S] → Dᵒᵖ`. Its inclusions are
  `coneInclusion` and `baseInclusion`; `coneVertex` is the image of the last
  pure join vertex and `baseObject` the image of `d`.
- `value D φ X d` is precisely that pushout's mapping simplicial set `(d,v)`.
  `valueAction` uses the base inclusion on mapping objects and pushout
  composition. Its tensor factors are reversed once by the Cartesian braiding,
  so the displayed action is covariant in `D` and given by precomposition in
  `Dᵒᵖ`, as required. `valueMap` is the actual pushout map on an arrow over `S`.
- The category of diagrams has Mathlib `EnrichedFunctor SSet D SSet` as its
  object data, wrapped in `Diagram` to use the correct arrow category.
  `DiagramHom.app` is a family of simplicial maps; `naturality` is the equality
  `action F ≫ app = (app ⊗ id) ≫ action G` of full simplicial maps.
  This includes positive-dimensional mapping simplices. Mathlib's
  `EnrichedNatTrans` stores only a natural transformation between ordinary
  `ForgetEnrichment` functors, which is insufficient for this explicitly
  requested action-square equality; it is therefore not used as the Hom type.
- `HasProjectiveModel D` asserts completeness, cocompleteness, and existence
  of a Mathlib `ModelCategory` with its three classes fixed to
  `projectiveWeak`, `projectiveFib`, and `projectiveCof`. These are respectively
  objectwise realization weak equivalences, objectwise all-horn Kan fibrations,
  and the left lifting class of their intersection. Small generating arrow sets
  `I,J` have exactly the specified injective classes and functorial cellular
  factorizations, in the convention of the contravariant-slice node.
  `ProjectivelyFibrant` means every value is a `KanComplex`.
- `IsStraightening D φ L` fixes all object values, all full actions, and all
  arrow maps of the existential left functor. `HEq` only handles the object
  equality transports; it asserts equality of maps, not arbitrary isomorphism.
  `SimplexDescription.equiv` specifies every degree of `U F` by the pair
  `(σ : Δ[n] → S, L(σ) → F)`. Its `projection`, `operator`, and `map` fields
  specify the projection, restriction along every simplex operator, and
  postcomposition along every enriched transformation.
- The existential `adj : L ⊣ U` is normalized by `IsConeAdjunction`: on a
  simplex `z` the adjoint of `f` is `L(z) ≫ f`, with its prescribed base
  simplex. Thus the witnesses are the displayed cone adjunction, with no
  arbitrary choice of an unrelated adjunction or right functor.
- The next two conjuncts assert preservation of monomorphisms as projective
  cofibrations and of monic cone weak equivalences as projective weak
  equivalences. Together with the fixed projective classes these say exactly
  that `L` preserves cofibrations and trivial cofibrations. `contravariantWeak`
  is the categorical-equivalence-of-cones class of the recorded slice node.
- `Bergner.dwyerKanEquivalences φ → ...` is the conditional Quillen-equivalence
  assertion: mappingwise weak homotopy equivalences plus equivalence on `π₀`.
  It quantifies over EVERY `X : Over S`, EVERY objectwise Kan `F`, and EVERY
  actual map `f : L.obj X → F`. The iff uses precisely its adjoint under `adj`.
- The following conjunct says `Enhanced.rightFibration (U.obj F).hom` for every
  projectively fibrant `F`, independently of the Dwyer--Kan condition on `φ`.
- `singQ T` has degree `n` the actual simplicial maps `Qⁿ → T`, with operators
  by precomposition with the recorded `qFunctor`. `fiberIso F s` is a
  simplicial isomorphism from the recorded strict fiber of `U F` to
  `singQ (F(φ(s)))`, for EVERY `F` and vertex `s`. The explicit naturality
  equation uses `Enhanced.fiberMap (U.map f)` and `singQMap (f.app (φ(s)))`.
- `RealizationGenerator`, `RealizationRelation`, `realizationSetoid`, and
  `qRealization` implement the quotient of the coproduct `K_n × Qⁿ` by every
  relation `(K(α)z,q) ∼ (z,Q(α)q)`. The quotient has the actual induced
  simplicial restriction maps; it is not identified with `K` or selected from
  an unproved existence theorem. `qGenerator` is its summand map.
- `PinchedGenerators` supplies canonical construction witnesses, each fixed by
  its normalization: the standard last-vertex cone isomorphism fixes its
  initial face and last vertex; the `Qⁿ ≅ C[Jⁿ](x,y)` identification agrees
  with `PinchedCube.canonicalMap` after the surjective quotient map; and the
  collapsed enriched functor agrees on the uncollapsed simplex with the
  actual cone inclusion. Its endpoints are the coefficient and cone objects.
  `pinchedValueMap` is the resulting map of mapping simplicial sets. These
  witnesses are asserted to exist inside the theorem and are never chosen
  as definition data from it.
- `comparison X s` has source the quotient `|X_s|_Q` and target `(L X)(φ(s))`
  in its explicit `value` encoding. Its equation on EVERY `qGenerator n z`
  says it is `pinchedValueMap` followed by `valueMap` of the ACTUAL fiber
  simplex inclusion `fiberSimplexArrow`. This determines the comparison
  uniquely and rules out an arbitrary map. The final equality says the fiber
  restriction of the adjoint, followed by `fiberIso`, equals `qAdjunct` of
  this comparison followed by the transported component of `f`. It is an
  equality of whole simplicial maps and therefore includes every operator
  relation. No fibrancy is assumed in these last clauses.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence` (realization, components and all
  positive based homotopy groups), and its simplicial-set conventions.
- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`:
  `SSet.Bergner.simplicial_interval_lifting`, which supplies cocompleteness to
  the existing rigidification; `CategoryTheory.CoherentNerve.SCat` is its
  bundled category of small enriched categories.
- `Sheaf.AlgebraicTopology.PinchedCubeLatching`:
  `coherentSimplexUnit`, `rigidification`, `Q`, `qFunctor`, `J`, `pinch`, `x`,
  `y`, `quotientMap`, `canonicalMap`, and `pinched_cube_latching` (including
  the normalized isomorphism and all monotone operators).
- `Sheaf.CategoryTheory.ContravariantSliceModel`:
  `coneExtensionMap`, `IsCategoricalEquivalence`, `IsInjectiveAgainst`,
  `cellProperty`, `fiberMap`, and `contravariant_slice_model`. Read the complete
  statement: monomorphisms, cone weak equivalences, cellular factorizations,
  fibrant right fibrations and fiberwise detection over arbitrary `S`.
  The fibration and fiber interface is `SSet.Enhanced.rightFibration` and
  `fiber`, reexported by that module. No repair of that landed interface is needed.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `right_proper_kan_quillen`; all-horn fibrations are
  `SSet.modelCategoryQuillen.J.rlp`.
- The stated proof dependency
  `Sheaf.AlgebraicTopology.SimplicialPresheafProjectiveModel` is imported
  without `public`. The other proof dependencies have no recorded Lean module
  on this base; their full mathematical assertions remain the node's six-step
  plan and are written in the main theorem's docstring. No identity-base
  theorem is proved by citing the general theorem.

Every universe and variable is explicitly bound (`set_option autoImplicit false`).
All theorem proofs are `sorry`: `coneMap_inclusion`, `pushoutMap_objects`,
`realizationOperator_rel`, `qGenerator_naturality`, `fiberSimplex_comm`, and
`unmarked_straightening_quillen`. Each has its source and a complete natural-
language proof in its docstring, with the item's blueprint tag. The first five
are the named well-definedness/transport proofs needed by the canonical maps
and quotient explicitly introduced in this item's own statement; their data
are all explicit. No definition has data written as `sorry`.

Edge cases checked: empty `S` (the vertex-indexed clauses are empty, but the
model/adjunction clauses remain); empty `D` when a functor `φ` exists; empty
`X`; the constant point base; `n = 0` (the full coend relation and boundary
classes include it, and the cone is `Δ¹`); degenerate and noninjective simplex
operators; non-Kan values of `F` in the strict fiber formula; an arbitrary base
which is not a quasicategory; coefficient mapping sets which are not Kan.
The construction never presupposes an element of any empty object type.

Searches made with the prescribed wrapper on 2026-10-17:

- `leanfinder`: "Unmarked straightening Quillen equivalence for enriched
  simplicial diagrams and contravariant simplicial sets" returned 8 hits:
  ordinary simplicial enrichment, simplicial nerve and thickening, and
  Cat-enrichment of quasicategories. None states this adjunction or theorem.
- `loogle`: `SSet, "straightening"` returned zero hits.
- `grep` in Mathlib `CategoryTheory`: `straighten|unstraighten|EnrichedNatTrans`
  returned only five explanatory references to `EnrichedNatTrans` in
  `Enriched/Basic.lean`. Its full definitions (lines 299--469 and 494--508)
  were read. `GradedNatTrans` has the full enriched equation, whereas the
  ordinary `EnrichedNatTrans` category used here by default does not. The
  wrapped object type and explicit full action-square Hom avoid silently
  changing the statement's category.
- `rg` for the item id, straightening/Quillen, enriched-natural maps and all
  proposed declaration names in `WeilConjectures/` and `lean/Sheaf/` found
  no general unmarked theorem. The existing
  `RightStraighteningFiberComparison.lean` gives the identity-base cone
  construction and cites THIS item in its proof; importing it would create
  a dependency cycle. It is not a statement of the general `φ` theorem.
  The general coefficient pushout here is that construction with the second
  attaching map `C[a] ≫ φ`, exactly as this item's statement prescribes.
- A follow-up `rg` for pinched realization and singular constructions found
  `Sheaf/CategoryTheory/PinchedRigidificationResolution.lean`. Its
  `SSet.Pinched.realization` and `singular` use the separate cosimplicial
  hom-object resolution `SSet.Pinched.resolution`; the current prerequisite
  records instead prescribe the explicit quotient `SSet.PinchedCube.qFunctor`.
  Those are canonically isomorphic models, not the same recorded declaration.
  The present `qRealization` is the explicit coend quotient for the prescribed
  `qFunctor`, and `singQ` uses that same functor. The downstream resolution
  theorem also depends through the right-straightening comparison on this item;
  it cannot supply the prerequisite proof of this theorem. No downstream
  theorem is imported or used to define the comparison.

Source checked directly: HTT PDF at the node's URL, printed pp. 73--77
(§2.2.1, Theorem the project server, §2.2.2 and Remark the project server). The theorem has arbitrary
simplicial `S` and arbitrary simplicial coefficient category. The strict fiber
isomorphism in Remark the project server has no fibrancy condition. No statement correction
or disputed statement is needed.

Validation: the complete final module compiles through the prescribed scompile.py
wrapper, separately as a sandbox module and under its final library module path,
with no errors or warnings (about three seconds per compile). The required
`deliver2.py Q72 lem-coef-unmarked-straightening-quillen --no-push` printed:

> OK (dry run): commit b908bb90f0 compiles and passes the preflight except for
> the second reading, which the second reader writes; nothing pushed.

No second-reading section has been written by this worker. The packet is ready
for the independently assigned reader.

## Second reading by Q72

Independent second reader, 2026-10-17. I opened the node, the entire delivered
module, the five statement-dependency records and their source declarations,
the maintenance prerequisite-repair report, and the source HTT PDF. This is not
a Stacks statement: the node explicitly cites HTT instead. In the PDF I read
Section 2.2.1 (printed pp. 73–74), the coend/singular conventions and construction
of Q in Section 2.2.2 (pp. 75–76), Remark the project server (p. 77), and the projective
model conventions in Section A.3.3, especially Proposition A.3.3.2 and Remarks
A.3.3.4–5. These assume arbitrary simplicial S and arbitrary small simplicial
coefficient category, with no local Kan or quasicategory assumption. The
strict fiber formula applies to every F. No statement correction is needed;
there are no new nodes or dependency modules to review.

My object/hypothesis/conclusion list, checked against Lean:

1. Arbitrary small simplicial S, small simplicial D, and simplicial
   φ : C[S] → Dᵒᵖ: exactly the three explicit theorem binders `S : SSet.{u}`,
   `D : SCat.{u}`, `φ : rigidification.obj S ⟶ oppositeCategory D`. The bundled
   `SCat` is the recorded `EnrichedCat` of simplicial categories, and
   `oppositeCategory` uses Mathlib's enriched opposite. Verdict: exact.
2. An arbitrary map a : X → S and its last-vertex cone pushout M:
   `X : Over S`, `conePushout D φ X`, with attaching maps
   `rigidification.map (orderedJoinInl X.left Δ[0])` and
   `rigidification.map X.hom ≫ φ`. `baseInclusion`, `coneInclusion`,
   `baseObject`, and `coneVertex` are the actual pushout maps and images of the
   vertices, using the recorded coherent-simplex unit. Verdict: exact.
3. L(X)(d) = M(d,v), precomposition action, and canonical functorial maps:
   `value`, `valueAction`, `pushoutMap`, and `valueMap`, fixed by all three
   fields of `IsStraightening`. The braiding puts the base mapping object
   before M(d,v) for enriched composition; Dᵒᵖ reverses d,e correctly.
   `HEq` in the action/map fields only handles the stated object equalities.
   Verdict: exact, including positive-dimensional mapping simplices.
4. The category of enriched D-diagrams and full enriched transformations:
   `Diagram.functor` is Mathlib `EnrichedFunctor SSet D SSet`. I repaired the
   Hom representation, as explained below, to wrap Mathlib `GradedNatTrans`
   with tensor-unit grading. `DiagramHom.app` is its uncurried simplicial
   component, and `DiagramHom.naturality` is the whole action-square equality.
   Identities and composites in `diagramCategory` are the curried objectwise
   identities and composites. Verdict: exact after the reuse repair.
5. Cofibrantly generated projective model, with functorial factorizations:
   `HasProjectiveModel D` fixes all three fields of its `ModelCategory` witness
   to `projectiveWeak`, `projectiveFib`, and `projectiveCof`, respectively.
   These are objectwise realization weak equivalences, objectwise all-horn Kan
   fibrations, and the left lifting class of objectwise trivial fibrations.
   The small sets I,J have exactly the two specified injective classes and
   functorial cellular factorizations. Bicompleteness is included. Verdict:
   exact in the node's recorded model-generation convention.
6. U(F) over S: `SimplexDescription.equiv` describes every n-simplex as the
   pair of its actual base simplex σ and an enriched map L(σ) → F.
   `projection` fixes the map to S; `operator` covers every simplex operator;
   `map` fixes the action on enriched diagram arrows. Verdict: exact.
7. The displayed adjunction: existential `adj : L ⊣ U`, with
   `IsConeAdjunction description adj` requiring its hom bijection on every
   simplex z to be `L.map (simplexArrow X n z) ≫ f`. This fixes the actual
   adjunction, as well as the object and arrow descriptions. Verdict: exact.
8. Preservation of cofibrations and trivial cofibrations: the next two
   conjuncts quantify over every slice arrow, with `Mono f.left` and, in the
   second, `contravariantWeak S f`. These are the source cofibration and
   trivial-cofibration classes. Verdict: exact; no extra preservation or
   fibrancy hypothesis is inserted.
9. Conditional Quillen equivalence: `Bergner.dwyerKanEquivalences φ` expands
   to local realization weak equivalences and equivalence on π₀. Under that
   hypothesis, for every X and every objectwise Kan F, and every actual map
   f : L(X) → F, the displayed iff compares f with its own adjoint under adj.
   Every X is covered, as every slice object is cofibrant. Verdict: exact.
10. Fibrant diagrams give right fibrations: the next conjunct is
    `ProjectivelyFibrant F → Enhanced.rightFibration (U.obj F).hom` for every
    F, independently of the Dwyer–Kan implication. Verdict: exact.
11. Strict fiber formula for every F and vertex s: `fiberIso F s` is an
    isomorphism from the recorded strict pullback fiber to
    `singQ (F.functor.obj (coefficientVertex D φ s))`. `singQ` has maps Qⁿ → T
    as its actual degree-n objects and precomposition as its operators.
    `singQMap` is postcomposition. The explicit equality with `fiberMap
    (U.map f)` states naturality in every enriched transformation. Verdict:
    exact; this is an isomorphism of simplicial sets, not only an equivalence
    of homotopy types, and no fibrancy is required.
12. Realization |K|_Q: `RealizationGenerator K r` is the coproduct of K_n × Qⁿ_r.
    `RealizationRelation.ofMap` has exactly the two representatives
    (K(α)z,q) and (z,Q(α)q), for every monotone α. `realizationSetoid` closes
    this relation under equivalence, and `qRealization` is its quotient with
    the induced simplicial operators. `qGenerator` gives every summand map.
    Verdict: exact quotient construction, with no choice of unknown data.
13. The first comparison arrow comes from the fiber inclusion into the cone:
    `PinchedGenerators` fixes the standard cone isomorphism on its entire
    initial face and last vertex, qIso on the surjective quotient projection,
    and collapse on the whole uncollapsed simplex. Its source/target fields
    identify the actual coefficient and cone objects. Thus `pinchedValueMap`
    is fixed; the comparison equation on every `qGenerator n z` uses exactly
    `valueMap` of `fiberSimplexArrow X s n z`. The latter is Yoneda's actual
    fiber simplex followed by the pullback's second projection. Verdict:
    canonical arrow, not an unconstrained map or isomorphism choice.
14. Compatibility of adjunction with fibers: the final equality is between
    whole simplicial maps, `fiberMap` of the actual adjoint followed by
    `fiberIso`, and `qAdjunct` of the generator-normalized comparison followed
    by the component of f (with only the object equality transport).
    `qAdjunct` evaluates on qGenerator and uses all coend relations.
    Verdict: exactly the last clause, for all X,F,f,s without fibrancy.

Dependency reading: I checked `PinchedCube.rigidification` is the simplex-colimit
left Kan extension, not a nerve, and that its `Q`, `qFunctor`, `quotientMap`,
`canonicalMap`, J,x,y and normalized isomorphism really are the node's explicit
pinched cubes with all monotone operators. `Bergner.simplicial_interval_lifting`
supplies the required colimits for this construction. I opened
`Enhanced.IsWeakHomotopyEquivalence`: it tests components and every positive
based homotopy group after realization. `right_proper_kan_quillen` identifies
all-horn `modelCategoryQuillen.J.rlp` with Kan fibrations and `KanComplex` with
fibrant objects. I read the complete `contravariant_slice_model` signature:
monomorphisms, categorical-equivalence-of-cones weak equivalences, small
cellular factorizations and fibrant right fibrations over arbitrary S. Its
`coneExtensionMap`, `IsCategoricalEquivalence`, `cellProperty`, `fiberMap` and
the reexported `InfinityFibrations.fiber` and `rightFibration` have exactly the
required signatures. The Bergner Dwyer–Kan predicate was traced through
`SimplicialIntervalCellStability` to `CoherentNerveComparison`: its π₀ condition
uses components of the mapping sets, not strict isomorphisms of arrows.
No dependency interface needs repair. The only stated proof dependency apart
from these is `SimplicialPresheafProjectiveModel`, imported without `public`;
I checked its Kan-combinatorial first assertion. The other proof inputs have
no recorded Lean module. The main docstring retains all six DAG proof steps,
including the small-object argument and comparison of the two contravariant
model structures; maintenance's three prerequisite records are left intact.

Edge cases: empty S leaves no vertex-indexed obligations but retains the model
and adjunction assertions; empty D is admitted whenever φ exists; the unique
empty X over S is included; no nonemptiness is selected by any construction.
Dimension zero is included in the coproduct/relations, with Q⁰ a point and the
constant-simplex cone Δ¹. Every degeneracy and noninjective ordinal map is
included in both the coend and U operators. Non-Kan F is explicitly covered by
the fiber and adjunction formulas; non-quasicategorical S and non-locally-Kan D
are unrestricted. There is no characteristic/ring/scheme parameter or
additional n = 0 exception. All universes and variables are explicit under
`autoImplicit false`. A common arbitrary universe u expresses small simplicial
sets/categories; larger chosen smallness bounds are handled by increasing u,
without adding an equality between different site universes.

Independent searches (prescribed msearch wrapper, recorded in searches.jsonl):
`leanfinder` query "simplicial correspondence cone adjunction projective model
enriched diagram" returned eight hits, including generic cone-functor
enrichment and nerve adjunctions, not this theorem. `loogle` query
`"Unstraightening"` returned zero hits. `grep` query
`unstraightening|simplicial.*correspondence|GradedNatTrans` returned the actual
Mathlib `GradedNatTrans` declaration and references. Direct `rg` searches in
Mathlib's enriched and algebraic-topology sources, upstream WeilConjectures,
and the project's Sheaf modules found only the identity-base straightening,
the different hom-object pinched resolution, and their consumers, not this
arbitrary-φ assertion. I opened `RightStraighteningFiberComparison` and
`PinchedRigidificationResolution`: the former is the identity-base case and
cites this item; the latter uses its different `resolution` cosimplicial
object and also depends downstream on that case. Neither supplies this
statement or the prescribed explicit `qFunctor` quotient. All proposed new
full names were searched and have no collision.

Mismatch found and repaired (H4): the first worker correctly rejected Mathlib
`EnrichedNatTrans`, whose stored datum is an ordinary transformation between
forgetful functors, but nevertheless duplicated full enriched naturality in
`DiagramHom`. Mathlib `GradedNatTrans` already stores that full enriched
notion. I replaced `DiagramHom` by a one-field wrapper of
`GradedNatTrans (𝟙_ (Center SSet)) F.functor G.functor`, and recover components
by `MonoidalClosed.uncurry'`. Identity and composition are concrete currying
of the identity/composite components. Three named proof-only helper theorems
translate naturality in both directions and give component extensionality;
each has a source/blueprint tag, a complete proof explanation, and `sorry` as
its whole proof. Their owning DAG statement is this item's enriched-diagram
category clause. No data is taken from them, beyond these property proofs.
I updated `lean.declarations` to include these helpers, the previously omitted
`DiagramHom`, and its component accessor, and updated `lean.note`. The earlier
worker report's description of the custom Hom record and six-theorem inventory
is superseded by this paragraph: there are now nine named postponed theorems.
No other mismatch was found and no mathematical/node statement was changed.

Validation: the complete revised module compiles with the required scompile.py
wrapper both as sandbox `Sheaf.Stage2.Sandbox0` and under its final library
module name, with no errors or warnings (3.6 s and 3.8 s, respectively).
The main `lean.statement` is byte-for-byte the signature in the Lean file;
there are no lines over 100 characters. All nine theorem proofs are `sorry`,
all definition data are explicit, and no file-local notation, private copy of
a dependency, or unbound variable is used. The node's only changed key is
`lean`. The prescribed delivery dry run and push follow this review.

Second-reader delivery dry run: `deliver2.py Q72
lem-coef-unmarked-straightening-quillen --no-push` exited successfully and
printed `OK (dry run): commit 7058afdda1 passes the preflight and compiles;
nothing pushed`. The normal prescribed delivery push is now requested.
