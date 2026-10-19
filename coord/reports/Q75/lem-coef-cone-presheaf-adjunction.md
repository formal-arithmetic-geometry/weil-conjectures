## Worker report

The delivery states `SSet.ConePresheaf.cone_presheaf_adjunction` in
`Sheaf.AlgebraicTopology.ConePresheafAdjunction`. Definitions have explicit data; all five
named theorems have `sorry` proofs and source/proof docstrings. The item is copied from the
current N2-reviewed split; only `lean` changes. No statement correction, new node, dependency
repair, or statement dispute is needed. The empty kept sandbox contained no earlier Lean or
report to recover. In particular this delivery does not try to redeliver the superseded split.

Source read: Lurie, Higher Topos Theory, official PDF
https://people.math.harvard.edu/~lurie/papers/HTT.pdf, printed pages 73–74, Section 2.2.1,
construction and first assertion in the proof of Theorem the project server; printed pages 870–871,
Definition A.3.3.1, Proposition A.3.3.2, Remark A.3.3.4. The cone is the last-vertex cone.
The projective model and raw adjunction require arbitrary small S, without a quasicategory
hypothesis. No assertion of Quillen equivalence or of a contravariant slice model is made.

Hypotheses and every clause of the node are rendered as follows:

| Natural statement | Lean rendering |
| --- | --- |
| Fixed small simplicial set S; universes enlarged as needed | `(S : SSet.{u})`, explicit `universe u`; presheaf objects in `Type (u+1)`, arrows and mapping simplices in `Type u` |
| D = C[S]^op | `EnrichedFunctor SSet (PinchedCube.rigidification.obj S)ᵒᵖ SSet.{u}` in `Presheaf.functor` |
| Objects are simplicial functors | `Presheaf` wraps exactly that Mathlib enriched-functor data, including its enriched identity and composition laws |
| Arrows commute with simplicial action maps | `Hom.app`, `Hom.naturality`, using `action`, a map on the entire mapping simplicial set; `presheafCategory` has componentwise identities/composition |
| Objectwise weak homotopy equivalences | `weakEquivalences S`, using the recorded realization-based `Enhanced.IsWeakHomotopyEquivalence` at every realized-base object |
| Objectwise Kan fibrations | `fibrations S`, using `modelCategoryQuillen.J.rlp` at every object, with no endpoint fibrancy assumption |
| Projective cofibrations lift against objectwise trivial Kan fibrations | `trivialFibrations S` is the objectwise `modelCategoryQuillen.I.rlp`, including the zero-dimensional boundary; `cofibrations S := (trivialFibrations S).llp` |
| This is a complete, cocomplete model category | The first conjunct fixes all three structure fields of an existential `ModelCategory (Presheaf S)`; the next two conjuncts assert `HasLimitsOfSize.{u,u}` and `HasColimitsOfSize.{u,u}` |
| Functorial factorizations | `HasFunctorialFactorization (cofibrations S) (trivialFibrations S)` and `HasFunctorialFactorization (cofibrations S ⊓ weakEquivalences S) (fibrations S)` |
| Mapping simplicial set has enriched maps F×Δ[n]→G as n-simplices | `ParameterMap F G K` has actual simplicial component maps and their action equation in every degree. `mapping F G` specializes K to `SSet.stdSimplex.obj n.unop`; `restrictParameter` precomposes the parameter |
| Projectively fibrant means objectwise Kan | The next theorem conjunct tests every map to a terminal presheaf and equates its fibration condition with `∀ c, KanComplex (obj F c)`. Terminal objects exist by the completeness conjunct |
| Projectively cofibrant means the initial map is projective cofibration | `IsProjectivelyCofibrant F` tests the map from any initial object against `cofibrations S`. Cocompleteness supplies an initial object. This is a definition, not an additional lifting theorem |
| T_a is C[cone X] amalgamated with C[S] along C[X] | Reuses `Straightening.conePushout a.hom` and its two inclusions, already defined as that enriched pushout |
| v is the distinguished last cone vertex | Reuses `Straightening.coneVertex`, defined by the pure final join inclusion and the canonical simplex-colimit vertex |
| L_S(X)(s)=T_a(s,v), action by precomposition | `leftObj a := ⟨Straightening.straightening a.hom⟩`, whose objects are the recorded `valueAt` and action is the recorded `enrichedAction`; `action` uncurries it |
| Functoriality in maps over S | `leftApp` applies the actual `conePushoutMap` on mapping sets with the specified endpoint equalities `pushoutMap_objects`; `leftApp_naturality` and `leftMap_laws` give `left S : Over S ⥤ Presheaf S` |
| U_S(F) degree n over σ consists of enriched maps L_S(Δ[n]→S)→F | `RightSimplex F n := Σ σ : stdSimplex.obj n ⟶ S, (left S).obj (Over.mk σ) ⟶ F`; `rightSet` has these degreewise simplices |
| Simplex operators are restriction | `simplexOverMap`, `rightRestrict` precompose the label by `left.map` of the corresponding simplex morphism; `rightRestrict_laws` retains the dependent base simplex |
| Projection U_S(F)→S | `rightProjection` sends the base map σ to its Yoneda simplex; `rightObj := Over.mk (rightProjection F)` |
| Functoriality in F | `rightSetMap` postcomposes labels by the enriched map F→G, retaining σ; `right S` is the resulting ordinary slice functor |
| Ordinary adjunction L_S⊣U_S | `Nonempty (left S ⊣ right S)` for the two specified functors, not an arbitrary pair of functors or arbitrary maps |
| Every degreewise monomorphism over S maps to a projective cofibration | `∀ (a b : Over S) (f : a ⟶ b), Mono f.left → cofibrations S ((left S).map f)`; Mathlib simplicial monos are exactly degreewise injections |
| Relative cones before realization | `relativeCone a := pushout (Enhanced.orderedJoinInl a.left Δ[0]) a.hom`; `relativeConeMap f` uses the canonical cone map and identity of S |
| DK means local weak homotopy equivalences and equivalence on π0 | Reuses `CategoryTheory.DwyerKanEquivalence` with `A` and `B` the `CoherentNerve.underlying` categories of the two actual rigidified relative cones |
| A DK equivalence of those relative cones makes L_S(f) objectwise weak equivalence | The final conjunct has exactly that antecedent on `PinchedCube.rigidification.map (relativeConeMap f)` and concludes `weakEquivalences S ((left S).map f)` |
| No model structure on sSet/S or quasicategory assumption | There is no such instance, binder or predicate in any construction or in the theorem |

The five postponed theorems are `pushoutMap_objects`, `leftApp_naturality`, `leftMap_laws`,
`rightRestrict_laws`, and the main `cone_presheaf_adjunction`.
The first four are the well-definedness and functoriality laws of this node's own canonical
maps. Their proofs are written in their docstrings; the main docstring contains the six
steps of N2's current split with its actual dependencies, including the independent
boundary-cube attachment. There is no data chosen from an uncharacterized existence theorem.

Dependency declarations read and used:

- `def-cbc-enhanced-diagrams-cones`: `Sheaf.CategoryTheory.EnhancedDiagramsCones`,
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, full signature/docstring: bijective realization
  components and every based homotopy group in positive degree; reused without a new predicate.
- `lem-coef-pinched-cube-latching`: `Sheaf.AlgebraicTopology.PinchedCubeLatching`,
  `SSet.PinchedCube.coherentSimplex`, `rigidification`, `coherentSimplexUnit`,
  `sCatColimits`, and `pinched_cube_latching`. The entire construction and main signature
  were read. Rigidification is the left Kan extension of the recorded coherent simplices.
- `lem-coef-simplicial-boundary-collapse-test`:
  `Sheaf.AlgebraicTopology.SimplicialBoundaryCollapseTest`,
  `CategoryTheory.simplicial_boundary_collapse_test`; its explicit model-category and
  functorial-factorization signature and docstring were read. We use those Mathlib model
  conventions, and retain the module as a statement dependency.
- `lem-coef-kan-quillen-right-proper`: `Sheaf.AlgebraicTopology.KanQuillenRightProper`,
  `SSet.KanQuillen.right_proper_kan_quillen` and `weakEquivalenceStructure`; full recorded
  signature read. The theorem fixes the Kan fibrations at `J.rlp`, trivial fibrations at
  `I.rlp`, and the realization-based weak-equivalence structure. These are the classes used.
- The canonical constructions already reside in
  `Sheaf.AlgebraicTopology.RightStraighteningFiberComparison`:
  `SSet.Straightening.straightening`, `conePushout`, `baseInclusion`, `coneInclusion`,
  `coneVertex`, `valueAt`, `precomposition`, `enrichedAction`, `coneMap`,
  `coneInclusion_naturality`, `conePushoutMap`. Full definitions and docstrings were read.
  Only these constructions and their named structure laws are used. No invocation of
  `right_straightening_fiber_comparison`, the contravariant model, or a full Quillen theorem
  occurs. Adding that downstream theorem as a DAG dependency would be circular, so the
  unchanged DAG statement dependencies are retained. Reusing its already landed construction
  layer avoids making a second copy of a notion.
- `Sheaf.CategoryTheory.CoherentNerveComparison`, `CategoryTheory.DwyerKanEquivalence`,
  `PiZeroEquivalence`, `PiZeroEssentiallySurjective`; read their definitions and docstrings.
  Only the predicates are used, not the downstream coherent-nerve theorem.
- Mathlib: `EnrichedFunctor`, enriched opposites, the monoidal-closed self-enrichment,
  `ModelCategory`, `MorphismProperty.llp`, `HasFunctorialFactorization`, simplicial Yoneda
  and `Over`. `EnrichedNatTrans.out` was read: it records only naturality of the underlying
  ordinary functors. It therefore does not express the required full action equation.
  `Hom` adds precisely this requirement while keeping Mathlib enriched functor objects.

Proof-only imports: the landed `Sheaf.AlgebraicTopology.SimplicialPresheafProjectiveModel`,
Mathlib lifting-class closure and transfinite lifting modules. `SimplicialIntervalLifting`
is publicly available through the construction imports. The genuine proof inputs
`lem-coef-simplicial-projective-model-calculus` and `lem-coef-rigidification-boundary-cube`
have no recorded Lean declarations, so there is no module to import for them. They are
retained in the unchanged proof plan; they are not required for typing this statement.

Edge cases checked mathematically before constructing the statement:

- Empty S forces every X→S to have empty domain; there are no old objects, and the
  presheaf category has one object/arrow up to isomorphism. No chosen old vertex is needed
  in `pushoutMap_objects`. The right simplices form an empty dependent sum, so U is empty.
- Empty X with arbitrary S retains the new cone vertex; every old-to-v mapping set is
  empty, so L(X) is initial. The adjunction has singleton hom sets in this case.
- For S a point and X a vertex the cone is the one-arrow category, and L(X) is the point.
- The zero-dimensional boundary is empty; `I.rlp` includes that lifting test. Thus
  objectwise trivial fibrations include the required degree-zero surjectivity condition.
- Degenerate simplices and all monotone maps occur in `rightRestrict`; restriction is
  not limited to injective maps. No nonempty hypothesis occurs.
- Identity f gives identity cone maps and therefore both preservation conclusions.
- Full enriched naturality is necessary even when actions have nontrivial higher simplices;
  naturality only on vertices is not used as a replacement.

Searches made (actual tool calls, not inferred absence):

- `msearch.py leanfinder`, query “The right cone straightening functor from simplicial
  sets over a base is left adjoint to enriched simplicial presheaf unstraightening”:
  eight hits for ordinary nerve, coskeleton, Čech nerve and ordinary cone adjunctions;
  none gives this enriched cone construction or its preservation assertions.
- `msearch.py loogle`, query `"EnrichedFunctor", "Adjunction"`: zero hits.
- `msearch.py leansearch`, query “Simplicial enriched presheaf cone straightening
  adjunction”: eight hits for ordinary cone adjunctions, their naturality, and the
  singular/geometric realization adjunction; no exact match.
- `msearch.py grep`, query `straighten|conePresheaf|EnrichedFunctor`: fifteen hits in
  Mathlib's enriched-category and simplicial-nerve files. Read `Enriched/Basic.lean`,
  `Enriched/EnrichedCat.lean`, `Enriched/FunctorCategory.lean`, `Enriched/Opposite.lean`
  and `Monoidal/Closed/Enrichment.lean`. They supply objects, enrichment and ordinary
  functor-category ends, not the full raw cone adjunction.
- `rg` of `lean/Sheaf/AlgebraicTopology` and the upstream `WeilConjectures` category and
  algebraic-topology sources for `CoherentNerve`, `EnrichedFunctor`, presheaf structures,
  and cone adjunction names: found the landed `RightStraighteningFiberComparison` and
  reused its canonical data. The ordinary-indexed `SimplicialPresheafProjectiveModel`
  does not have simplicially enriched index C[S]^op and is not substituted for this theorem.
- `rg` of upstream `WeilConjectures` for the exact node id: no hit.
- `rg` of `dag/lean_names_upstream.json`, `lean/Sheaf` and upstream for
  `SimplicialProjectiveModelCalculus|ConePresheaf|RigidificationBoundaryCube`: no exact
  preexisting raw-adjunction declaration. No duplicate theorem is recorded as a new one.

Validation: the prescribed `scompile.py Q75 lem-coef-cone-presheaf-adjunction` compiled
both the sandbox probe and the actual module cleanly (1.9 s and 2.2 s in the successful
run), with no warnings. Every universe and variable is explicit (`autoImplicit false`).

## Second reading by Q75

I read the current node (including all six proof steps), its sandbox module, all four
statement-dependency nodes and their recorded source declarations. The source is HTT,
not Stacks: I independently opened the official PDF at
https://people.math.harvard.edu/~lurie/papers/HTT.pdf and read printed pp. 73–74
(§2.2.1, construction, adjunction, and start of the proof of Theorem the project server) and
pp. 870–871 (Definition A.3.3.1, Proposition A.3.3.2, Remark A.3.3.4).
The general enriched model theorem assumes an excellent enriching model category and a
combinatorial enriched target; here these specialize to the Kan model on simplicial sets.
They impose no additional condition on the small enriched indexing category. The raw
construction fixes an arbitrary simplicial set S. No Kan or quasicategory condition on S,
or local Kan condition on C[S], is implicit in this use of the source.

Here is my own object/hypothesis/conclusion list, with its final Lean rendering and verdict:

| Node object, hypothesis or clause | Final Lean rendering and verdict |
| --- | --- |
| Arbitrary small S; universes may be enlarged | `S : SSet.{u}`, universally quantified `u`; no extra binder. PASS. |
| D is the opposite of the coherent realization of S | `Presheaf.functor : EnrichedFunctor SSet (PinchedCube.rigidification.obj S)ᵒᵖ SSet.{u}`. PASS. |
| Objects are simplicial functors, including identity and composition axioms | Mathlib `EnrichedFunctor` has actual object maps and simplicial hom maps with both laws. The object wrapper installs the required category. PASS. |
| Arrows are enriched natural transformations, commuting with the whole simplicial action | After repair, `Hom` abbreviates Mathlib `GradedNatTrans` with unit parameter. `component` uncurries each component. `component_naturality` states the action equation as an equality of simplicial maps. PASS after H4 repair. |
| Weak equivalences are objectwise weak homotopy equivalences | `weakEquivalences S` applies `Enhanced.IsWeakHomotopyEquivalence` to every `component f c`. PASS. |
| Fibrations are objectwise Kan fibrations | `fibrations S` applies `modelCategoryQuillen.J.rlp` to every component, without assuming fibrant endpoints. PASS. |
| Trivial Kan fibrations and projective cofibrations | `trivialFibrations S` uses the complete boundary class `I.rlp`, including degree zero; `cofibrations S` is its `llp`. PASS. |
| The projective classes define a model category with all small limits and colimits | The existential `ModelCategory` witness has all three classes fixed; separate `HasLimitsOfSize.{u,u}` and `HasColimitsOfSize.{u,u}` conjuncts provide the size used here. PASS. |
| Both factorizations are functorial | The two `HasFunctorialFactorization` conjuncts use `(cofibrations,trivialFibrations)` and `(cofibrations ⊓ weakEquivalences,fibrations)`. PASS. |
| Mapping n-simplices are enriched maps F×Δ[n]→G; operators are restriction | After repair, `ParameterMap F G K` is Mathlib's K-graded transformation. Its curried component is K→[F(c),G(c)], equivalently F(c)×K→G(c); graded naturality is precisely the parameter-preserving action equation. `mapping` is `stdSimplex.op ⋙ enrichedNatTransYoneda`, so every simplex operator is parameter restriction. PASS after H4 repair. |
| Fibrant objects are exactly objectwise Kan complexes | The terminal-map conjunct in `cone_presheaf_adjunction` is an iff with `∀ c, KanComplex (obj F c)`. Completeness supplies terminal objects, so the universal terminal-map formulation is not vacuous. PASS. |
| Cofibrant means its initial map is projectively cofibrant | `IsProjectivelyCofibrant` tests maps from any initial object against `cofibrations S`. Cocompleteness supplies that object. This is the stated definition. PASS. |
| T_a is the enriched pushout C[cone X] amalgamated with C[S] along C[X] | `leftObj` reuses `Straightening.straightening`; I opened `conePushout`, `baseInclusion`, and `coneInclusion`, which use exactly these two rigidified legs. PASS. |
| v is the last cone vertex | The reused `coneVertex` is the image of `orderedJoinInr X Δ[0]` through the simplex inclusion and cone pushout leg. PASS. |
| L_S(X)(s)=T_a(s,v), acted on by precomposition | Reused `valueAt`, `precomposition`, `enrichedAction`, and `straightening` have exactly these data; `action` uncurries the latter. PASS. |
| L is functorial over the fixed S | `leftApp` uses the actual enriched `conePushoutMap` with base identity, with `pushoutMap_objects` transporting both endpoints. `leftMap := homMk ...` and `leftMap_laws` assemble `left`. PASS. |
| U's n-simplices over σ are enriched transformations L(Δ[n]→S)→F | `RightSimplex F n` is the dependent sum of σ and precisely that Hom type. PASS. |
| U's simplex operators are restriction | `simplexOverMap` and `rightRestrict` precompose the label by `left.map`; `rightRestrict_laws` retains the dependent base map. All monotone maps, including degeneracies, occur. PASS. |
| U projects to S and is functorial in F | `rightProjection` evaluates σ under simplicial Yoneda; `rightSetMap` postcomposes the transformation label, and `right` is its slice functor. PASS. |
| Specified ordinary adjunction L_S⊣U_S | `Nonempty (left S ⊣ right S)`, using the two explicit constructions. No arbitrary functors or object choices replace them. PASS. |
| Every degreewise mono over S maps to a projective cofibration | The next conjunct quantifies over all slice maps f and assumes `Mono f.left`, equivalent to degreewise injectivity in simplicial sets. PASS. |
| The relative cones in the DK hypothesis are simplicial pushouts before realization | `relativeCone` is the pushout of `orderedJoinInl` along a.hom; `relativeConeMap` is its canonical induced map, fixing S. PASS. |
| DK means local weak homotopy equivalences and equivalence of π0 categories | I opened `DwyerKanEquivalence`, `PiZeroEquivalence`, and `PiZeroEssentiallySurjective`: these test local realization weak equivalences, bijections on hom components, and essential surjectivity using inverse witnesses modulo components. `underlying` only equips the same enriched category with its ordinary category. PASS. |
| DK on those realized relative cones implies objectwise weak equivalence of L(f) | The final implication uses `rigidification.map (relativeConeMap f)` on the two specified relative cones and concludes `weakEquivalences S ((left S).map f)`. The order of quantifiers and implication is exact. PASS. |
| No slice model or quasicategory hypothesis | Neither occurs in the theorem or construction binders. PASS. |

Dependency checks: `PinchedCube.rigidification` is the left Kan extension of the
endpoint-subset coherent simplices, not an ordinary nerve or an assumed equivalent
category. Its object universe is u, though the bundled category lives higher; this
makes the component families and all Hom simplicial sets u-small. `KanQuillen` fixes
fibrations to horn lifting and trivial fibrations to boundary lifting, and its weak
structure uses the same realization predicate. `SimplicialBoundaryCollapseTest` spells
out completeness/cocompleteness and functorial-factorization conventions, both retained
here. I read `Enhanced.componentsMap`, `homotopyGroupMap`, and
`IsWeakHomotopyEquivalence`: all realized components and all positive based groups are
included. I also read `CoherentNerve.SCat`, `hom`, `underlying`, and the complete
straightening construction through `conePushoutMap`; no comparison theorem from those
modules is invoked. There are no new nodes or dependency modules in this delivery.

Edge cases: an empty S admits no nonempty X over it. All families over C[S] remain
valid without choosing a base vertex, and the right simplices are empty dependent sums.
For empty X and arbitrary S the new cone vertex still exists, while old-to-v homs are
empty, giving the initial presheaf. The mono-preservation proof keeps the cone vertex
in its partial cone even in this case. At n=0 the boundary test is empty→Δ[0], so no
surjectivity condition is lost. Parameter restriction includes identities and
degeneracies, not just faces. Identity slice maps use identity cone maps and transport
by the functor laws. There is no additive zero, scheme, or characteristic hypothesis in
this statement. All object, morphism, and simplicial universes were checked: one common
u is allowed by the node's universe-enlargement convention, without a finiteness or
nonemptiness restriction or equality of genuinely different site universes.

Independent searches (different queries from the first author):

- `msearch.py ... leanfinder 'Enriched presheaves on coherent realization: straightening
  as mapping into the final vertex of a relative cone, with a right adjoint'`: eight
  results, chiefly ordinary-indexed `FunctorCategory.coneFunctorEnrichedHom` and site
  enriched Hom. Their signatures do not give this raw cone adjunction.
- `msearch.py ... loogle '"EnrichedNatTrans"'`: seven results. I opened
  `Mathlib/CategoryTheory/Enriched/Basic.lean`, including both `EnrichedNatTrans.out`
  and the neighboring `GradedNatTrans` and `enrichedNatTransYoneda` declarations.
- `msearch.py ... leansearch 'Simplicial natural transformation of enriched functors
  with a parameter as a graded natural transformation'`: eight results led by
  `GradedNatTrans` and its fields. This confirms the usable existing construction.
- `rg` over Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf` for
  `cone.?presheaf|raw.*adjunction|GradedNatTrans|cone.*straighten|straighten.*adjunction`:
  Mathlib has `GradedNatTrans` and its Yoneda presheaf; the project has the existing
  straightening cone/value/action construction; no full theorem matching this node.
  I also inspected Mathlib `Monoidal/Closed/Enrichment.lean` and the curry/uncurry
  equivalences in `Monoidal/Closed/Basic.lean`.

Mismatch and repair: the first author correctly rejected `EnrichedNatTrans.out`, whose
stored condition is only underlying ordinary naturality, but overlooked the usable
`GradedNatTrans` immediately above it. Its unit-parameter specialization already gives
full enriched transformations; its general parameter and `enrichedNatTransYoneda`
already give the parameterized maps and restriction. The custom `Hom` and
`ParameterMap` structures therefore duplicated an existing notion (H4). I replaced both
with abbreviations of `GradedNatTrans`, reused its Yoneda presheaf for `mapping` and
`restrictParameter`, and added the canonical `component`/`homMk` adapters. The named
postponed adapter laws `component_naturality`, `homMk_naturality`, and `hom_ext` have
explicit natural-language proofs and this node's blueprint/source docstrings. Their
data is fixed by curry and uncurry, with only proofs postponed. I adjusted the category
structure and objectwise properties to use these actual components, and `leftMap` to
use `homMk`. This paragraph supersedes the first author's descriptions of the two
custom structures and its count of postponed theorems. The other five postponed
theorems, all cone constructions, the main signature, the mathematical node statement,
and its proof plan remain unchanged. No source correction or citer audit is required.

Validation: the prescribed `scompile.py Q75 lem-coef-cone-presheaf-adjunction <module>`
compiled both the sandbox probe and the actual library module with no errors and no
warnings (6.8 s and 6.9 s). Every delivered file was included. `autoImplicit false` is
explicit. All eight theorem proofs are `sorry`; all definitions have real data, and
only structure-law proofs are supplied inside structures. No file-local notation,
private definition, or local instance is introduced. No line exceeds 100 characters.
The node's `lean.declarations` and note were updated; normalized `lean.statement` was
checked verbatim against the unchanged signature. The independent reading found no
other object, hypothesis, quantifier, or conclusion mismatch.
