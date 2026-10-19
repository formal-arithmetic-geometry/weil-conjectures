## Worker report

The delivery states `lem-coef-marked-point-cartesian-model` in
`Sheaf.AlgebraicTopology.MarkedPointCartesianModel`. There is one postponed theorem,
`SSet.Marked.marked_point_cartesian_model`. All other declarations construct data or
specify the concrete assertions assembled by that theorem. No dependency node is
restated, no node statement is corrected, and no new DAG node is introduced.

The entire informal statement is rendered as follows. All names below, unless
qualified, are in `SSet.Marked`.

| Hypothesis or clause | Lean rendering |
| --- | --- |
| Nested size convention | Explicit universe levels `u v`; marked simplices and Hom sets are in `u`, the category of all marked objects is in `u + 1`; coherent nerves live in `u + 1`. `enlarge.{u,v}` goes to `max u v`. No equality of independent universe levels is assumed. |
| Simplicial sets and quasicategories | Existing `SSet.{u}`, `SSet.Quasicategory`, standard simplex and simplicial operators. |
| A pair `(X,M)` containing every degenerate edge | `SSet.Marked` has fields `underlying`, `marking`, `degenerate`. |
| Maps preserve markings | `Hom` is the subtype of underlying natural transformations satisfying preservation for every marked edge; `markedCategory` composes the underlying maps. |
| Cartesian products mark precisely coordinatewise marked edges | `product` uses the degreewise Mathlib tensor, and its marking is the conjunction of the two marking predicates. `productMap` acts coordinatewise. |
| Flat and sharp markings | `flat.marking = Set.range (K.σ 0)`; `sharp.marking = Set.univ`; `flatMap`, `sharpMap` preserve them. |
| Natural marking | `natural` marks equivalences together with degenerate edges. `CartesianModelStatement.natural_marking` asserts, for every simplicial set and edge, that this is exactly the dependency's equivalence predicate. The explicit union supplies real degeneracy data; it is extensionally the requested marking. |
| Marked internal Hom | `mapFlat` has actual marked maps `X × (Δ[n])♭ → Y` as simplices. `internalHom` marks an edge precisely when the same underlying map preserves the sharp interval marking. Its degeneracy proof uses the collapse to the zero-simplex. |
| Marked exponential adjunction | `exponential` is `(Z → Y^X) ≃ (Z × X → Y)`. `exponential_formula` fixes its evaluation on every simplex at the identity simplex; it therefore specifies the canonical adjunction, with variable order matching the node. |
| Sharp mapping object | `mapSharp X Y = (sharpSimplex ⋙ productLeft X).op ⋙ yoneda.obj Y`: degree `n` is literally the marked Hom set `X × (Δ[n])♯ → Y`. Operators precompose the parameter. `mapSharpPre` and `mapSharpPost` are actual pre/postcomposition. |
| A complete and cocomplete model category | `CartesianModelStatement.complete`, `.cocomplete`, and `.model : ModelCategory Marked`. Mathlib's model axioms include retract closure, two-out-of-three, lifting, and factorizations; their standard consequences identify both weak factorization systems by their diagonal-lifting classes. |
| Cofibrations are injections on underlying simplices | `cof` quantifies over every degree, requiring `Function.Injective (f.val.app n)`. The `.cofibrations` field identifies this property with the actual model field. A map adding only markings is included. |
| Mapping-test weak equivalences | `weak` quantifies over every `C : SSet.{u}` with `Quasicategory C`, and uses exactly `Enhanced.IsWeakHomotopyEquivalence (mapSharpPre f (natural C))`. `.weak_equivalences` identifies this with the same model's weak equivalences. |
| Fibrations are RLP against trivial cofibrations | `.fibrations` identifies the actual model field with `(cof ⊓ weak).rlp`. |
| Functorial factorizations | `.cof_triv_fib_factorization` and `.triv_cof_fib_factorization` use Mathlib's `HasFunctorialFactorization`, on precisely the intersections with `weak`. Together with the model axioms these are functorial WFSs. |
| Combinatorial and locally presentable | `.generating_cofibrations` and `.generating_trivial_cofibrations` give `u`-small morphism properties whose RLP classes are respectively the trivial fibrations and fibrations. `.locally_presentable` is Mathlib's `IsLocallyPresentable.{u}`, using some regular cardinal, a small filtered generator, and Hom preservation. |
| Fibrant objects exactly naturally marked quasicategories | `IsNaturallyFibrant X` is the conjunction of quasicategory fibrancy and exact equality of the marking and equivalence predicates. `.fibrant_objects` tests the actual model fibration class on `toPoint X`. |
| Every object cofibrant | `.every_object_cofibrant` includes every object and every initial-object representative. Completeness/cocompleteness supplies initial objects, so this is not a vacuous conditional. |
| Terminal object is sharp zero-simplex | `.terminal_point : IsTerminal (sharp Δ[0])`; `toPoint` is the actual unique underlying map with target sharp marking. |
| Cartesian pushout product and triviality in either factor | `IsPushoutProduct i j p` requires the universal pushout square from `X × Y` to `X' × Y` and `X × Y'`, and the two exact restrictions of `p : P → X' × Y'`. `.pushout_product` asserts `cof p`, and `weak p` if `weak i ∨ weak j`. This retains arbitrary pushout representatives. |
| Products with any marked set preserve weak equivalences | `.products_preserve_weak_equivalences` states `weak f → ∀ Z, weak (productMap f (𝟙 Z))`. Symmetry of the explicit product gives the equivalent other-coordinate formulation. |
| Enrichment with mapping objects Map sharp | `.enrichment : SimplicialCategory Marked`; `.mapping_iso` identifies its Hom with `mapSharp`. `.ordinary_enrichment` fixes every ordinary map's image in every degree. `.enrichment_composition` fixes every enriched composite by the diagonal-parameter formula. Thus composition and identities are the canonical ones, including their entire simplicial structure. |
| Tensor `X ⊗ K = X × K sharp` | `.tensor_adjunction` gives the tensor's Hom adjunction for every simplicial set `K`; `.tensor_formula` fixes every simplex of its transpose, including restriction to every parameter simplex. |
| Cotensor | `.cotensor_adjunction` uses the actual `internalHom (sharp K) Y`; `.cotensor_formula` fixes its transpose by evaluation. These formulas imply the ordinary and enriched naturality of both adjunctions. |
| Simplicial model pushout-product axiom over Kan--Quillen | `.simplicial_pushout_product` quantifies over any underlying monomorphism `j : K → L` and the actual pushout product with `sharpMap j`; triviality is `weak i ∨ Enhanced.IsWeakHomotopyEquivalence j`. This uses exactly the cofibration and realization-based weak-equivalence classes of the recorded Kan--Quillen dependency. |
| Mapping Kan complexes into fibrant objects | `.sharp_mapping_kan` covers arbitrary marked sources and every naturally fibrant target. |
| Identity with the functor core | `.mapping_core` is the natural isomorphism between `mapSharp (natural C) (natural D)` and the dependency's `Enhanced.core ((ihom C).obj D)`. `.mapping_core_formula` fixes its full underlying evaluation, so naturality and compatibility with composition follow from the displayed formulas rather than an arbitrary choice of an isomorphism. |
| Coherent nerve is the prescribed model of Cat infinity | `FibrantObjects` is the full subcategory on the exact fibrancy predicate. `fibrantNerve` is its actual Mathlib coherent nerve. `quasicategoryNerve` is the actual coherent nerve of small quasicategories. `.qcat_enrichment`, `.qcat_mapping`, `.qcat_ordinary_maps`, `.qcat_composition` specify the core enrichment and its ordinary maps and composition. `.fibrant_nerve_identification` identifies the two nerves; `.nerve_objects` and `.nerve_mapping` normalize it on all objects and all enriched mapping simplices, not just vertices. `.cat_infinity_quasicategory` states that this model is a quasicategory. |
| Respect for composition | Explicitly `.enrichment_composition`, `.qcat_composition`, `.mapping_core_formula`, and `.nerve_mapping`. These specify the same evaluation maps and diagonal-parameter composition. |
| Universe stability of weak equivalences and fibrancy | The final two conjuncts of `marked_point_cartesian_model` are biconditionals for `weak f` and `IsNaturallyFibrant X` under the actual degreewise lifting `enlarge`/`enlargeMap` to arbitrary `max u v`. |
| Model, small colimits, functorial replacements in the input universe | The first two conjuncts assert the complete structure in both `u` and `max u v`. Each model's colimits are indexed in its simplex universe, and its functorial factorizations take values in that same marked category. In particular factoring a terminal map yields replacement objects with simplices still in the input universe. The collection of all objects, and its nerve, are in the successor universe. |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsEquivalenceEdge`,
  `core`, `IsWeakHomotopyEquivalence`; the latter tests realization on components
  and all positive homotopy groups at every basepoint. Mathlib's `ihom` is the
  recorded functor simplicial set.
- `def-weil-size-convention` is recorded as a metatheoretic convention, not a
  declaration; the explicit universe levels implement it.
- `Sheaf.CategoryTheory.CoherentNerveComparison`: the recorded
  `CategoryTheory.coherent_nerve_comparison` and its full structure were read;
  this delivery uses its actual coherent-nerve convention from
  `CategoryTheory.SimplicialNerve` and its `CoherentNerve.QCats` category. The
  nerve is the enriched-functor simplicial set from Mathlib's subset-poset
  thickening, not an unrelated nerve construction.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen` supplies the Kan--Quillen model
  comparison and the realization-based weak-equivalence convention.
- Proof-only imports:
  `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`
  (`SSet.Enhanced.enhanced_functor_cone_calculus`, pointwise equivalences and cores),
  and `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct`
  (`SSet.anodyneExtensions_pushoutObjObjι`). The marked-anodyne, saturation, and
  perfect-class-recognition proof nodes have no Lean statements yet and are not
  imported. They are not statement prerequisites; their nine-step use is recorded
  verbatim in the theorem docstring for stage 3.

Edge cases checked before and after writing:

- The empty simplicial set has empty edge marking and vacuous degeneracy condition;
  it is admitted as a quasicategory and a fibrant object. No binder requires any
  vertex, object or component to exist.
- Degree zero is included in all injection and transpose formulas. The flat and
  sharp zero-simplex agree extensionally, and `toPoint` requires no chosen vertex.
- A map that adds marked edges but is an identity on underlying simplices remains
  a cofibration, because `cof` tests only the underlying maps.
- Products have conjunction markings; multiplying with an empty object gives an
  empty product, and multiplying with the marked point gives the expected marking.
- The internal Hom marks only the requested sharp extensions; no sharp marking is
  imposed on an arbitrary target. Its degenerate edges factor through the point.
- In the pushout-product formula the common source is `X × Y`, and the target is
  `X' × Y'`; neither copy of a primed factor has been interchanged.
- Tensor triviality uses ordinary weak *homotopy* equivalence on the unmarked
  parameter, not a Joyal equivalence or a flat marking.
- The weak-equivalence test includes every small quasicategory, including the empty
  one. It is not restricted to fibrant marked sources.
- `v` is arbitrary; no same-universe shortcut or fictitious independent small
  universe for test objects is used. Enlargements transport every marking.
- The strict nerve identification is possible because the marking of a fibrant
  object is uniquely its equivalence predicate. The source object can carry any
  definitionally different presentation of that same set; the normalized isomorphism
  handles those presentations without requiring a definitional equality.

Searches for existing declarations (all through the prescribed search wrapper):

| Tool | Query | Result |
| --- | --- | --- |
| LeanFinder | `Cartesian simplicial model structure marked simplicial sets quasicategories` | Eight hits: unmarked `SSet.QCat`, Kan--Quillen generating classes/fibrations/cofibrations, and quasicategory instances; no marked object or marked model theorem. |
| Loogle | `"MarkedSSet"` | No hits. |
| Mathlib grep | `MarkedSSet\|marked.{0,20}simplicial\|MapSharp` | No hits. |
| LeanSearch | `marked simplicial sets Cartesian simplicial model structure` | Eight hits: unmarked SSet, Cartesian products, Kan--Quillen classes, and coordinatewise tensor lemmas; no match. |
| Source and side-library ripgrep | Case-insensitive `marked.?sset\|marked.?simplicial\|MapSharp\|markedPoint` in upstream `WeilConjectures` and project `lean/Sheaf` | No hits. |
| Upstream item-id search | `lem-coef-marked-point-cartesian-model` in `WeilConjectures` | No hits. |
| DAG ripgrep | `marked simplicial\|marked.*simplicial\|simplicial.*marked` | Read the candidate names; the current node introduces the marked-set notion. Other hits concern its anodyne, saturation and localization consequences, not an existing definition to duplicate. |

The source [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf) was opened online:
Proposition the project server (PDF p. 174) is the Cartesian combinatorial model, and Corollary
the project server (PDF p. 179) explicitly uses Map sharp and the sharp tensor parameter.
The complete nine-step proof from the node is in the theorem docstring, including
all named inputs, the product inverse argument, and the universe-independence step.

No `STATEMENT-DISPUTED` issue or node fault was found. The constructions that the
node itself introduces are helpers in its owning module, recorded in
`lean.declarations`; they are not additional assertions of other DAG nodes.

Validation: the full statement has compiled with the prescribed `scompile.py`
wrapper. The three proof-docstring long-line warnings from the first complete-file
check were shortened before the final compile and delivery dry run. The required dry run checks final compilation and server preflight before handoff.

## Second reading by Q97

I independently read the complete node, its four statement-dependency records,
the dependency declarations, and all 510 lines of the delivered module. There
is no repair note for this item. The delivered node differs from the shared
node only in `lean`; there is no statement correction, new node, or dependency
module. I found no mismatch requiring a Lean change and have preserved the
worker's statement and constructions.

Source check: I opened [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf)
online and read Definition the project server (PDF p. 161), Definition the project server and
Notation the project server (p. 163), the internal-Hom setup and Remark the project server
(p. 171), Proposition the project server (p. 172), Proposition the project server
(pp. 174--177), Proposition the project server (pp. 177--178), and
Proposition the project server, Corollaries the project server--the project server and Remark the project server
(pp. 178--179). The ambient source base is an arbitrary simplicial set;
here it is the terminal point. In that case Cartesian edges are equivalences.
There is no geometric, finiteness, nonemptiness, or characteristic hypothesis
to import. The node's explicit small-universe convention is retained.

The following is my independent list of the objects, hypotheses and conclusions
in the node, matched against the Lean. Helper names and field names in this
table are in `SSet.Marked` unless otherwise qualified. Every verdict is PASS.

| Node object, hypothesis, or conclusion | Lean rendering and reading verdict |
| --- | --- |
| Nested universes and all small simplicial sets | `universe u v`, `SSet.{u}`, and the theorem's `max u v` version. No equation of independent universes is assumed; object collections and coherent nerves live in `u + 1`. PASS. |
| Quasicategories, equivalences, functor sets and cores are the recorded notions | Mathlib `Quasicategory`, `(ihom C).obj D`, and the dependency's `Enhanced.IsEquivalenceEdge` and `Enhanced.core`. PASS. |
| Marked object `(X,M)` and every degenerate edge marked | `SSet.Marked.underlying`, `.marking : Set (underlying _⦋1⦌)`, and `.degenerate` for every vertex. PASS. |
| Marking-preserving maps and their ordinary category | `Hom` is the subtype of actual simplicial maps with edge preservation; `markedCategory` uses ordinary identities and composition. PASS. |
| Product with precisely coordinatewise markings | `product` uses the actual degreewise product and the conjunction of markings; `productMap` is its coordinatewise map. PASS. |
| Minimal and maximal markings | `flat` uses exactly `Set.range (K.σ 0)` and `sharp` exactly `Set.univ`; both are functorial. PASS. |
| Natural marking of a quasicategory | `natural C` includes equivalence edges and degeneracies; `natural_marking` identifies that union with exactly equivalence edges. The union adds no edges, since a degenerate edge has its degenerate inverse and two degenerate inverse triangles even without quasicategory fibrancy. PASS. |
| Marked internal Hom with the stated Cartesian adjunction | `mapFlat` has marked maps out of `X × (Δ[n])♭`; `internalHom` marks exactly the sharp-interval extensions. `exponential` and `exponential_formula` give the canonical evaluation adjunction, in the node's `Z × X` order. PASS. |
| Sharp mapping object in every degree, with restriction operators | `mapSharp` is the Yoneda construction on `sharpSimplex ⋙ productLeft X`; its simplices are literally the marked maps in the formula. `mapSharpPre` is precomposition with `f × id`, in the required contravariant direction. PASS. |
| Complete and cocomplete category | `complete` and `cocomplete` give all limits and colimits indexed in the input simplex universe, with no nonempty-index restriction. PASS. |
| Model structure, retract closure, two-out-of-three, and lifting axioms | `model : ModelCategory Marked` has Mathlib CM1--CM5. I read its fields: CM2 is two-out-of-three, CM3 closes all three classes under retracts, CM4 gives the two liftings, and CM5 the two factorizations. Its existing instances give both mutually characterized weak factorization systems. PASS. |
| Cofibrations precisely underlying degreewise injections | `cof` tests `Function.Injective (f.val.app n)` for every `n : SimplexCategoryᵒᵖ`; `cofibrations` equates it to this same model's class. PASS. |
| Weak equivalences precisely the sharp mapping tests against every small quasicategory | `weak` quantifies over every `C : SSet.{u}` and `Quasicategory C`; the tested map is `mapSharpPre f (natural C)`. `weak_equivalences` equates this to the same model's weak equivalences. PASS. |
| Fibrations precisely RLP against trivial cofibrations | `fibrations` is equality with `(cof ⊓ weak).rlp`; no chosen lifting or stronger fibration property is required. PASS. |
| Functorial factorizations for both systems, with trivial meaning weak | `cof_triv_fib_factorization` and `triv_cof_fib_factorization` use `HasFunctorialFactorization` and intersections with `weak` on exactly the required side. PASS. |
| Both systems generated by sets | `generating_cofibrations` and `generating_trivial_cofibrations` give `I.IsSmall.{u}` and `J.IsSmall.{u}` with their required RLP equalities. I checked Mathlib's `IsSmall`: it is smallness of the set of arrows, not a smallness condition on every object. PASS. |
| Locally presentable in the stated sense | `locally_presentable : IsLocallyPresentable.{u} Marked` uses Mathlib's existential regular cardinal and small filtered generator of presentable objects; its definition also includes cocompleteness. PASS. |
| Fibrant objects precisely naturally marked quasicategories | `fibrant_objects` tests the actual model's fibrations on the canonical `toPoint X`; `IsNaturallyFibrant X` is quasicategory fibrancy together with equality of the marking and equivalence predicates. PASS. |
| Every object cofibrant and the stated terminal point | `every_object_cofibrant` covers every initial representative and every target; `terminal_point` says `IsTerminal (sharp Δ[0])`. Existence of initial objects follows from `cocomplete`, so the first assertion is not vacuous. PASS. |
| Cartesian pushout product, with the exact source and target | `IsPushoutProduct i j p` supplies the universal square from `X × Y` to `X' × Y` and `X × Y'`, and both restrictions to `X' × Y'`. `pushout_product` gives cofibrancy and triviality when `weak i ∨ weak j`. Arbitrary pushout representatives are retained. PASS. |
| Products with every marked object preserve weak equivalences | `products_preserve_weak_equivalences` asserts `weak f → ∀ Z, weak (productMap f (𝟙 Z))`. Coordinate interchange is a marking-preserving isomorphism and gives the other argument as well. PASS. |
| Enriched over simplicial sets with the sharp mapping objects | `enrichment : SimplicialCategory Marked`, `mapping_iso`, `ordinary_enrichment`, and `enrichment_composition` specify the actual ordinary maps and diagonal-parameter composition in all degrees. No arbitrary enrichment comparison is left unnormalized. PASS. |
| Tensor exactly `X × K♯` | `tensor_adjunction` has this concrete object and `tensor_formula` fixes evaluation on every parameter simplex and every restriction `a`. PASS. |
| Cotensor with the same enrichment | `cotensor_adjunction` has the concrete `internalHom (sharp K) Y`; `cotensor_formula` fixes evaluation. Together with the exponential and tensor formulas these specify the enriched adjunctions and their naturality, not just unrelated bijections. PASS. |
| Simplicial model axiom for the Kan model structure | `simplicial_pushout_product` uses arbitrary `Mono j`, `sharpMap j`, and triviality for `weak i ∨ Enhanced.IsWeakHomotopyEquivalence j`. These are precisely the recorded Kan--Quillen parameter classes. PASS. |
| Kan mapping complexes into fibrant objects | `sharp_mapping_kan` allows every marked source and every `IsNaturallyFibrant` target. PASS. |
| Natural sharp-mapping identity with the functor core | `mapping_core` uses the actual `Enhanced.core ((ihom C).obj D)`. `mapping_core_formula` fixes its inclusion by evaluation on every simplex. This supplies the natural canonical identification despite the two sides having different Lean presentations. PASS. |
| Coherent nerve of the fibrant enriched category is the specified Cat infinity model | `FibrantObjects` is the exact full subcategory; `fibrantNerve` and `quasicategoryNerve` are actual Mathlib `SimplicialNerve`s. `qcat_mapping`, `qcat_ordinary_maps`, and `qcat_composition` fix the core enrichment. `fibrant_nerve_identification`, `nerve_objects`, and `nerve_mapping` normalize the nerve isomorphism on objects and enriched maps. `cat_infinity_quasicategory` asserts the model is a quasicategory. PASS. |
| The identifications respect composition | `enrichment_composition` is the same evaluation formula as functor composition; `qcat_composition` uses `MonoidalClosed.comp`; `mapping_core_formula` and `nerve_mapping` identify these formulas. PASS. |
| Weak equivalences and fibrant objects unchanged by enlargement | The theorem's last two conjuncts are biconditionals for actual degreewise `enlarge` and `enlargeMap`, with arbitrary `v`. PASS. |
| Model structures, small colimits and functorial replacements stay in the input universe | The theorem supplies `CartesianModelStatement.{u}` and `.{max u v}`. Its factorization objects lie in the respective marked category; factoring the terminal map gives a replacement with simplices in that universe. The successor universe is used only for the collection of all objects and its nerve. PASS. |

Dependency verification: I read the definitions of `IsEquivalenceEdge` (an
inverse and the two inverse triangles), `core` (all edges equivalences), and
`IsWeakHomotopyEquivalence` (realized components and every positive based
homotopy group) in `EnhancedDiagramsCones.lean`. These are the node's objects.
I read `CoherentNerveComparisonStatement`, its recorded theorem, and
`CoherentNerveInfrastructure.QCats`: the latter is the full category of small
quasicategories and all simplicial maps. Their coherent nerve uses the same
Mathlib subset-poset thickening as this delivery. I read
`KanQuillen.weakEquivalenceStructure` and the signature of
`right_proper_kan_quillen`: its cofibrations are monomorphisms and its weak
equivalences use the same realization predicate. The size dependency is
explicitly recorded as a metatheoretic convention and supplies no missing
Lean object. No recorded interface needs a private copy or a repair.

Edge cases: the empty simplicial set admits the empty marking and all relevant
horn conditions vacuously; it is not excluded as a source or a testing
quasicategory. The category has no additive zero-object hypothesis (zero
objects, empty schemes, and ring characteristic are inapplicable). Degree zero
is included in `cof`, in every adjunction formula and in the nerve formulas.
The flat and sharp markings on `Δ[0]` coincide extensionally. A map adding
markings only is a cofibration, and no condition accidentally demands marking
reflection. Empty limits and colimits are allowed by `HasLimitsOfSize` and
`HasColimitsOfSize`. Products with the empty marked set have empty underlying
sets and markings; products with the terminal marked point retain exactly the
original marking. No chosen vertex, inhabited mapping set, fibrant source, or
fibrant parameter is assumed. All test objects have universe `u`, not an
independent potentially smaller universe; enlargement is to arbitrary
`max u v`. Explicit binders and `autoImplicit false` leave no unbound universe
or variable.

Independent searches, using different queries from the worker:

| Search | Query and result |
| --- | --- |
| LeanFinder through `msearch.py` | `marked edges simplicial sets tensor sharp Cartesian model`: eight hits about unmarked products, edges, and `SSet.instMonoidalClosed`; no marked-object definition or theorem. |
| LeanSearch through `msearch.py` | `simplicial sets with a specified subset of edges containing degeneracies`: eight hits about `SSet.Subcomplex` and degenerate simplices. A subcomplex imposes closure on all simplices and is not an arbitrary marking on edges; no match. |
| Mathlib grep through `msearch.py` | `edge.?marking|MarkedSimplicial|marked.?set|cartesian.?model`: zero hits. |
| Direct Mathlib, source, and project `rg` | Case-insensitive `marked.{0,30}(simplicial|edge)|simplicial.{0,30}mark|map.?sharp|cartesian.{0,15}model`: only unrelated project comments about Cartesian scheme/module models; no declaration of this notion. |
| Upstream names and source `rg` | `Marked|marked_point_cartesian_model|mapSharp|CartesianModelStatement` in `dag/lean_names_upstream.json` and upstream `WeilConjectures`: no hits. |
| DAG `rg` and candidate reading | Read `def-cbc-enhanced-cartesian-fibration`, the marked-anodyne and saturation nodes, simplicial interval localization, simplicial model coherent diagrams, and perfect-class recognition. None has an existing Lean marked-object definition to reuse. The first defines a marked Grothendieck construction; the remaining nodes consume or develop marked-model notions and have no Lean record. |

The owning-node helpers contain real data. There is exactly one postponed
theorem, `marked_point_cartesian_model`, whose whole proof is `sorry`; no
assertion of another DAG node is inserted as a helper theorem. I checked its
docstring against all nine node proof steps, including their named inputs,
the product inverse argument, both trivial-factor cases, sharp parameter, and
universe comparison. All declarations carry source/blueprint docstrings,
all Lean lines have at most 100 characters, and imports match the statement
dependencies and the currently recorded proof dependencies. The three unstated
proof prerequisites have no module to import and are named in the proof
docstring. `lean.statement` is verbatim the theorem signature.

Changes in this reading: appended this independent review and its searches;
no Lean or node field needed correction. Validation: prescribed `scompile.py`
compiled the sandbox and library presentations cleanly (4.2 s and 4.8 s),
without errors or warnings. `deliver2.py --no-push` then reported OK: the
delivery compiles and passes the server preflight. Final delivery repeats
those checks before pushing.
