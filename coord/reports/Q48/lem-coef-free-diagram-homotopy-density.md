## Worker report

Item: `lem-coef-free-diagram-homotopy-density`, stage 2, Q48.
Module: `Sheaf.CategoryTheory.FreeDiagramHomotopyDensity`.
Main declaration: `HomotopicalAlgebra.FreeDiagram.free_diagram_homotopy_density`.
Helper: `HomotopicalAlgebra.FreeDiagram.freeDiagram`.

The module states the node's generation assertion, with a single `sorry` and no proved
auxiliary theorem. The helper is the actual Mathlib evaluation left adjoint lifted to
the existing full subcategory of cofibrant objects. Its data are fully defined.
There are no new nodes, dependency repairs, or statement corrections.

The previous dispatcher result concerned Q81's stage-1 split. The current node has
`status: split` and a Q81 stage-1 review, but no `lean` binding. This delivery supplies
its stage-2 statement without resplitting or changing the statement or proof.

### Hypotheses and objects

- The node's universe U is `u`. The ordinary category is `(M : Type v) [Category.{u} M]`.
  Object size `v` is independent of hom size `u`; no equality of these universes is imposed.
  `HasLimitsOfSize.{u, u} M` and `HasColimitsOfSize.{u, u} M` are exactly all U-small
  ordinary limits and colimits, not only finite ones.
- The three classes C,F,W are the fields of `CategoryWithCofibrations M`,
  `CategoryWithFibrations M`, `CategoryWithWeakEquivalences M`. These structures contain
  only their indicated class, so bundling them adds no mathematical hypothesis.
  Their projections are `cofibrations M`, `fibrations M`, `weakEquivalences M`.
- W retract closure and two-out-of-three are the instances
  `(weakEquivalences M).IsStableUnderRetracts` and `.HasTwoOutOfThreeProperty`.
- Both WFS are `IsWeakFactorizationSystem (cofibrations M) (trivialFibrations M)` and
  `IsWeakFactorizationSystem (trivialCofibrations M) (fibrations M)`. Mathlib defines
  `trivialFibrations M` as F intersect W and `trivialCofibrations M` as C intersect W.
  The WFS class asserts both lifting characterizations and arrow factorization.
  The two corresponding `HasFunctorialFactorization` instances assert functoriality.
  There is no added `ModelCategory`, properness, combinatoriality, simplicial enrichment,
  projective model structure, or universe-sized completeness hypothesis.
- The initial object is the chosen Mathlib initial object, supplied by the colimit
  hypothesis. `IsCofibrant X` abbreviates `Cofibration (initial.to X)`; hence
  `CofibrantObject M` is exactly the existing full subcategory M_c specified by the node.
- `(I : Type u) [Category.{u} I]` specifies a U-small category, allowing it to be empty.
- `A : SSet.{max u v t}` is the enlarged-universe infinity localization. The map `q`
  has source `FiniteReedy.largeNerve (I ⥤ CofibrantObject M)`.
- `hq : FiniteReedy.IsLocalization
  (((weakEquivalences M).inverseImage CofibrantObject.ι).functorCategory I) q`
  uses exactly componentwise W on strict cofibrant diagrams. The inverse image along
  the full inclusion tests W on the underlying M-morphism. `functorCategory I` tests
  every natural-transformation component. The recorded localization interface asserts
  quasicategory structure, inversion of these arrows, and the equivalence on entire
  coherent functor categories for every enlarged-universe quasicategory target. This
  is not ordinary categorical localization or only an equivalence on cores.
- `hcolim : HasSmallCoherentColimits.{u, max v t} A` is exactly the separately recorded
  notion of all U-small coherent colimits. It quantifies over `K : SSet.{u}`, lifts K
  degreewise to the ambient universe, and requires an actual colimiting cocone for
  every diagram. The auxiliary universe `t` imposes no size relation on `u` or `v`.

### Free diagrams and every conclusion clause

- `evaluationLeftAdjoint M i` is read directly from Mathlib's evaluation adjunction
  module. Its value at `X.obj` and `j` is the chosen coproduct over `i ⟶ j`. Its map
  on `f : j ⟶ j'` is `Sigma.desc (fun g => Sigma.ι _ (g ≫ f))`, exactly the node's
  identity-on-summands formula, including its order of composition.
- The first conclusion supplies `hE : ∀ i X j, IsCofibrant (...)`. These are only
  proofs that the already constructed coproduct values belong to M_c, as is implicit
  in the node's instruction to define E_iX in `Fun(I,M_c)`. They are a conclusion,
  not an added hypothesis. `freeDiagram M I i X (hE i X)` uses
  `(cofibrantObjects M).lift` on the actual evaluation left adjoint. It makes no choice
  of an arbitrary diagram or arbitrary map. All possible membership proofs give the
  same data by proof irrelevance. This first existential therefore adds no independent
  assertion beyond the node's well-definedness of its stipulated free diagrams.
- A predicate `P : A _⦋0⦌ → Prop` specifies the full subcategory on those vertices;
  the dependency's `fullSubcomplex` retains exactly all simplices with these vertices.
  Quantifying over every P expresses the node's explicitly equivalent formulation
  using every full replete colimit-closed subcategory.
- Repleteness is
  `∀ e, IsEquivalenceEdge A e → P (A.δ 1 e) → P (A.δ 0 e)`.
  Here delta 1 is the source and delta 0 is the target. Since inverse edges are
  equivalences too, this is closure under equivalences in both directions.
- Colimit closure quantifies over `K : SSet.{u}`, the actual ambient lift
  `SSet.uliftFunctor.{max v t}.obj K`, every diagram `D`, and every colimiting cocone
  `c : (coconeCategory D) _⦋0⦌`. Its premises require all diagram vertices in P, and
  its conclusion `P c.1.1` is membership of this cocone's actual apex. This is closure
  under all U-small coherent colimits, without a restriction to ordinary nerve shapes,
  finite shapes, nonempty shapes, or a separately assumed collection of chosen colimits.
- Containment of generators is exactly
  `∀ i X, P (FiniteReedy.object q (freeDiagram M I i X (hE i X)))`.
  `FiniteReedy.object` takes the actual zero-simplex image of the strict free diagram.
- The conclusion `∀ a : A _⦋0⦌, P a` says that this full subcategory is all of A.
  It implies in particular containment of every localized strict diagram, and is
  equivalent to the stated smallest full replete colimit-closed subcategory assertion.
  No comparison with a coherent functor category is claimed.

### Reused declarations and imports

Read the recorded `SSet.Enhanced.coneCategory` declaration and its docstring in
`Sheaf.CategoryTheory.EnhancedDiagramsCones`, together with its comma construction
and the mapping, equivalence and colimit interfaces used here. The definitions use the
internal hom, actual
comma cone/cocone simplicial sets, equivalence edges, and `IsColimiting` as initiality
in the actual coherent cocone category. This module uses its `IsEquivalenceEdge`,
`coconeCategory`, and `IsColimiting` without private substitutes.

Added two already landed nodes to `stmt_deps`, without changing any other node:

- `def-coef-coherent-localization-interface`, whose recorded existing module is
  `Sheaf.CategoryTheory.FiniteReedyLocalization`: `HomotopicalAlgebra.FiniteReedy`
  declarations `largeNerve`, `IsLocalization`, `object`. Read the full source signatures
  and docstrings. Only their definition interface is used; the finite-Reedy theorem is
  not used. This avoids restating localization or replacing it with ordinary localization.
- `lem-coef-cocomplete-cofibration-localization`, module
  `Sheaf.CategoryTheory.CocompleteCofibrationLocalization`, declaration
  `SSet.Enhanced.HasSmallCoherentColimits`. The local older checkout lacks this source;
  read its current full source using `scompile.py --source`. Its independent small
  universe and degreewise lifted shapes exactly match this item's colimit hypothesis.
  This is also already a proof dependency of the item.

Mathlib supplies `CofibrantObject`, `cofibrantObjects`, `IsCofibrant`, the full-subcategory
lift, `evaluationLeftAdjoint`, morphism-property inverse image and functor category,
WFS, functorial factorization, and the standard limits/colimits classes. Read their
signatures and relevant docstrings in Bifibrant, IsCofibrant, ObjectProperty/FullSubcategory,
Adjunction/Evaluation, MorphismProperty/WeakFactorizationSystem and Factorization.

The other stated proof dependencies are imported without `public`:
`EnhancedFunctorConeCalculus`, `JoinSliceRightFibration`, `RightFibrationMorphismSpace`,
`SpacesHomotopyFiberDetection`, and the Mathlib LiftingProperty/BrownLemma matches.
The remaining proof-dependency nodes have no published Lean binding in the current
DAG and introduce no statement notions here; they are named in the eight-step proof
docstring, not given invented theorem declarations or nonexistent module imports.

### Edge cases and semantic checks

- I empty: the generator premise is vacuous, but colimit closure still tests the empty
  simplicial set. Its initial-object apex must lie in P. The strict diagram category
  and its localization are terminal, so repleteness yields all vertices. There is no
  nonemptiness binder that would remove this case.
- I terminal: Hom(*,*) is a singleton and the free functor is canonically the identity;
  the result reduces to essential surjectivity of the localization.
- I discrete: generators are a copy of X at their supporting object and initial
  objects elsewhere. Empty Hom sets give genuine empty coproducts, whose cofibrancy
  is included in `hE`.
- I an arrow category: the free diagram at its source gives the identity transition;
  the free diagram at its target gives the initial-to-X transition. This checks the
  direction of `g ≫ f` in the reused free functor.
- K empty: the diagram-vertex membership premise is vacuous. The actual colimiting
  cocone condition forces P to contain an initial object, so P = false is not a
  spurious closed subcategory. K is not required to be a quasicategory or a nerve.
- W all morphisms, or W the isomorphisms: both use the same genuine coherent
  localization predicate; no saturation or diagram comparison is assumed implicitly.
- The initial object and any zero object are included. Independent object universe v,
  ambient universe t, and hom/index universe u are all retained. No arbitrary map,
  Nonempty data choice, or hypothesis identifying two universes is introduced.

Source read online: Cisinski's CatLR.pdf July 30, 2026 revision, Theorem 7.9.8,
printed pp. 409--412, in particular the relative-slice comparison (the project server), small
final indexing argument, colimit comparison (the project server)--(the project server), and conservativity.
The eight proof steps in the theorem docstring track the node's eight proof steps.
No STATEMENT-DISPUTED or node fault remains.

### Searches and validation

- `msearch.py leanfinder`, query: "Free evaluation diagrams generate the infinity
  localization of strict diagrams in a model category under small coherent colimits".
  Eight hits concerned ordinary cofibrant homotopy-category resolutions/localizers,
  the Joyal lifting trick, and ordinary localization. Their ordinary HoCat types do
  not state generation in a quasicategory under coherent colimits.
- `msearch.py loogle`, query: `"CofibrantObject", "colimit"`: zero hits.
- `msearch.py grep`, query: `free.*diagram|diagram.*homotopy.*dens`, subdirectory
  AlgebraicTopology: zero hits.
- `msearch.py leansearch`, query: "Free evaluation diagrams generate the infinity
  localization of strict diagrams under small coherent colimits": eight hits, including
  `evaluationJointlyReflectsColimits`, formal coproduct evaluation, ordinary colimit
  cocones, finite-colimit preservation for modules, and ordinary localization
  universal properties. These are ordinary-category facts and do not state this node.
- `rg` in the upstream WeilConjectures tree for the item id, free diagrams and homotopy
  density gave no match. `rg` in `lean/Sheaf/CategoryTheory` found only the proof-plan
  reference in `SmallDiagramModelRectification` and the ordinary free-evaluation
  adjunction reference in `SmallModuleDiagramsGrothendieck`. The rectification theorem
  is a downstream consumer, not the internal generation assertion and is not imported.
- Read Mathlib `Adjunction/Evaluation.lean:38--48`: the free diagram construction is
  already present and reused, not redefined by private coproduct data.
- `scompile.py Q48 lem-coef-free-diagram-homotopy-density
  lean/Sheaf/CategoryTheory/FreeDiagramHomotopyDensity.lean` passed with no errors or
  warnings. Its required CocompleteCofibrationLocalization overlay also compiled.
  `autoImplicit` is false; every universe and variable is explicitly bound.
- The node's Lean statement is extracted verbatim from the theorem keyword through
  its signature, before `:=`, and JSON uses indent 1, UTF-8 and a final newline.

## Second reading by Q48

The node statement was checked clause by clause against Cisinski, *Higher Categories
and Homotopical Algebra*, Theorem 7.9.8, formulas (the project server)--(the project server), pp. 411--412.

- Objects and ambient hypotheses: `M : Type v` with `Category.{u} M`, all
  `u`-small limits and colimits, the three Mathlib classes
  `CategoryWithCofibrations`, `CategoryWithFibrations`, and
  `CategoryWithWeakEquivalences`, retract closure and two-out-of-three for `W`, and
  the two weak factorization systems with their functorial factorizations. These are
  exactly the node's classes C, F, W and model hypotheses; no properness,
  combinatoriality, projective structure, or universe equality is added.
- Index and localization: `(I : Type u) [Category.{u} I]`, the enlarged simplicial
  localization target `A`, map `q` from the enlarged nerve of
  `I ⥤ CofibrantObject M`, and `hq : FiniteReedy.IsLocalization` for the inverse
  image of componentwise weak equivalences. This renders the node's `W_I` and full
  coherent functor-category localization, rather than an ordinary or core-only
  localization.
- Colimits: `hcolim : HasSmallCoherentColimits.{u, max v t} A` quantifies over every
  `u`-small simplicial shape and every actual colimiting cocone, with the prescribed
  degreewise universe lift. It includes the empty shape and does not choose a smaller
  class of colimits.
- Free diagrams: `freeDiagram` is Mathlib's `evaluationLeftAdjoint` lifted through
  `cofibrantObjects`; its value at `j` is the coproduct over `i ⟶ j`, and its map on
  `v : j ⟶ j'` sends the `u` summand to `u ≫ v`. The existential `hE` supplies exactly
  the cofibrancy proofs required by this lift and adds no construction or hypothesis.
- Closure conclusion: the predicate `P` is closed under equivalence edges and under
  every specified coherent colimit, contains every localized free diagram
  `FiniteReedy.object q (freeDiagram ...)`, and therefore contains every vertex of
  `A`. Quantifier order and all clauses agree with the node; no comparison with a
  coherent functor category is concluded.

Edge cases were checked: empty `I` and empty colimit shape, terminal and discrete `I`,
the arrow category, empty Hom-indexed coproducts, zero/initial objects, all-map and
isomorphism choices for `W`, and independent universes `u`, `v`, and `t`. No
nonemptiness assumption or hidden universe identification excludes a source case.

Searches were repeated in Mathlib and the upstream `WeilConjectures` tree by name and
concept, using `msearch.py` (`leanfinder`, `loogle`, `leansearch`) and `rg`. Results
were ordinary evaluation adjunctions, ordinary localizations, and cofibrant-object
facts; none states this coherent homotopy-density assertion. The existing declarations
`evaluationLeftAdjoint`, `FiniteReedy.IsLocalization`, `FiniteReedy.largeNerve`,
`FiniteReedy.object`, `SSet.Enhanced.coconeCategory`, `IsColimiting`, and
`HasSmallCoherentColimits` were read and reused. No duplicate definition or hollow
definition was found.

No mismatch was found and no Lean or DAG correction was needed. The worker module and
node copy already contain the exact recorded signature and the required source and
blueprint docstrings. `scompile.py` passed for
`Sheaf/CategoryTheory/FreeDiagramHomotopyDensity.lean` with no errors or warnings.
