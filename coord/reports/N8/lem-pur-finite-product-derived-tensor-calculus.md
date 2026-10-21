## Worker report

The node is stated jointly by three theorems in
`Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus`, namespace
`AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor`:
`finite_clopen_derived_calculus`, `finite_clopen_tensor_calculus`, and
`finite_clopen_scalar_calculus`. The only other postponed theorem is
`restriction_exact`, the exactness fact needed to define the degreewise derived
restriction. Every theorem has proof `by sorry`; all definitions have real data.
The node's statement, proof and dependency lists are unchanged. No statement
correction, new node, dependency repair, or disputed mathematical statement is needed.

Hypothesis and clause correspondence, after reading the complete node and file:

| Node text | Lean rendering |
| --- | --- |
| A scheme X and an arbitrary finite set I | `(X : Scheme.{t}) (I : Type w) [Finite I]`; w is independent, with no `Nonempty I`. |
| Subschemes X_i with open and closed inclusions | `Y : I → Scheme.{t}`, `j : ∀ i, Y i ⟶ X`, the two families of `IsOpenImmersion` and `IsClosedImmersion` instances. |
| Pairwise disjoint images covering X | `hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k)))` and `hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i)`. |
| Small pro-etale sites and fixed universes | Mathlib `X.ProEt` and `topology X`; site objects are in t+1, arrows in t. Coefficients and modules are in `max u (t+1)`, with arbitrary independent u. No site/Hom universe equality is assumed. |
| An arbitrary commutative ring sheaf R and its restrictions R_i | `R : Sheaf (topology X) CommRingCat.{max u (t+1)}`; `(rings.{t,u} (j i)).obj R` is actual precomposition along the component-site inclusion. Forgetting commutativity commutes definitionally with this restriction. |
| The module restrictions r_i of the gluing node | `restriction` is a transparent application of the recorded `clopenModuleRestriction` to the underlying ring sheaf. It does not replace modules, their scalar actions, or their morphisms. |
| Unbounded derived categories and degreewise restriction | `DerivedCategory (Modules R)` and `derivedRestriction`, defined as Mathlib's exact `restriction.mapDerivedCategory`. `hasDerived` chooses `HasDerivedCategory.standard` in the standard localization universe. This choice is a localization, not an assumption about the complexes. |
| Equivalence with the product of derived categories | The derived theorem supplies `E : DerivedCategory (Modules R) ≌ (∀ i, DerivedCategory (Modules R_i))` with its functor equal to the tuple of the actual derived restrictions. The target is the product of derived categories, not a derived category formed using a separately chosen Abelian structure on a product category. |
| Triangulated equivalence | Every component restriction is `IsTriangulated`; the product has componentwise shifts and distinguished triangles. With `E` this is precisely the componentwise triangulated equivalence. |
| Quasi-inverse equal to the sum of insertions | The derived theorem supplies `e`, the tuple-insertion functors `s`, and their factorization `e i = s i ⋙ E.inverse`. A bilimit bicone on the functors `Pi.eval ... i ⋙ e i` has vertex `E.inverse`; thus it expresses the asserted natural finite direct sum, without requiring an inhabited index or choosing coproduct instances. |
| r_i e_i = 1, r_i e_j = 0 for unequal indices, sum e_i r_i = 1 | The `Nonempty` natural isomorphisms, off-diagonal `IsZero` clauses, and bilimit bicone with vertex the identity in the derived theorem. These characterize the descended zero insertions canonically up to natural isomorphism. |
| H^m(r_iK) is r_iH^m(K) | The natural isomorphism between `derivedRestriction ⋙ DerivedCategory.homologyFunctor _ m` and `DerivedCategory.homologyFunctor _ m ⋙ restriction`, for every integer m. |
| Joint detection of vanishing and isomorphisms | The two universal iff clauses using `IsZero K` and `IsIso f`. They quantify over all unbounded derived objects and derived morphisms. |
| Natural ordinary tensor and unit comparisons | Each restriction is given a `Functor.Braided` structure for the existing sheaf tensors. `tensorComparison` is its inverse invertible tensorator; its unit isomorphism is `Functor.Monoidal.εIso`. The existing module tensor unit is the coefficient ring module, so the unit comparison is r_i R ≅ R_i. |
| The pure-tensor formula | The first tensor-theorem equation on `pure` at every component-site test object. `pure` is exactly the presheaf tensor's pure tensor followed by the module-sheafification unit and the recorded inverse tensor/sheafification isomorphism. Restriction here evaluates x and y on the component test object, so the right hand side is r_i x tensor r_i y. |
| Associativity, symmetry and unit compatibility | `Functor.Braided` contains the invertible tensorator, its naturality, both unit laws, associativity and the braiding law, on the prescribed monoidal structures; no tensor is transported across E to make these laws true by definition. |
| Total tensor comparison, including differential | `c` is a natural isomorphism of functors into `CochainComplex`; hence its components and inverses are chain maps. Its equation on `coefficientTensorGenerator` fixes every (p,q) summand and sends its pure tensors to their restrictions. The existing `coefficientTotalTensor` is the recorded `mapBifunctor` totalization, with the Koszul signed differential. |
| Flat iff all components flat | First iff in the tensor theorem, using the recorded `SheafOfModules.IsFlatOnSite` on both sides, not sectionwise module flatness. |
| K-flat iff all restricted complexes K-flat | Second iff in the tensor theorem, using `CochainComplex.IsKFlatIndependentCoefficients`; the complex restriction is the actual degreewise functor. No boundedness or flat-term hypothesis occurs in either direction. |
| Symmetric monoidal derived equivalence for K-flat derived tensor | Each derived restriction is `Braided` for `RingedDerivedNative.monoidal` and its prescribed Koszul symmetry. The `derivedTensorComparison` helper is its inverse tensorator. The final tensor-theorem equation identifies this tensorator on K-flat representatives with `c` via the exact localization comparisons and `RingedDerivedNative.tensorIso`. Those are the models used by the closed symmetric monoidal dependency, itself obtained by K-flat descent. The existence of E and these componentwise structures is the symmetric monoidal equivalence with the componentwise tensor on the product. |
| Every coefficient map R to S | The scalar theorem quantifies over every `a : R ⟶ S`; no flatness, surjectivity, quotient, nonzero, or nonidentity restriction is imposed. |
| S_i-linear component extension | `c i a` and `γ i a` have codomain the category of S_i-module sheaves and its derived category, not merely their underlying R_i-modules. Their functors are the existing normalized `Presentation.ordinary` and `Presentation.derived`. |
| Natural comparisons on derived objects and morphisms | `γ i a` is a natural isomorphism of functors on the entire unbounded derived category. Its K-flat representative equation uses the universal `Presentation.counit`; `scalarHomotopyComparison` is the actual degreewise lift of `c i a`. |
| Canonical scalar comparison, not an arbitrary isomorphism | The `c` pure-section equation uses the existing `sectionTensor`, in the scalar-first convention s tensor x; the universal-counit square fixes `γ` on K-flat flat-term models and therefore on all derived inputs by descent. `p`, `q`, `N`, `Ni` are universally quantified in the conclusion over any presentations and normalizations of the existing universal pairs. Their existence is the recorded successive-normalization theorem; they are not new assumptions or definitions of scalar extension. |
| Compatibility with composites of coefficient maps | The last scalar-theorem equation is the composition square for every a, b and derived K. It uses the existing `N.derived a b` and `Ni.derived`, with `scalarComposite` performing only the equality transport from functoriality of `rings.map_comp`. In particular it compares the already normalized compositors, whose representative formula is (x tensor s) tensor t ↦ x tensor psi(s)t. |
| Finite reductions and reductions from the completed ring | These are instances of the same arbitrary-a statement using the actual integral quotient maps, transitions, and completed projections. The gluing dependency `clopen_integral_coefficients` supplies the identifications and their normalization on constants and projections. Since there is no flatness hypothesis, non-flat reductions are included. Identity coefficient maps are also included in every scalar formula. |
| Empty partition and zero categories | The derived theorem explicitly asserts terminal-category equivalence for every empty component and for empty I, and `IsEmpty X` in the latter case. None of the other theorems excludes these cases or excludes the zero ring sheaf. |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`;
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale` supplies continuity.
- `Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing`:
  `clopenModuleRestriction`, its additivity theorem, `clopenRingRestriction`,
  `clopen_ringed_module_gluing`, and `clopen_integral_coefficients`. I read the
  section formulas, scalar actions, unit/counit, insertion support and bicone clauses.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  exactly Mathlib's `SheafOfModules` and Abelian structure.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`,
  `Qh`, `HasDerivedCategory.standard`; `ExactFunctor`: `mapDerivedCategory`,
  its factors, shift and triangulated instances; `HomologySequence`: the derived
  homology functor. `ShortComplex.PreservesHomology` is the cohomology proof input.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the existing
  localization tensor, its symmetry, preadditivity and colimit preservation.
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`:
  `tensorObjIsoSheafification`. `Mathlib.Algebra.Homology.BifunctorShift`:
  `CochainComplex.mapBifunctor`; no second total tensor was defined.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `IsFlatOnSite`;
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `IsKFlatIndependentCoefficients` (the full acyclic-test definition).
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `site_derived_tensor_descent_independentCoefficients` and its unique extension
  clause. `RingedDerivedTensorNative`: `monoidal`, `symmetric`, `tensorIso`;
  `RingedDerivedClosedSymmetricMonoidal`: the theorem and coherence record tying
  these to the K-flat derived tensor, with unit R[0] and prescribed constraints.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `DerivedChangeOfRingsCochainModel`, `nonempty_derivedChangeOfRingsCochainModel`.
  `SuccessiveDerivedQuotientData`: `Presentation`, `Normalization`, `sectionTensor`;
  `SuccessiveDerivedQuotientNormalization`:
  `successive_derived_quotient_normalization`. These definitions are used verbatim.
- Proof inputs imported: finite product localization `Functor.IsLocalization.pi`,
  localization's natural-transformation extension and uniqueness, the recorded
  bilinear tensor universal property, left-adjoint colimit preservation, K-flat
  resolution existence, scalar tensor cancellation, and the normalized compositor.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and the actual completed coefficient
  sheaf and quotient cone; used through the gluing node's coefficient clause.

Source checks: read Stacks `derived.tex` exact-functor Lemma 015F and unbounded
localization definition 05RU; `sites-modules.tex` sheafification-tensor Lemma
0GMW and the bilinear universal property; `sites-cohomology.tex` definitions of
K-flatness and derived tensor, K-flat resolution existence, and factorization
through K-flat complexes (06YN, 06YS, 06YU, 0G7D). The node's twelve proof steps
are distributed across the three main docstrings, with exactness in its helper.

Searches for an existing statement:

- `msearch.py ... leanfinder "Restriction to a finite clopen partition gives a
  symmetric monoidal equivalence of unbounded derived categories of sheaves of
  modules and detects K-flatness"`: eight hits, including the exact derived
  functor/factorization and sheaf equivalence APIs, no theorem with this full statement.
- `msearch.py ... loogle "Functor.mapDerivedCategory, Functor.Monoidal,
  CochainComplex.mapBifunctor"`: zero hits, unknown short identifier
  `Functor.mapDerivedCategory`; direct source searches found the fully qualified API.
- `msearch.py ... grep "mapDerivedCategory|IsKFlat|Monoidal.*Equivalence"
  CategoryTheory`: 25 hits, mainly transported monoidal categories; none matches.
- `msearch.py ... leansearch "Finite product of categories of sheaves of modules
  derived tensor restriction clopen partition"`: eight hits on ordinary sheaf
  tensor/cartesian structures, finite products and coproducts, and clopen
  topological products; no unbounded derived clopen tensor calculus match.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for finite-product derived
  tensor/clopen tensor and the exact item id found the older
  `Sheaf.Paper.FiniteClopenDerivedDecomposition`. I opened it in full: its
  statements specialize to a purity finite setting, finite/completed coefficients,
  and schemes finite type over its fixed field. They do not state this node's
  arbitrary-scheme, arbitrary-ring-sheaf and arbitrary coefficient-map calculus.
  Its restrictions were not copied; this module uses the dependency's newer general
  `Scheme.ProEt.clopenModuleRestriction`. Other matches were consumers and unrelated
  ordinary ring tensor results. No exact existing match exists.

Edge cases checked before writing: I empty forces X empty; an individual empty
component supplies a terminal derived factor; a singleton partition recovers the
identity restriction; zero coefficient sheaves and zero complexes are allowed.
No statement assumes flat coefficients or bounded complexes. In particular the
non-flat reductions Z → Z/4 → Z/2 are included in the scalar formulas; their
comparison is derived and is not asserted to be an ordinary flat base change.
An arbitrary finite index type in a separate universe is retained. The site object
and morphism universes remain t+1 and t. Two overly specialized high-priority
sheafification instance attributes are disabled within this module so the existing
independent-coefficient instances are selected; their conclusions are unchanged and
no local statement-only notation or local instances are introduced.

Validation: each module is compiled separately by the prescribed `scompile.py`
against the live published build; the last complete compile before adding explicit
proof imports took 24.7 s for the sandbox and 25.3 s for the library file, with no
warnings or errors. Final compile and delivery preflight results are recorded below.

## Final worker clause audit

I reopened the node and reread the complete finished module for the final worker
audit. The maintainer supplies the independent review after delivery. I checked every
row of the table against the signatures. The tensor and scalar comparisons are
natural functor isomorphisms, not unrelated object isomorphisms. The derived tensor
normalization square uses the exact-functor localization comparison on both inputs
and the prescribed total tensor; the scalar normalization square uses the universal
left-derived counits, and the final square uses the existing normalized compositor.
The two finite bicones state both the identity decomposition and the sum formula
for the inverse. Empty partitions and off-diagonal zero insertions remain present.

Elaboration repairs during the reading: ring-forgetful functors, component module
categories and all restriction uses now carry explicit universe arguments, avoiding
accidental equality with the smaller site universe. The exactness and standard
localization helpers select the recorded constructions. The final file has no
`#check`, `example`, local notation, private declaration, or proof left inside a
constructor as `sorry`. All postponed proofs are named and documented. I found no
mathematical statement change or missing hypothesis/clause after these repairs.

Final validation: the completed module, including all explicit proof imports,
compiled cleanly in 19.1 s (sandbox) and 18.6 s (library path). The prescribed
`deliver2.py --no-push` printed OK: preflight and per-file compile passed.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
