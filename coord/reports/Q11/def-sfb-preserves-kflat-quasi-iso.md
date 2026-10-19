## Worker report

The module `Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso` states the
entire node at its stated generality. It defines
`CochainComplex.IsKFlatForTotalTensor` and
`CategoryTheory.Functor.PreservesTotalTensorKFlatQuasiIso`, and states the final
exact-functor assertion as
`CategoryTheory.Functor.preservesTotalTensorKFlatQuasiIso_of_exact` with `sorry`.
The definition bodies are actual propositions. There are no other postponed facts,
new nodes, dependency repairs, or changes to the natural-language statement.

Clause-by-clause correspondence:

- The abelian category C is `{C : Type uC} [Category.{vC} C] [Abelian C]`.
  `MonoidalCategory C` supplies the tensor and unit. `MonoidalPreadditive C`
  is precisely additivity of tensoring in both variables; it provides the
  `curriedTensor` additive/zero-preserving instances used by the total construction.
- Countable coproducts are `[HasCountableCoproducts C]`, whose definition is
  existence of colimits of discrete diagrams on countable index types. Its
  universe transport instance covers countable index sets in every universe.
  No preservation of infinite coproducts or existence of flat resolutions is assumed.
- Every complex is `CochainComplex C ℤ`; its morphisms are Mathlib's chain maps.
  Every quasi-isomorphism condition is Mathlib's `QuasiIso`, meaning invertibility
  of all induced homology maps, as required by the abstract-derived-category node.
  This statement needs complexes and quasi-isomorphisms, not a choice of localization,
  so no `HasDerivedCategory` hypothesis is imposed.
- The total tensor and tensor maps are the existing
  `HomologicalComplex.tensorObj` and `HomologicalComplex.tensorHom`. Reading their
  implementations in `Mathlib.Algebra.Homology.Monoidal` and `Bifunctor` shows that
  they are `mapBifunctor` and `mapBifunctorMap` for `curriedTensor C`. The total object
  is the coproduct on the fiber of `(p,q) ↦ p+q` over n. This fiber is countable,
  so the required `HasTensor` instances are synthesized from countable coproducts.
  In `ComplexShapeSigns`, `TensorSigns (ComplexShape.up ℤ)` has epsilon one for
  the first differential and `p.negOnePow` for the second. Thus the differential
  on a summand is exactly the displayed `d_P ⊗ id + (-1)^p id ⊗ d_Q`.
  `Bifunctor.d₁_eq`, `d₂_eq`, `ι_D₁`, and `ι_D₂` identify these components;
  `mapBifunctorMap` is induced by `a.f p ⊗ₘ b.f q` into the same-index summand.
  Their existing construction supplies square-zero and functoriality, so no
  reimplementation or postponed construction is used.
- Both K-flat tests occur as the two conjuncts of `IsKFlatForTotalTensor`:
  for every morphism `s : Q ⟶ Q'`, `QuasiIso s` implies `QuasiIso (tensorHom (𝟙 P) s)`
  and, respectively, `QuasiIso (tensorHom s (𝟙 P))`. These are precisely the actions
  of the two functors formed by fixing one input of `map₂CochainComplex`.
  Both tests are retained because the node does not assume symmetry.
- D is separately `{D : Type uD} [Category.{vD} D] [Abelian D]`, with independent
  object and morphism universes. It has no monoidal or coproduct hypothesis.
- F is `(F : C ⥤ D) [F.Additive]`. The preservation class requires both
  `P.IsKFlatForTotalTensor` and `P'.IsKFlatForTotalTensor`, then every
  `s : P ⟶ P'` with `[QuasiIso s]`. The conclusion is precisely
  `QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s)`.
  It makes no assertion about K-flatness of F(P).
- The last assertion has exactly `[F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]` and concludes the preservation property. Its sole
  `sorry` is the whole proof of this named theorem, belonging to this node's
  final sentence. The docstring gives the cohomology comparison, naturality,
  inverse preservation, and restriction to the K-flat endpoints argument.

Dependency inspection and use:

- `def-sp-abelian`: Mathlib leaf `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`; read its full class and docstring.
  It supplies the abelian-category binders and homology infrastructure.
- `def-weil-pbc-category-colimit`: read `colimit`, `colimit.cocone`, and `colimit.ι`
  in `Mathlib.CategoryTheory.Limits.HasLimits` (generated as duals of limits).
  The binary total tensor uses these chosen coproduct colimits through Mathlib's
  graded-object/total-complex API; `Shapes.Countable` supplies exactly the
  countable existence interface. No separate colimit definition is introduced.
- `def-weil-abstract-derived-category`: read the recorded `DerivedCategory`,
  `HasDerivedCategory`, and `Q` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`;
  that module is publicly imported. Its complex and quasi-isomorphism APIs are reused.
- Proof dependency `lem-weil-pbc-exact-functor-complex-cohomology`: read
  `CategoryTheory.Functor.homologyFunctorIso` and `preservesHomologyOfExact` in
  `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`; this module is explicitly
  imported for the future proof. They give the comparison used in the proof docstring.

Existing-definition searches (2026-10-16):

- `msearch.py` LeanFinder: “K-flat cochain complex and additive functor preserving
  quasi-isomorphisms between K-flat complexes” returned derived exact functor
  liftings, `mapDerivedCategoryFactors`, and `DerivedCategory.Q`, not either
  predicate under the node's minimal ambient assumptions.
- `msearch.py` Loogle: `HomologicalComplex.tensorObj, HomologicalComplex.tensorHom,
  HomologicalComplex.quasiIso_map_of_preservesHomology` returned no matches for
  the combined query; the exact tensor declarations were found and read locally.
- `msearch.py` grep `KFlat|kFlat|PreservesKFlatQuasiIso|HasTensor` in
  `Algebra/Homology` returned five hits in `Monoidal.lean`, for binary total tensor
  and the associator requirements, but no K-flat predicate in Mathlib.
- `msearch.py` LeanSearch: “K-flat complexes tensor quasi-isomorphisms additive
  functors” returned `quasiIsoAt_map_of_preservesHomology`, `QuasiIso`, and
  localization functors. These cover quasi-isomorphisms and the exact-functor
  consequence, not the new general preservation predicate.
- `rg` for `PreservesKFlatQuasiIso|def kFlat|KFlat|K-flat` in project and
  upstream sources found the existing upstream
  `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs` class
  `CategoryTheory.Functor.PreservesKFlatQuasiIso`, the generic
  `CategoryTheory.MorphismProperty.kFlat` in
  `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`, and module-sheaf
  `CochainComplex.IsKFlat` in `Sheaf.Algebra.Homology.KFlat`. Read their actual
  signatures and documentation. The first two need a monoidal structure on
  complexes; the available construction of that structure additionally requires
  `HasTensor₄ObjExt`, `HasGoodTensor₁₂Tensor`, and `HasGoodTensorTensor₂₃`.
  These are not hypotheses of this node and cannot be silently added.
  The sheaf-specific predicate concerns sheaves of modules over a commutative
  ring, rather than every monoidal abelian category. None is an exact match.
  This module generalizes the two-sided test to the binary tensor API and does
  not construct a second total tensor or specialize to module sheaves.
- `rg` for the proposed names in all Mathlib, upstream `WeilConjectures`, and
  project `lean/Sheaf` found no collisions. The upstream-name table gave no
  `kFlat`/`PreservesKFlatQuasiIso` entry. Searching the node ID in upstream sources
  found no declaration carrying this blueprint node. The current blueprint source
  was opened and agrees with the node's two-sided preservation definition.

Edge cases checked before writing: the zero complex and the zero abelian category
are not excluded; no nonzero tensor unit, nonempty coefficient object, boundedness,
flat-resolution existence, symmetry, or field characteristic is required. All
integer degrees, including negative degrees and zero, use the standard sign rule.
Each degree's indexing fiber is countably infinite even for unbounded inputs;
countable coproducts suffice and tensoring need not commute with them. A zero
additive functor and identity functor satisfy the stated semantic preservation test.
There is no monoidal hypothesis on D or any asserted K-flatness of its image.
No statement dispute or node fault was found.

Validation: `scompile.py Q11 def-sfb-preserves-kflat-quasi-iso` compiled the module
both as an isolated sandbox file and at its intended library path, with no errors
or warnings. A final required `deliver2.py --no-push` dry run is recorded below.

## Second reading by Q11

I independently read the node, the complete delivered module, its three statement
dependencies and proof dependency, and the actual declarations listed below.
The source is the blueprint definition at order 1611, not a Stacks definition of
module sheaves. I also read its parent unit's left-derived-functor paragraph:
that paragraph supplies countable coproducts. The node already makes that
requirement explicit. Stacks homology.tex, lemma-exact-functor (010N), assumes
only abelian source and target categories and proves the finite-limit/colimit
characterization. Stacks derived.tex, lemma-right-derived-exact-functor (015F),
explicitly applies to unbounded complexes and says exact functors preserve
quasi-isomorphisms. Neither adds a coefficient, boundedness, or size hypothesis.
There is no stage-2 statement_change or repair note on this item.

Object/hypothesis/conclusion checklist, in the node's order:

1. Abelian category C: `{C : Type uC} [Category.{vC} C] [Abelian C]`.
   PASS. I read `CategoryTheory.Abelian` in Mathlib's Abelian.Basic: its
   preadditivity, finite products, kernels/cokernels, and normal mono/epi
   requirements give precisely def-sp-abelian, including zero and biproducts.
2. Monoidal tensor and unit, additive in each variable:
   `[MonoidalCategory C] [MonoidalPreadditive C]`. PASS. The latter's four
   zero/addition whiskering laws are exactly the two additivity requirements;
   its curriedTensor instances impose no additional exactness or symmetry.
3. Countable coproducts: `[HasCountableCoproducts C]`. PASS. I read
   Shapes.Countable's class and its Shrink-based instance for arbitrary-universe
   countable index types. This is coproduct existence, with no preservation
   condition. The chosen coproduct is the colimit of a discrete diagram, using
   def-weil-pbc-category-colimit's existing `colimit`/`colimit.ι` API.
4. Integer cochain complexes, chain maps, and quasi-isomorphisms:
   `CochainComplex C ℤ`, `s : Q ⟶ Q'`, and `QuasiIso s`. PASS. I read the
   recorded DerivedCategory.Basic declarations `HasDerivedCategory`,
   `DerivedCategory`, and `DerivedCategory.Q`, and QuasiIso's degreewise
   homology formulation. The item uses only the complexes and morphism
   property, so it correctly requires no chosen derived localization.
5. The degree-n direct-sum total tensor: the actual objects at the endpoints
   of `HomologicalComplex.tensorHom` are `HomologicalComplex.tensorObj`.
   PASS. I followed Monoidal.tensorObj to Bifunctor.mapBifunctor, then
   HomologicalComplex₂.total and GradedObject.mapObj. Its indexing fiber is
   exactly `{(p,q) : ℤ × ℤ | p + q = n}` and mapObj is its coproduct.
6. Differential and tensor maps: PASS. ComplexShapeSigns' TotalComplexShape
   uses addition for π, ε₁ = 1, and ε₂(p,q) = p.negOnePow for `.up ℤ`.
   Bifunctor.d₁_eq/d₂_eq and ι_D₁/ι_D₂ therefore give exactly the node's two
   differential components; total.d is their sum. The formula
   ι_mapBifunctorMap identifies the induced tensor map on each summand with
   `a.f p ⊗ₘ b.f q` into that same-index summand. Existing Mathlib proofs
   supply square-zero and functoriality. No new construction is necessary.
7. K-flatness tests both functors on every quasi-isomorphism: the two conjuncts
   of `IsKFlatForTotalTensor` quantify over arbitrary `Q`, `Q'`, and `s`,
   and test respectively `tensorHom (𝟙 P) s` and `tensorHom s (𝟙 P)`.
   PASS. Neither direction is omitted; neither assumes the test endpoints
   K-flat. The fixed-factor functors are the existing map₂CochainComplex.
8. Separate abelian target D and additive functor F:
   `{D : Type uD} [Category.{vD} D] [Abelian D]`, `(F : C ⥤ D)` and
   `[F.Additive]`. PASS. D has independent universes and no tensor or
   coproduct requirements.
9. Preservation property: `PreservesTotalTensorKFlatQuasiIso.quasiIso_map`
   takes both K-flat endpoint hypotheses and every `s : P ⟶ P'` with
   `[QuasiIso s]`, then asserts
   `QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s)`.
   PASS. This is the termwise image map, and asserts nothing about image
   K-flatness. Instance-style binding of QuasiIso changes no quantifiers.
10. Every exact F has the property:
    `preservesTotalTensorKFlatQuasiIso_of_exact` assumes `[F.Additive]`,
    `[PreservesFiniteLimits F]`, and `[PreservesFiniteColimits F]` and concludes
    `F.PreservesTotalTensorKFlatQuasiIso`. PASS. I read the proof dependency's
    recorded `Functor.homologyFunctorIso` and `preservesHomologyOfExact` in
    ShortComplex.PreservesHomology, including naturality. Its specialization
    to the degreewise short complex gives the comparison used in the docstring.
    The docstring follows the node: comparison, functorial inverse, conjugation,
    and restriction to K-flat endpoints. Its proof is the sole `sorry`.

Edge cases: the zero category, zero complexes, zero functor, and all integer
degrees, including 0 and negative degrees, are included. Empty coproducts are
covered by HasCountableCoproducts; although the displayed degree fiber itself
is nonempty, all its summands may be zero. No boundedness, nonzero unit,
resolution existence, symmetry, field, or characteristic assumption occurs.
Empty schemes and geometric indexing sets introduce no extra case in this
abstract categorical statement. The four declared universe variables are
independent and bound; countability does not restrict C's object or morphism
universe. No extra tensor instance is passed implicitly as a hypothesis.

Independent reuse searches (2026-10-16):

- LeanFinder via msearch.py: "total tensor product of unbounded cochain
  complexes preserving quasi-isomorphisms in both variables K flat". Returned
  HasGoodTensor₁₂/₂₃, their instances, and factorization/shift declarations;
  no preservation predicate at this generality.
- Loogle via msearch.py: `HomologicalComplex.tensorHom`. Returned the exact
  Mathlib binary total-tensor morphism used here; I read its full local source.
- LeanSearch via msearch.py: "An additive exact functor maps quasi-isomorphisms
  of cochain complexes to quasi-isomorphisms". Returned
  quasiIso_map_of_preservesHomology and derived-localization declarations;
  these cover the exact-functor argument but neither new predicate.
- Independent rg searches of all Mathlib, upstream WeilConjectures, and
  project lean/Sheaf used declaration patterns for `KFlat`/`kFlat`,
  `tensorHom.*QuasiIso`, and `QuasiIso.*tensorHom`, as well as exact-name
  collision searches including dag/lean_names_upstream.json. No exact match
  or name collision was found. I opened upstream LeftDerivedFunctor.Defs:
  PreservesKFlatQuasiIso requires the three extra graded tensor interfaces
  (quadruple tensor existence and the two triple coproduct-preservation
  interfaces). Generic MorphismProperty.kFlat requires a monoidal structure
  on the category of complexes, whose Mathlib construction needs those
  additional interfaces. They are not implied by this node's assumptions.
  I also opened project KFlat.lean: its predicates quantify over sheaves of
  modules over commutative ring sheaves, a specialization of this node's C.
  The existing binary total tensor is reused; no second tensor is defined.

No mismatch was found, and no Lean or natural-language node content was
changed. There are no new nodes or dependency modules to review. Definitions
have real predicate bodies, every declaration has its source/blueprint
docstring, no statement is proved, and the node's lean.statement is verbatim
the class signature in the file. I preserved the correct first-worker work
and added this independent reading only.

Validation: the required scompile.py command compiled the sole delivered file
in sandbox mode (4.6 s) and at its intended module path (5.3 s), with exit 0
and no warnings or errors. All lines fit 100 characters. Delivery preflight
and push are performed after this report is saved.
