## Worker report

The module `Sheaf.CategoryTheory.LinearScalarLocalization` states
`CategoryTheory.exists_linear_scalarLocalization_category`, with one `sorry` and no definitions
or proofs. The node's statement, dependencies and proof are unchanged; only `lean` is added.

The source read was
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-rationalization-karoubi.md`:
the displayed tensor-Hom formula and the explicit requirement of raw localization, without
Karoubi completion. All five proof steps of the DAG node appear in the theorem's docstring.

Hypotheses and conventions:

- The commutative ring is `(R : Type r) [CommRing R]`, the element is `(p : R)`, and its
  localization is Mathlib's `Localization.Away p`, including its actual ring and R-algebra
  structures. No nonzero, nontriviality, domain, or regular-element assumption is added.
- The original category is `(C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]`.
  No additive-category, triangulated-category, smallness, or finiteness hypothesis is added.
- H(K,L) is `Localization.Away p ⊗[R] (K ⟶ L)`. This is the scalar-first convention of the
  recorded module-base-change dependency. Tensor symmetry identifies it with the node's
  `(K ⟶ L) ⊗[R] Localization.Away p`, with its right-factor scalar action.
- Localized objects are `ULift.{0} C`, a single-field wrapper with constructor `ULift.up` and
  inverse `.down`, in the same universe as C. Every object is uniquely `ULift.up K`: this
  changes no objects and adds no summands or idempotents. The wrapper keeps original and
  localized category instances distinct, including when their Hom universes coincide.
  The existential equivalences `e K L` identify the localized Hom modules with exactly H(K,L).
  Transport through `e` and `.down` gives literally the tensor-Hom category on C. Thus no
  alternative category or loss of tensor morphisms is permitted by this presentation.

Clause-by-clause correspondence:

1. `∀ K L M, ∃! β : H(L,M) →ₗ[A] H(K,L) →ₗ[A] H(K,M), ...` states existence and
   uniqueness among A-bilinear maps. The universal pure-tensor equation is
   `β (a ⊗ₜ[R] f) (b ⊗ₜ[R] g) = (a * b) ⊗ₜ[R] (g ≫ f)`.
   Lean writes composition in diagrammatic order, hence `g ≫ f` is the node's `f ∘ g`.
2. The existential `d : Category.{max r v} (ULift.{0} C)` includes associativity and both
   identity laws. The existential `a : Preadditive ...` and `l : Linear A ...` give the
   abelian Hom groups and the A-bilinear composition. The equivalences `e` are A-linear
   bijections from the actual tensor modules. Their two displayed equations specify that
   the identity is the image of `1 ⊗ 𝟙 K` and composition has exactly the formula in clause 1.
   Consequently the transported composition is its unique β. The category axioms supply
   the laws on all tensors, not just on pure tensors.
3. The existential `lr : Linear R ...` is constrained by
   `r • f = (algebraMap R A r) • f` on every localized Hom: it is exactly restriction of
   scalars, not an arbitrary R-action. The actual functor `Q : C ⥤ ULift.{0} C` has
   `Q.obj K = ULift.up K` and `HEq (Q.map f) (e K L (1 ⊗ₜ[R] f))`.
   Its `Functor` structure includes preservation of identities and composition.
   `Q.Additive ∧ Q.Linear R` is precisely R-linearity on Hom modules.
4. For every pair of actual endofunctors T,S with `[T.Additive] [T.Linear R]` and the
   strict inverse equations `T ⋙ S = 𝟭 C` and `S ⋙ T = 𝟭 C`, there exist actual localized
   endofunctors T',S'. Both are additive and A-linear. Both object maps and both pure-tensor
   maps are explicitly specified, including the formula induced by S without assuming S
   linear as an additional hypothesis. The two strict inverse equations for T',S' make
   them automorphisms, and `T ⋙ Q = Q ⋙ T'` is the node's commuting-square equation in
   Lean's order of functor composition. Thus this concerns strict automorphisms, not merely
   equivalences of categories, in agreement with proof step 5.

The `HEq` equations are only heterogeneous because functor objects are propositionally
identified with their specified object maps. Together with those object equalities they
are exactly the usual equations after transport along object equality; they impose the full
morphism formulas, not merely equality of isomorphism classes.

The instance-binding lambdas are applied with named arguments to the existential structures.
They are transparent lambda applications, not `let`, `have`, `show ... from`, new definitions,
or extra assumptions. All variables and universes are explicitly bound.

Dependency declarations read and used:

- `def-weil-ring-localization-away`: `Localization.Away`,
  `Mathlib.GroupTheory.MonoidLocalization.Away`, with ring/algebra instances supplied by
  `Mathlib.RingTheory.Localization.Away.Basic`. The abbreviation is localization at powers.
- `def-weil-linear-category`: `CategoryTheory.Linear`,
  `Mathlib.CategoryTheory.Linear.Basic`, together with `Preadditive` and `Category`.
- `def-weil-module-base-change`: `TensorProduct`, scalar-first tensor module structure,
  `LinearMap.baseChange`, and `TensorProduct.AlgebraTensorModule.distribBaseChange`,
  as recorded in `Mathlib.LinearAlgebra.TensorProduct.Tower`. Read the signatures and
  docstrings of `baseChange`, `distribBaseChange` and their pure-tensor formulas.
  The theorem uses the existing tensor module and curried linear maps, not a replacement
  notion of base change. `baseChange` and `distribBaseChange` are the proof-plan inputs.
- `def-weil-linear-functor`: `CategoryTheory.Functor.Linear`,
  `Mathlib.CategoryTheory.Linear.LinearFunctor`, and `Functor.Additive` from
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`. Their full signatures/docstrings
  were read: additivity plus scalar preservation gives linearity of the Hom map.

All statement/proof dependencies are Mathlib declarations; their modules are public imports.
No project dependency is missing, no new nodes or dependency modules are needed, and no
statement correction or dispute is present.

Edge cases checked mathematically: C may be empty; the universal clauses and functor
construction then remain valid. The zero ring, p=0, and nilpotent p are included: A can be the
zero ring and all tensor Hom modules then vanish, with the unique identity on each object.
This still defines a category (distinct objects can be uniquely isomorphic). For p a unit,
this is ordinary scalar extension along an isomorphism. Identity automorphisms and arbitrary
strict inverses are included. Object, Hom, and coefficient universes are independent; the
localized Hom universe is their required maximum `max r v`, and no universe lift adds objects.

Searches for an existing declaration (all run for this item using msearch.py):

- LeanFinder: `Extension of scalars of a linear category tensor product morphism modules
  composition`: eight hits on ModuleCat extension of scalars and its monoidal structure,
  including `ModuleCat.ExtendScalars.map_tmul`, `ModuleCat.extendScalarsComp_hom_app_one_tmul`,
  `ModuleCat.instMonoidalLinear`, and tensor-whiskering formulas. These construct functors
  between module categories, not the tensor-Hom category with unchanged objects.
- Loogle: `CategoryTheory.Linear, TensorProduct`: zero hits.
- Mathlib grep: `baseChange|extendScalars|scalarExtension` in `CategoryTheory/Linear`:
  zero hits.
- LeanSearch: `Base change of a linear category by tensoring morphism modules with a
  commutative algebra`: service unavailable (Internal Server Error), recorded as unavailable.
- Source/project rg: `scalarExtension|ScalarExtension|scalarLocalization|ScalarLocalization|
  lem-weil-linear-scalar-localization-category` in WeilConjectures and lean/Sheaf, followed by
  the narrower `Linear.*Localization|tensor.Hom|tensor-Hom|scalar localization|
  ScalarLocalization`. Hits concern module/complex scalar extension, tensor-Hom adjunctions,
  and existing sheaf coefficient extension; none states this raw tensor-Hom construction.
  The exact item-id search in upstream sources found no declaration. The chosen theorem name
  was also checked against the upstream name index, Mathlib, upstream source, and lean/Sheaf;
  no collision was found.

Validation: the module compiled cleanly through scompile.py on the server (nice 19, two
threads, 60-second per-file limit), with no warnings. No local Lean compiler or library build
was run. The required delivery dry run is run after preparing this report; its outcome is
reported in the worker's final readiness answer. No delivery is pushed by this worker.


## Second reading by NG

I independently read the item node, the complete proposed Lean module, all four
statement/proof dependency nodes and their recorded Mathlib declarations, and the source
`def-weil-rationalization-karoubi.md`. I also read the Stacks tensor-product universal
property and its quotient construction (algebra.tex, 00CV/00CX), base change (05G4),
and the linear-category and linear-functor definitions (dga.tex, 09MJ/09MK).
The blueprint specializes to a valuation ring and its fraction field and a triangulated
category; this node deliberately isolates the elementary category construction over an
arbitrary commutative ring. Nothing in that construction requires a field, triangulation,
nonzerodivisor, or finite generation. The source explicitly excludes Karoubi completion.

Object/hypothesis/conclusion checklist, written from the node and then matched to Lean:

1. A commutative ring R and an element varpi, with A = R[1/varpi]. Rendered by
   `(R : Type r) [CommRing R]` and `(p : R)`, with `Localization.Away p` throughout.
   PASS: `Localization.Away` is the quotient localization at `Submonoid.powers p`;
   `Away.Basic` supplies the ring/algebra structures. No extra ring hypothesis.
2. An R-linear category C, without an additive-category assumption. Rendered by
   `(C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]`.
   PASS: `Linear.homModule`, `smul_comp`, `comp_smul`, and Preadditive give exactly
   module-valued Homs and bilinear composition; finite biproducts are not required.
3. For each K,L, H(K,L) is Hom(K,L) tensor_R A. Rendered by
   `Localization.Away p ⊗[R] (K ⟶ L)`.
   PASS: the reversed order is precisely the recorded module-base-change convention;
   tensor symmetry takes the right-factor action in the node to the left-factor action
   here. Read `LinearMap.baseChange`, its pure-tensor equation, and
   `AlgebraTensorModule.distribBaseChange` and its inverse pure-tensor equation.
4. Clause (1): for every K,L,M a unique A-bilinear composition with the stated formula.
   Rendered by `∀ K L M : C, ∃! β : ... →ₗ[A] ... →ₗ[A] ..., ...` and
   `β (a ⊗ₜ[R] f) (b ⊗ₜ[R] g) = (a * b) ⊗ₜ[R] (g ≫ f)`.
   PASS: the curried linear map is bilinear, uniqueness ranges over all such maps,
   and diagrammatic `g ≫ f` is exactly f composed with g. No quantifier is lost.
5. Clause (2): same objects, these full Hom modules, associativity and identities,
   and A-linearity. Rendered by existential `d : Category.{max r v} (ULift.{0} C)`,
   `a : Preadditive ...`, `l : Linear A ...`, and the A-linear equivalences `e K L`.
   The identity equation is `e K K (1 ⊗ₜ[R] 𝟙 K) = 𝟙 (ULift.up K)` and the next
   equation gives composition on all pure tensors.
   PASS: Category contains all three laws; Preadditive and Linear make composition
   bilinear, so equality on pure tensors extends to all morphisms. Consequently its
   transported composition is the unique map of (1). The e are bijections of full
   modules, not just maps into a larger Hom. ULift.up/down are inverse object bijections;
   transporting back gives exactly the original object type. No summands are adjoined.
6. Clause (3): Q is identity on objects and sends f to f tensor 1; it is an R-linear
   functor for restriction of scalars. Rendered by `lr : Linear R ...`, the equation
   `r • f = (algebraMap R A r) • f`, and the existential functor Q with its object
   equation, `HEq (Q.map f) (e K L (1 ⊗ₜ[R] f))`, `Q.Additive`, and `Q.Linear R`.
   PASS: the restriction action is constrained, not freely chosen. The functor supplies
   preservation of composition and identities. Additive plus Functor.Linear matches
   the dependency's module-homomorphism definition. Object equations justify the
   dependent transports in HEq; these are actual morphism equalities.
7. Clause (4): for every R-linear strict automorphism T, localize its Hom maps,
   obtain the A-linear automorphism T' with inverse induced by T inverse, and
   Q composed with T equals T' composed with Q. Rendered by universal T,S with
   `[T.Additive] [T.Linear R]`, both strict inverse equalities, and existential T',S'.
   Their object and pure-tensor map equations are specified separately, both have
   Additive/Linear A properties, both strict inverse equalities hold, and the final
   equation is `T ⋙ Q = Q ⋙ T'`.
   PASS: a supplied strict inverse is exactly the node's meaning (explicit in proof
   step 5). Its R-linearity is a consequence, not an additional hypothesis. Both
   inverse directions and the commuting square are present with the correct order.

Edge cases: empty C makes object-indexed requirements vacuous but still allows the
empty localized category and functors. For the zero ring, p=0 or nilpotent p, A is allowed
to be the zero ring: every tensor Hom is zero, and its unique element serves as identity;
there is no contradiction even for multiple objects. Zero objects or zero original Homs
are permitted without assumptions. For a unit p this recovers ordinary scalar extension
along an isomorphism. No characteristic is restricted. There is no index family, scheme,
or n parameter to exclude an empty set, empty scheme, or n=0. The independent universes
r,u,v cover large categories, with tensor Homs in `max r v` and unchanged object universe u.
All binders were checked: no free variable or unbound universe occurs.

Independent duplicate searches (queries differ from the first reader's):

- LeanFinder via msearch.py: `Change coefficients in a preadditive category by tensoring
  each morphism module`. Eight hits, including ModuleCat.instMonoidalPreadditive and
  tensorLeft/tensorRight linearity; these concern tensoring objects in an existing
  monoidal category, not constructing the category with tensor-extended Hom modules.
- Loogle via msearch.py: `TensorProduct, CategoryTheory.Functor`. Five hits, including
  ModuleCat.extendScalarsComp_hom_app_one_tmul and representation tensor identities;
  none states this construction.
- LeanSearch via msearch.py: `Localize a linear category at a scalar by tensoring its
  morphism groups`. Service unavailable (Internal Server Error), recorded as unavailable.
- Independent rg searches of upstream WeilConjectures, project lean/Sheaf and Mathlib
  CategoryTheory used ChangeOfRings/changeOfRings, enriched base change, scalar
  localization, tensor Hom, and then change.of.rings/change.of.scalars/
  extension.of.scalars/scalar.localization/raw.scalar/tensor.hom in the category-theory
  directories. Hits were module/presheaf change of rings, monoidal tensor-Hom, and derived
  module results, not this raw category. The upstream name index, Mathlib, upstream Lean,
  and project Lean have no `exists_linear_scalarLocalization_category` collision.

No new nodes or dependency modules are present or needed; all dependencies are usable
Mathlib leaves. No statement correction is present or needed, so no citer correction
verdicts apply. There are no definitions, hollow data, proved theorems, private aliases,
file-local notation, or local instances in this delivery. The one theorem has `sorry`.
The module and theorem docstrings contain the source and exact blueprint id; the proof
plan carries all five node steps. Imports cover the statement and proof dependencies.
All lines are at most 100 characters. The node's `lean.statement` was mechanically checked
verbatim equal to the complete theorem signature before `:= by`.

Mismatches found: none. Changes: appended this independent second-reading report only;
the correct Lean module and node record were preserved. Remote scompile.py validation
passed cleanly: 1.2 seconds, nice 19, two threads, 60-second per-file limit, no warnings.
