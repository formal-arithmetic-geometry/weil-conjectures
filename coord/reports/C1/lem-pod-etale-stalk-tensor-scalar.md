## Worker report

The delivery states `lem-pod-etale-stalk-tensor-scalar` in
`Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`, namespace
`AlgebraicGeometry.Scheme`. Its seven named theorems all have `sorry` proofs.
No data definition, private copy of a dependency, axiom, or proof is introduced.
The node's statement and dependencies are unchanged.

Sources read: [Stacks 007K](https://stacks.math.columbia.edu/tag/007K),
[008B](https://stacks.math.columbia.edu/tag/008B),
[03EL](https://stacks.math.columbia.edu/tag/03EL), and
[04FM](https://stacks.math.columbia.edu/tag/04FM). The local literature checkout
contains the citation lists but not the Stacks source tree, so these source
places were opened on the Stacks website. The node's five proof steps were
read in full; the relevant steps and dependency IDs appear in each theorem's
docstring. 007K/008B give the stalk comparison; 03EL gives the tensor/pullback
comparison by adjunction; 04FM identifies the pointed-neighborhood colimit
with the point fiber. The extension-of-scalars adjunction is the balanced-map
universal property of the tensor product, also the alternative explicitly
allowed in proof step 4 of the node.

Hypotheses and objects, individually:

- The arbitrary scheme is `{Y : Scheme.{u}}`; there is no quasi-compactness,
  finite-type, Noetherian, connectedness, or nonemptiness hypothesis.
- The geometric point is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `y : Spec (.of Ω) ⟶ Y`. This is an algebraically closed field, not an
  arbitrary rational point. Mathlib's `pointSmallEtale` accepts the implied
  separable closedness. Its fiber objects are lifts of this morphism to an
  étale neighborhood, as inspected in `EtalePoint.lean`.
- The small étale site is exactly `Y.smallEtaleTopology` on `Y.Etale`.
- All stalks use `(pointSmallEtale y).ulift.{u + 1}.sheafFiber`. The lift only
  changes the universe of the fiber sets, not the stalk; the existing
  `Point.uliftSheafFiberIso` identifies it with the recorded dependency's
  `Point.sheafFiber`. A pointed neighborhood is `U : Y.Etale` together with
  `x : p.fiber.obj U`; its germ map is `p.toPresheafFiber U x F.obj`.
- A sheaf of left modules is `Sheaf Y.smallEtaleTopology (ModuleCat R)`.
  Its section groups are modules, and its restriction morphisms are linear
  by the category of values; the sheaf condition is the usual module-valued
  sheaf condition. No separate notion of a module sheaf is copied.
- The coefficient and module universe is `u + 1`, with rings of that same
  universe, as required by Mathlib's module monoidal unit. The declarations
  are polymorphic in `u`; there is no fixed small universe, finite-cardinality
  or finite-dimensional restriction. Schemes, fields, rings and modules in
  differing universes can be placed in this common universe by the standard
  universe lifts. This follows the source project's étale-sheaf convention.

Clause 1, hypothesis by hypothesis and conclusion by conclusion:

- Commutativity is `[CommRing R]`; `F G : Sheaf ... (ModuleCat R)` are
  arbitrary module sheaves.
- `F ⊗ G` is the existing sheaf monoidal tensor, obtained by localization
  from the objectwise presheaf tensor and sheafification. It is canonically
  the sheafification of `F.obj ⊗ G.obj`. In Mathlib the localized tensor
  object is not definitionally that chosen sheafification, so the canonical
  section map is `Functor.LaxMonoidal.μ (sheafToPresheaf J A) F G`, using
  `sheafificationAdjunction.rightAdjointLaxMonoidal`. This is precisely the
  map sending the tensor of sections to its sheafified section, under that
  canonical identification, rather than an ill-typed direct composition
  with `toSheafify`. Its source at U is the sectionwise module tensor.
- `etale_stalk_tensor_unique` defines a local predicate `P` on linear
  morphisms `T.obj F ⊗ T.obj G ⟶ T.obj (F ⊗ G)`. For every pointed U its
  equation is `(germ_F ⊗ germ_G) ≫ f = sectionTensor ≫ germ_tensor`.
  Equality of these linear morphisms is exactly the pure-germ formula.
  The conclusion `(∃! f, P f)` asserts uniqueness among ALL linear maps
  with the germ formula, without assuming invertibility of a competitor.
  `P (Functor.LaxMonoidal.μ T F G)` and `IsIso ...` identify that unique
  map with the canonical tensorator and assert it is an isomorphism.
- `etale_stalk_tensor_natural` quantifies arbitrary sheaf morphisms
  `f : F ⟶ F'` and `g : G ⟶ G'` and states the naturality square in both
  variables for that same tensorator.
- `etale_stalk_tensor_coherence` states, as separate conjuncts, the unit
  sheaf identification with `(constantSheaf J A).obj (ModuleCat.of R R)`,
  the associativity diagram using `α_`, the commutativity diagram using
  `β_`, and both the left and right unit diagrams using `λ_` and `ρ_`.
  `Functor.LaxMonoidal.ε T` is the canonical identification of the module
  unit with its constant-sheaf stalk. All the diagrams concern the map
  identified in the uniqueness theorem, not an unrelated chosen isomorphism.

Clause 2, hypothesis by hypothesis and conclusion by conclusion:

- Rings are `[Ring R] [Ring S]`, not `CommRing`; `f : R →+* S` is an
  arbitrary unital ring homomorphism. The iterated statement similarly
  uses `[Ring V]` and `g : S →+* V`.
- Mathlib's `ModuleCat.extendScalars` is NOT used: its signature explicitly
  requires commutativity. The tensor object for general rings is rendered
  by its defining universal property, `E ⊣ ModuleCat.restrictScalars f`.
  For every M, the adjunction says that S-linear maps from E(M) to N are
  R-linear maps from M to N with scalars restricted through f. This is
  exactly the universal property of S ⊗_R M, with pure tensor `a ⊗ m`
  represented by `a • adj.unit.app M m`. In particular the unit is
  `m ↦ 1 ⊗ m`. This uses Mathlib's existing `Adjunction`, not a new
  predicate or a commutative special case. Quantifying E and its adjunction
  allows any representative of that tensor object. The named theorem
  `etale_scalar_extension_exists` supplies existence for every f, so the
  statement does not assume the missing construction exists as an extra
  mathematical hypothesis, nor define unknown data with `sorry`.
- The scalar-extended sheaf is explicitly
  `(presheafToSheaf J B).obj (F.obj ⋙ E)`. Thus the underlying presheaf
  has exactly the module scalar extensions on sections, and sheafification
  is the recorded dependency's adjunction.
- `etale_stalk_scalar_component_unique` is the individual-map statement.
  Its local P is the germ equation at the adjunction unit, hence at
  `1 ⊗ s`; S-linearity gives the equation at every `a ⊗ s`.
  `(∃! c, P c)` ranges over all S-linear maps without requiring an
  arbitrary competitor to be invertible. It also asserts the canonical
  comparison `c₀` satisfies P and is an isomorphism. That comparison is
  the inverse of `presheafFiberCompIso E`, followed by the inverse of
  `presheafToSheafCompSheafFiberIso B`.
- `etale_stalk_scalar_unique` states existence and uniqueness of the
  natural transformation between the functors `stalk ⋙ E` and
  `underlyingPresheaf ⋙ postcompose E ⋙ sheafify ⋙ stalk`, with the same
  germ equation, and states that every component satisfying it is an iso.
  This includes the requested naturality in F.
- `etale_stalk_scalar_iteration` uses three extension adjunctions, for f,
  g, and g.comp f. Its `a` is the canonical associativity identification
  of the extension functors, given by composition of adjunctions,
  `restrictScalarsComp`, and `leftAdjointUniq`. It asserts existence of a
  sheaf isomorphism b from the successive extension to the direct one,
  specifies it by the sectionwise associativity and the two sheafification
  unit maps, and states the stalk diagram
  `E₂₃.map c₁₂ ≫ c₂₃ ≫ stalk.map b.hom = a.hom.app (stalk F) ≫ c₁₃`.
  Each c is exactly the canonical comparison also present in the
  individual-map theorem. The section equation says what the sheaf
  identification is, so no arbitrary identification is assumed.

Dependency declarations used and signatures read:

- `def-weil-pbc-scheme-conventions` fixes no own declaration. Its convention
  record is respected by using `AlgebraicGeometry.Scheme` and the field-
  valued `Spec` morphism of `Scheme.pointSmallEtale`.
- `def-weil-pbc-etale-site`: `AlgebraicGeometry.Scheme.smallEtaleTopology`,
  `Mathlib.AlgebraicGeometry.Sites.Etale`, signature `(X : Scheme.{u}) :
  GrothendieckTopology X.Etale`; the covering-family criterion and `Etale`
  category declarations were also read.
- `def-weil-pbc-geometric-stalks`: `Point.sheafFiber`,
  `Mathlib.CategoryTheory.Sites.Point.Basic`, which is
  `sheafToPresheaf J A ⋙ Φ.presheafFiber`; `presheafFiber` is the colimit
  over the opposite category of elements. `Scheme.pointSmallEtale` in
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint` identifies those elements
  with the dependency's pointed étale neighborhoods. The existing
  universe-lift is in `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic`.
- `def-weil-pbc-sheafification`: `presheafToSheaf` and
  `sheafificationAdjunction`, `Mathlib.CategoryTheory.Sites.Sheafification`.
  Their full signatures and docstrings were read; these are the reflector
  and its adjunction to `sheafToPresheaf`.
- `def-weil-pbc-constant-sheaf`: `constantSheaf`,
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`, defined as
  `Functor.const Cᵒᵖ ⋙ presheafToSheaf J D`. It appears explicitly in the
  coherence theorem's unit-sheaf conjunct.
- The source project's `WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal`
  provides the compatible monoidal fiber instance. Its existing tensor
  isomorphism and naturality declarations were inspected but do not state
  this entire node, especially its noncommutative scalar clause and
  pure-section uniqueness. The module is imported to use that established
  structure; no new structure is defined.

Edge cases checked: zero modules and the zero ring remain allowed (`Ring`,
not `Nontrivial`); an identity ring map is allowed; a noncommutative matrix
ring and a noncentral ring homomorphism are allowed because only restriction
of scalars and its left adjoint are used, with the right R-action on S implicit
in that universal property. No flatness hypothesis is present or needed.
Empty schemes have no geometric point, as they should; nothing arbitrarily
excludes them. The statements do not impose a directed-set neighborhood
index; point fibers use the filtered category of pointed neighborhoods.
No finite index set, rank, dimension, or field characteristic is fixed.

Searches actually run:

- msearch LeanFinder: `stalk of tensor product and scalar extension sheaves
  modules etale site`. Eight hits, concerning affine tilde stalks and
  Kähler differential base change; no exact statement.
- msearch Loogle: `CategoryTheory.GrothendieckTopology.Point.sheafFiber`.
  Twelve hits, including `sheafFiberCompIso` and fiber comparisons; their
  signatures were read and reused. They do not state the full node.
- msearch LeanSearch: `stalk tensor product sheaf modules scalar extension`.
  Service unavailable, Internal Server Error; not recorded as no match.
- msearch grep on CategoryTheory: `stalk.*tensor|tensor.*stalk|sheafFiber|extendScalars`.
  Hits include `Sites/Point/Monoidal.lean`; the full file was read and its
  monoidal structure used.
- rg of the source project for `stalk.*tensor|tensor.*stalk` found the
  StalkMonoidal module, which was read in full. rg of the source project
  for the item ID returned no occurrence. rg of `lean/Sheaf` found unrelated
  affine tensor-fiber statements, no matching geometric-stalk theorem.
- rg for tensor/scalar declarations in Mathlib's ModuleCat presheaf and
  change-of-rings files found the commutative `extendScalars` API, whose
  full signature and docstring show why it cannot render clause 2.
- rg for each introduced theorem name in Mathlib, the source project,
  `dag/lean_names_upstream.json`, and `lean/Sheaf` found no duplicate.

Server validation: the complete file compiled cleanly, with no errors or
warnings, in 7.7 seconds after the final clause additions. The delivery dry
run is the final check. No statement dispute, statement correction, new
node, or dependency replacement is required.

## Second reading by C1

I independently read the node, its Stacks source places, and the complete Lean
file. The node introduces a scheme Y, geometric point ybar, the small etale
site and the geometric stalk convention, then the following objects and
clauses.

* In clause (1), Lambda is commutative and F,G are arbitrary sheaves of
  Lambda-modules. The Lean binders are `[CommRing R]` and `F G : Sheaf
  Y.smallEtaleTopology (ModuleCat R)`. `etale_stalk_tensor_unique` states
  existence and uniqueness of the linear map with the germ formula, identifies
  the canonical lax-monoidal map as satisfying it, and states that map is an
  isomorphism. `etale_stalk_tensor_natural` renders naturality for arbitrary
  `f` and `g`; `etale_stalk_tensor_coherence` renders the unit, associativity,
  symmetry, and both unit diagrams. These are exactly the node's clauses, with
  the point-fiber germ maps made explicit.
* In clause (2), Lambda to Lambda' is an arbitrary unital ring map and F a
  left-module sheaf. The Lean uses `[Ring R] [Ring S]` and `f : R →+* S`;
  `etale_scalar_extension_exists` supplies a left adjoint to restriction of
  scalars, which is the stated tensor universal property. `etale_stalk_scalar_unique`
  gives the natural transformation, its pure-germ equation, uniqueness, and
  componentwise isomorphism. The individual-map theorem gives the same equation
  and uniqueness for `c₀`, and proves `c₀` an isomorphism.
  `etale_stalk_scalar_iteration` introduces the second map and three adjunctions,
  then states the sheaf associativity equation and stalk compatibility.
  Quantifier order and all requested naturality and coherence clauses agree
  with the node.
* The ambient binders use `Y : Scheme.{u}`, `Omega : Type u`, `[Field Omega]`
  and `[IsAlgClosed Omega]`, with `y : Spec (.of Omega) ⟶ Y`; no extra
  finiteness, separatedness, characteristic, nonzero, or nonemptiness
  hypotheses occur. Coefficient objects consistently use universe `u + 1`,
  matching the module category and the node's unrestricted universe convention.

Edge cases checked: zero rings and zero modules are permitted; identity and
noncommutative ring maps are permitted; n = 0 and empty index sets do not occur
in this statement; an empty scheme has no geometric point and is not
artificially excluded; no finite generation, flatness, or characteristic
assumption is present. The stalk index is the filtered category of pointed
etale neighbourhoods rather than a directed set.

Searches were repeated with LeanFinder/Loogle/msearch for stalk-tensor and
scalar-extension declarations, `rg` over Mathlib, `WeilConjectures`, and
`lean/Sheaf`, and duplicate-name searches for every declaration in the file.
Only the existing point, sheafification, and monoidal infrastructure was found;
no declaration states this node. The source pages for Tags 007K, 008B, 03EL,
and 04FM were read directly. No mismatch was found, so no file, node field, or
dependency record was changed. The module compiles cleanly with only its seven
intended `sorry` proofs.
