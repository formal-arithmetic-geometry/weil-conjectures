## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CondensedRing.coefficientProjectionSquare`
in `Sheaf.Paper.CoefficientProjectionSquare`. Its proof is `sorry`, with the five
steps of the DAG proof retained in its docstring. There is no statement correction.
The additional definition module supplies the previously absent canonical internal
scalar tensor interface; it does not replace the existing scalar functor or comparisons.

Hypotheses and objects, matched against the node:

- The standing prime is `(ℓ : ℕ) [Fact ℓ.Prime]`. The field is `(k : Type u)
  [Field k]`; `[Fact (ringChar k).Prime]` says positive characteristic, and
  `[Fact (ringChar k ≠ ℓ)]` gives the required unequal characteristics.
- `X Y : Over (Spec (.of k))` and `f : X ⟶ Y` give two schemes over the same
  field and a morphism over that field. For both structure maps,
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` are precisely separated
  finite type. The operations use the underlying scheme morphism `f.left`.
- `R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, with `MonObj` and
  `IsCommMonObj`, are the commutative condensed rings. `(a : R ⟶ S) [IsMonHom a]`
  is their ring morphism. `coefficientMap a Z` is the recorded pulled-back map.
- `[∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]`
  is exact scalar extension on every scheme: finite colimits are already preserved
  by its recorded left adjunction. This is the same hypothesis used by the recorded
  definitions of `derivedPullIso` and `derivedPushHom`.
- `K` and `M` range over the full ordinary unbounded `DerivedCategory (Mod ...)`
  on `X.left` and `Y.left`, respectively. No boundedness or constructibility predicate
  occurs. `internalScalarExtension a Z` is definitionally the existing
  `(Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctor`, namely `T_Z`.
- `moduleObjectDerivedPullback R f.left` and
  `moduleObjectDerivedPushforward R f.left` are the recorded `P_R` and `G_R`;
  the same declarations with `S` give `P_S` and `G_S`.
- `derivedPullIso a f.left` is exactly the specified `c_f`; its `.hom.app M`
  has the direction `T_X(P_R M) ⟶ P_S(T_Y M)`.
  `derivedPushHom a f.left` is exactly the specified `gamma_f`, used at `K`
  and at `K ⊗ (moduleObjectDerivedPullback R f.left).obj M`, the stated `H`.
- `((internalScalarTensorComparison a Z).app A).app B` is `mu_Z`, in the required direction.
  Its companion `internalScalarTensorIso` exposes invertibility. Both are the
  existing universal bifunctor-derived lift of the uniquely normalized ordinary
  tensorator; the construction and normalization are described below.
- `moduleObjectProjectionMap R f.left K M` and its `S` specialization are precisely
  the recorded projection mates, without choices or additional hypotheses.

Every clause of the equality is represented, with Lean's `≫` read left to right:

1. The left side starts with `((internalScalarTensorComparison a Y.left).app (G_R.obj K)).app M`,
   then `((derivedTensor S Y.left).map gamma_K).app (T_Y.obj M)`,
   the first-factor tensor map `gamma_K ⊗ 1`, then
   `moduleObjectProjectionMap S f.left (T_X.obj K) (T_Y.obj M)`.
   This is the node's rightmost-first `pi_S (gamma_K tensor 1) mu_Y`.
2. The right side starts with `T_Y.map (moduleObjectProjectionMap R f.left K M)`,
   then `gamma_H`, then `G_S.map (mu_X ≫ ((derivedTensor S X.left).obj (T_X.obj K)).map c_M)`.
   This is exactly `G_S((1 tensor c_M) mu_X) gamma_H T_Y(pi_R)`.
3. Consequently both sources are `T_Y(G_R K ⊗ M)` and both targets are
   `G_S(T_X K ⊗ P_S(T_Y M))`. There is no equation only after forgetting scalars,
   taking cohomology, or applying an unspecified transport.
4. No properness assumption, `IsIso` assumption on gamma or projection, perfectness,
   boundedness, or constructibility assumption has been introduced.

Recorded dependency declarations used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `compactificationOverField` and the documented explicit standing-setting binders.
  The ambient categories, rather than its constructible subcategories, are used.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `AlgebraicGeometry.ProEtale.coefficientMap`, `CondensedRing.derivedPullIso`,
  `CondensedRing.derivedPushHom`, with their recorded adjunction definitions.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `moduleObjectDerivedPushforward`, `moduleObjectDerivedPullback`, definitionally
  the existing total derived functors of the complete underived composites.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` and its public
  Tensor import: `CondensedRing.derivedTensor` and the actual derived monoidal
  structure; `⊗` and `⊗ₘ` use that relative module-object tensor.
- `Sheaf.Paper.ModuleObjectProjectionMap`: `moduleObjectProjectionMap`.
- New node `def-sfb-internal-scalar-tensor-comparison`, module
  `Sheaf.Paper.InternalScalarTensorComparison`: `internalScalarTensorComparison`,
  `internalScalarExtension` and its uniquely normalized ordinary monoidal structure.

Stated proof dependencies are imported non-publicly:
`Sheaf.Paper.ModuleRingedToposDerivedComparison`,
`Sheaf.Paper.RingedComparisonTensorAdjunction`, and
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
The recorded ChangeOfCoefficients proof ingredients are already publicly imported
as statement dependencies. The Mathlib conjugate, mate, and composite-adjunction
matches are in the imports of these modules. The genuine proof prerequisite
`lem-sfb-internal-section-scalar-adjunction` has no recorded declaration; it is
not needed to type this statement and is not silently replaced or used as a hypothesis.

Edge cases checked before drafting: the empty scheme; zero complexes; identity
geometric morphism; identity scalar change; exact coefficient changes which are
not ring isomorphisms (e.g. localization); the zero coefficient ring; unbounded
objects. All remain in scope. In particular the new normalization uses morphisms
out of the actual tensor coprojection, not pointwise elements or an assumption
that the topos has enough points. Its ordinary construction and flat-preservation
property do not assume exact scalar extension. That hypothesis is retained for
the given derived comparisons and the exact-functor derived tensor API.

Searches run for the item:

- `msearch.py leanfinder`, query “The projection formula mate commutes with exact
  extension of coefficients via the canonical scalar tensor comparison”: eight
  ordinary ModuleCat extension/restriction and composition hits, no such square.
- `msearch.py loogle`, `CategoryTheory.Adjunction, CategoryTheory.MonoidalCategory`:
  twelve generic monoidal adjunction hits, no specified module-object equality.
- `msearch.py grep`, `projectionFormula|projection.*[Mm]ate|[Mm]ate.*tensor`, in
  `CategoryTheory`: zero Mathlib hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id, coefficient
  projection names, scalar tensor names and extension monoidality: no existing
  declaration of the item. Ordinary scalar tensor comparison is discussed below.

Validation uses only the prescribed `scompile.py` and `deliver2.py` wrappers.
Early compiler feedback exposed a class-reducibility warning, repaired with
`@[instance_reducible]`, and expensive repeated expansion of generic derived
functor arguments. The new `internalScalarExtension` shares the scalar functor arguments, and the
recorded `derivedTensor` bifunctor expresses the two one-factor tensor maps directly.
The final `scompile.py` run succeeded with no errors or warnings: the helper's
library compile took 38.5 seconds and the square's took 19.3 seconds, below the
unchanged 60-second limit. No standalone compiler, global build, or local
preflight script was run. The first prescribed dry run compiled both modules but its text parser included a
trailing line comment in the preceding theorem proof. Replacing that comment by
a block comment leaves the Lean declarations unchanged and repairs the packaging
check. The repeated `deliver2.py --no-push` completed successfully:
`OK (dry run): commit cf06a75be55 passes the preflight and compiles; nothing pushed`.
The final delivery uses the same declarations and node records.

## New nodes

`def-sfb-internal-scalar-tensor-comparison` defines the canonical internal scalar
monoidal structure and its derived tensor comparison in its own module. Source:
Stacks 07A4, `lemma-pullback-tensor-product` (the displayed total-complex construction),
for the identity underlying topos with coefficient ring map, and the current
blueprint rational proper-base-change proof (3). Its statement records the
scalar-unit universal property, the resulting unique strong monoidal structure,
flat preservation, and the derived bifunctor lift with its representative formula.
Its `stmt_deps` cite the recorded coefficient changes, scalar adjunction, and
relative derived tensors. The item gains exactly this dependency.

The normalization is `InternalScalarMonoidalNormalized a X m`: after
`Mod.tensorObjπ M N`, the unit on the tensor followed by `m`'s comonoidal map is
the tensor of the two scalar units followed by the target coprojection.
This is a fully specified equality in the abelian sheaf category, with fixed
scalar-adjunction units. `internalScalarMonoidalNormalized_existsUnique` states
existence AND uniqueness of the entire strong monoidal structure with this
property, including its unit. The definition `internalScalarMonoidal` selects
that uniquely determined structure. This is the permitted deferred universal
property, not data selected from a mere existence or `Nonempty` proposition.
The theorem's docstring supplies the balanced-map construction, inverse,
coherence, and uniqueness argument. `internalScalar_preservesFlat` is the other
postponed named theorem, with the scalar tensor cancellation argument in its
docstring; its property is explicitly part of this definition node's statement.
`internalScalarExtension` has the actual existing functor as its body.
`internalScalarTensorComparison` and `internalScalarTensorIso` are natural transformations
and natural isomorphisms of the canonical derived tensor bifunctors: the canonical
existing `leftDerivedTensorComparison`, packaged by `asIso` and then exposed
by `.hom`, after installing the uniquely normalized ordinary monoidal structure.
Their public types use the recorded `derivedTensor` bifunctors so that consumers
share the same structural arguments. Their definitions contain no
`sorry`. No canonical arrow is replaced by an arbitrary morphism.

Searches run for this notion (also retained in the node's `mathlib_searches`):

- `msearch.py leansearch`, query “Extension of scalars of internal module objects
  has a unique strong monoidal structure taking the scalar adjunction unit of a
  tensor to the tensor of units”: eight hits for generic monoidal adjunction units
  and ordinary ModuleCat/ModObj facts, no internal scalar monoidal interface.
- `msearch.py leanfinder`, query “Extension of scalars of internal module objects
  is strong monoidal with tensor comparison preserving the adjunction unit”:
  eight ordinary ModuleCat unit and composition hits, no internal tensorator.
- `msearch.py grep`, `extendScalars.*Monoidal|monoidal_extendScalars|extendScalarsTensor`:
  Mathlib has one hit, the ordinary `ModuleCat` instance, not internal modules.
- Project `rg` finds `Mod.monoidal_extendScalars` in `MapModMonoidal.lean:623`;
  its full signature at 615–623 requires `[IsIso φ]`. This cannot render the
  present arbitrary exact coefficient map. The geometric module pullback API
  likewise specializes to its invertible structural coefficient map.
- DAG searches locate `lem-sfb-scalar-ordinary-tensor-comparison` and
  `lem-sfb-scalar-tensor-comparison`. Their signatures use section-ring sheaf
  `ScalarHomTensor` models, not `Mod` of abelian sheaves. They do not expose the
  required internal comparison. The internal/section scalar transport is a
  separate genuine as-yet-unstated proof node, so using those declarations
  directly would require a new transport interface anyway. This module supplies
  the internal interface by its own balanced universal property, using the
  existing internal scalar extension and relative tensor, without reimplementing
  either notion or the ring-sheaf comparison.
- `tools/blueprint_refs.py search 'scalar tensor'` finds only
  `cor-pur-vector-bundle-purity`, not this definition. `ancestor` gives
  `det-thm-sfb-proper-base-change-rational`; the new node records paragraph (3)
  and the prescribed via list. Source/DAG searches find no declaration or node
  for this uniquely normalized internal structure.

## Second reading by Q07

A second pass by this worker checked the node and both files together; no separate
agent was started, as the dispatcher's brief explicitly prohibits doing so. The
maintainer supplies the independent review. The pass checked every binder and
all five arrows, their directions, coefficients, and category endpoints as listed
above. It also checked that the scalar-unit equation uses the same coefficient
adjunction units and actual balanced tensor coprojections. The tensor morphisms are rendered by the recorded `derivedTensor` bifunctor maps
for elaboration efficiency; the scalar comparison remains the canonical natural
transformation. Neither the equality nor its hypotheses changed.
No mathematical mismatch or disputed statement was found. All universes and
variables are explicitly bound, no file-local notation or private definitions
appear, and each delivered module belongs to exactly one node.
