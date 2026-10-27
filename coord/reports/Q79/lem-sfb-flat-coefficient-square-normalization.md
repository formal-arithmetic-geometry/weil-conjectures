## Worker report

The module `Sheaf.Paper.FlatCoefficientSquareNormalization` states the flat coefficient
square on the ordinary unbounded derived categories of the actual internal module
objects. There is no completion or boundedness restriction. The statement and proof
of the DAG node are unchanged. The returned H2 ownership defect is repaired by three existing:true definition nodes
on the unchanged published modules, together with citations of the existing section
comparison, internal scalar, section operations, tensor and realization definition owners.
The two theorem nodes added by the returned packet are removed from stmt_deps.
The original proof_deps are retained, including lem-sfb-internal-scalar-mate-projection.
The rectangle theorem was not in the base proof_deps and is not needed: only its plain
pushforward alias is used, now owned by the new definition node.

Hypothesis and clause correspondence:

- The prime, field, positive characteristic and unequal characteristic hypotheses are
  `ℓ p`, `[Fact ℓ.Prime]`, `k`, `[Field k]`, `[CharP k p]`, `_hp`, `_hne`.
- The two schemes are objects of `Over (Spec k)`. The two triples of
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` instances express exactly
  separated finite type over k. `f : X ⟶ Y` is the given k-morphism.
- The commutative condensed rings are `R S : Sheaf (coherentTopology Profinite) Ab`
  with `MonObj` and `IsCommMonObj`; `a : R ⟶ S` with `IsMonHom a` is their ring map.
  This is the unbundled form of `Profinite.CondensedRing`, not a topological presentation.
- Exact extension on every scheme is the section variable
  `[∀ T, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a T))]`.
  Extension is already a left adjoint and preserves finite colimits. Restriction `V`
  is exact without additional hypotheses.
- The pulled-back rings and compatible coefficient identifications are exactly
  `condensedRingObj`, `coefficientMap`, `condensedPullbackHom` from the recorded
  upstream modules. `D`, `V`, `L`, `F`, `scalarAdj` and `adj` are the existing named
  interfaces for their specified unbounded derived functors and adjunctions.
- C and B are `B a Y.left` and `B a X.left`; their underlying ordinary modules are
  `B₀`. The first two conjuncts assert `exactFunctor ... (tensorRight (B₀ ...))`,
  precisely the dependency's flatness test. They use the same tensor that the fixed
  section equivalence identifies with `IsFlatOnSite`.
- The next two conjuncts state exactness of the ordinary R and S geometric pullbacks.
  Their total left derived pullbacks are `L` and their termwise identifications are
  the existing `leftDerivedUpperStarIsoMapDerivedCategory`.
- The given canonical e maps are `eX.derived` and `eY.derived`. Their parameters carry
  `TensorNormalized`, which is the universal computation-counit characterization,
  not an arbitrary isomorphism or a new mathematical assumption. Existence is the
  recorded internal scalar normalization theorem.
- `flatScalarCoefficientMap` is the actual `coefficientMap` made into a regular-module
  morphism, and `flatScalarDerivedCoefficientMap` puts it in degree zero. The two unit
  equations say precisely unit followed by e equals right-unitor inverse followed
  by tensoring identity with this coefficient map. Thus they render M tensor a_Z.
- `flatScalarTheta` unfolds to the inverse of the actual `derivedPullIso`.
  `flatScalarDirectImage` unfolds to actual `derivedComapLowerStarIso`. These helpers
  merely expose the already recorded opaque functor names, with explicit bodies.
- Equality `(flatScalarDirectImage ...).hom = scalarRestrictionPush ...` identifies
  actual d with the geometric mate of canonical b inverse. Here `scalarRestrictionPull`
  is exact localization of actual `derivedComapUpperStarIso` and is exactly b.
- The section witnesses `sX`, `sY` satisfy `SectionScalarNormalized` and
  `SectionTensorNormalized`, fixing their ordinary generators and K-flat computation
  maps. The two displayed derived-unit equations compare the specified internal
  scalar units with `sX.pair.adjunction.unit` and `sY.pair.adjunction.unit` through
  the SAME restriction and extension comparison maps.
- The section d witness is tied to actual d by the displayed conjugation equation
  through `scalarSectionPushComparison` and `sectionScalarRestriction`. Its
  `FlatSectionDirectImageNormalized` property requires the ordinary restriction /
  pushforward comparison to be identity on every section and the right-derived
  computation-unit square on every K-injective S-complex. This is the defining
  normalization of the ring-sheaf d of the recorded ring-sheaf change adjunction.
  Identity on sections determines its ordinary map uniquely; K-injective resolutions
  and the invertible computation maps determine its derived components uniquely.
  Consequently the existential is an equality with that canonical comparison in
  the section realization, rather than mere existence of some isomorphism between
  the endpoints. The localization presentation used by scalarDerivedRestriction is
  `mapHomologicalComplexUpToQuasiIso`, so its matching Factorsh comparison is used;
  no equality of unrelated chosen localization functors is silently assumed.
- `PullNormalized ... (flatScalarTheta ...)` and `SectionPullNormalized` pin actual
  theta to the already normalized ordinary balancing map and its K-flat section
  computation. This renders the concluding representative characterization.
- For every `M : DerivedCategory (Modules R Y.left)`, the final equation is literally
  L(eY inverse), b inverse, U(theta), eX, in Lean's left-to-right composition order.
  Its right side is `scalarTensorPull ...` followed by tensor identity with
  `scalarCoefficientPull ...`. The latter is the canonical restricted-regular rho.
  The former is the specified internal oplax tensor comparison, identified with
  the ringed tensor isomorphism mu by `ModuleRingedComparison.delta_comparison`.
  (That comparison module calls its inverse `internalMu`; the present node's mu
  is the forward tensor-pullback map.) SectionPullNormalized supplies the flat-term
  K-flat pure-tensor description, using the same alpha coefficient identification.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` and its underlying
  ring-object encoding.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField` documents the setting; only the setting
  binders occur here, with no unnecessary compactification in the assertion.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `condensedPullbackHom`,
  `coefficientPullbackIso`, `condensedPushforwardHom`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `coefficientMap`, both coefficient-square identities, `derivedComapLowerStarIso`,
  `derivedPullIso`, and `derivedComapUpperStarIso`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: both named module-object derived functors.
- `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`:
  `Mod.derivedExtendMapDerivedCategoryAdjunction` and exact restriction instances.
- `Sheaf.Paper.InternalScalarPullbackNormalization`: `SectionScalarComparison`,
  `SectionScalarNormalized`, `SectionTensorNormalized`, `SectionPullNormalized`,
  `sectionScalarRestriction`, and the existence theorem.
- `Sheaf.Paper.InternalDerivedScalarComparisons` (publicly imported by the preceding
  dependency): `Modules`, `D`, `V`, `B₀`, `B`, `L`, `F`, `scalarAdj`, `TensorNormalization`,
  `TensorNormalized`, `PullNormalized`.
- `Sheaf.Paper.ModuleRingedToposDerivedComparison`: `ordinary_exact_flat_kflat`,
  `derived_homEquiv`, `delta_comparison`, and the fixed section derived functors.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  `proEtaleRingRestrictionDerivedPullback`, `proEtaleRingRestrictionDerivedDirectImage`,
  its existsUnique computation-unit characterization, `proEtaleRingSheafChangeAdjunction`.
  The statement uses their section realization with its actual object/Hom universes.
- `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact`, through
  the recorded internal/section tensor identification, fixes the ringed mu used here.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `exactFunctor`, `IsFlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, via the normalization predicates.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `CochainComplex.IsKInjective`.
- `Sheaf.Paper.InternalScalarMateProjection`: `scalarRestrictionPull`,
  `scalarRestrictionPush`, `scalarCoefficientPull`, `scalarTensorPull`.
- `Sheaf.Paper.ScalarGeometricExchangeRectangle`: `scalarSectionPushComparison`.

The other stated proof dependencies are imported privately. The main theorem docstring
contains the six-step proof of the DAG node. The only other theorem,
`flatScalarCoefficientMap_linear`, is the named proof required by the explicit regular
coefficient-map construction. Its proof is postponed and its docstring gives the complete
multiplication-preservation argument. Both theorem bodies are `sorry`; all definitions
have actual data. No new Lean construction, dependency module, or statement correction is needed.
The three definition nodes below record existing constructions only.

Edge cases: identity coefficient change and identity geometric map retain their actual
units and compositors; the zero coefficient ring and zero object need no nontriviality
assumption; empty schemes are allowed; arbitrary unbounded complexes and all integer
degrees remain included; flatness is required globally exactly as in the node, not only
on X and Y. Small pro-etale objects are in u+1 and their morphisms in u; coefficients and
modules are in u+1. The section `HasDerivedCategory` binders choose localization models,
not an equality of the site object and Hom universes. No properness, smoothness,
constructibility, finite coefficient presentation, completeness or boundedness is assumed.

Searches performed with msearch.py:

- LeanFinder: “The canonical conjugate pullback scalar change isomorphism agrees with
  tensor pullback comparison under scalar restriction”: eight results, ordinary
  base-change tensor and scheme pullback-triplet maps, plus
  `SheafOfModules.conjugateEquiv_pullbackComp_inv`; none states this derived square.
- Loogle: `SheafOfModules.pullbackComp, CategoryTheory.conjugateEquiv`: one hit,
  `SheafOfModules.conjugateEquiv_pullbackComp_inv`, an underived composition statement.
- LeanSearch: “The restriction of the derived scalar extension pullback conjugate is the
  canonical derived tensor pullback comparison”: eight results, ordinary restriction,
  presheaf pullback, derivations and open restriction. None has the required statement.
- Mathlib grep: `derivedComapLowerStarIso|flat_coefficient_square|TensorNormalized`:
  zero hits.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the node id found only its consumer's
  proof docstring in RestrictedCoefficientMateProjection. Searches for all proposed
  declaration names found no duplicates. Inspection found and reused the normalized
  scalar interfaces and canonical restriction / coefficient / tensor pullback helpers.

Validation: scompile.py compiles each file separately against the published library.
The final full packet is checked again by deliver2.py, including server preflight.
There is no STATEMENT-DISPUTED flag and no mathematical node fault found.

## Return repair and self-check

The returned immutable head was d53b89647312. The saved packet's initial dry run
passed as 79e56aefd77, confirming that H2 required a semantic ownership repair beyond
the mechanical checks. I compared the saved node against current main: only the
permitted lean and stmt_deps fields differ after rebasing the saved record on main.
The Lean module and its theorem signature are unchanged from the saved packet.

H2: scalarRestrictionPull, scalarRestrictionPush, scalarCoefficientUnit,
scalarCoefficientPull and scalarTensorPull are plain definitions, not choices from
internal_scalar_mate_projection. They now belong to
def-sfb-scalar-restriction-tensor-comparison-data. sectionScalarRestriction,
sectionScalarTensor, sectionScalarCoefficient and SectionTensorNormalized are plain
definitions before the normalization theorem, now owned by
def-sfb-section-scalar-tensor-normalization-data. scalarSectionPushComparison is
exactly ModuleRingedComparison.derivedPushComparison with F unfolded, and now belongs
to def-sfb-scalar-section-push-comparison-data. The original published modules are
neither copied nor moved. def-sfb-internal-section-scalar-pullback-comparison-data
is explicitly cited for SectionScalarComparison, SectionScalarNormalized,
scalarSectionPullComparison and SectionPullNormalized. The definition owners
def-sfb-internal-derived-scalar-comparisons, def-pd-section-module-operations-data,
def-pd-section-derived-tensor-data and def-pd-section-derived-realization are also cited.

The theorem does not apply proEtaleRingRestrictionDerivedDirectImage directly. Its
interface takes commutative-ring-valued sheaves and the independently constructed
proEtaleRingDerivedDirectImage localization model. The statement here uses the fixed
reconstructed section ring, scalarDerivedRestriction and ModuleRingedComparison's
fixed section derived functors. Identifying their types definitionally would require
additional ring-forgetful and localization-model transports. Instead the displayed
FlatSectionDirectImageNormalized predicate specifies the same ordinary identity-on-
sections map and K-injective computation-unit square in the actual fixed realization,
and the conjugation equation ties that normalized map to actual derivedComapLowerStarIso.
No arbitrary map replaces the canonical map, and no equality of site universes is imposed.

Self-check with the node, all new records and source definitions open: scalar
restriction/pullback is the exact localization composite, scalar restriction/pushforward
is its inverse's geometric mate, scalarCoefficientUnit retains localization and single
factors, scalarCoefficientPull retains the pullback unit, and scalarTensorPull is the
actual specified tensor comparison. SectionTensorNormalized retains all three clauses:
ordinary pure tensors, the flat-term K-flat computation square, and conjugation of t.
The section pushforward alias retains the fixed derivedPushComparison. The original
prime/field/scheme hypotheses, global exactness assumption, both flatness clauses,
both geometric exactness clauses, both unit equations, equality of d with its mate,
PullNormalized, existential section/unit/d normalization, and final tensor equation
are unchanged. Identity maps, zero coefficients, empty schemes, and unbounded complexes
remain covered. No STATEMENT-DISPUTED issue was found. No second agent was started,
as explicitly instructed by the dispatcher; the maintainer supplies independent review.

## New nodes

- def-sfb-scalar-restriction-tensor-comparison-data owns the five existing definitions
  scalarRestrictionPull, scalarRestrictionPush, scalarCoefficientUnit,
  scalarCoefficientPull and scalarTensorPull in Sheaf.Paper.InternalScalarMateProjection.
  Its statement follows their actual composites, mate, degree-zero coefficient and
  tensor map. Source: the current blueprint rational proof (1), (3), Stacks
  0D6D/07A6/0D6E/06YY/07A4, and the published definition docstrings.
- def-sfb-section-scalar-tensor-normalization-data owns sectionScalarRestriction,
  sectionScalarTensor, sectionScalarCoefficient and SectionTensorNormalized in
  Sheaf.Paper.InternalScalarPullbackNormalization. It states their localized
  restriction, tensor functor, degree-zero comparison and complete normalization
  predicate. Source: current rational proof (1), integral proof (1), Stacks
  03EK/06YY/06YU/07A6, and the published definition docstrings. It builds on the
  existing section scalar comparison data node rather than duplicating that node.
- def-sfb-scalar-section-push-comparison-data owns scalarSectionPushComparison in
  Sheaf.Paper.ScalarGeometricExchangeRectangle, exactly the alias of the fixed
  derivedPushComparison in the functor notation F. Source: rational proof (1),
  Stacks 07A6, and the published definition docstring.

Each new record is existing:true and introduces no module. A declaration-owner scan
of all DAG nodes found the exact names only in theorem records, with no definition
owner. The similarly named quotient SectionTensorNormalized has a distinct namespace
and coefficient-specific construction. blueprint_refs.py searches for
sectionScalarRestriction and scalarRestrictionPull return zero blueprint nodes.
Mathlib grep of all seven key names returned zero hits; rg found no upstream
WeilConjectures definitions and found the published definitions in the three modules
above. The new LeanSearch query on canonical derived internal scalar restriction,
regular coefficient pullback and section normalization returned eight ordinary scalar
restriction/presheaf constructions, including ModuleCat.restrictScalars and
PresheafOfModules.restrictScalars. LeanFinder on derived scalar restriction mates
and tensor normalization under section equivalence returned eight ordinary
ModuleCat extension/restriction unit, Hom and counit lemmas and
CategoryTheory.Mod_.scalarRestriction_hom. None gives the specialized unbounded
internal/section constructions. Exact queries and returned names are copied into
each node's mathlib_searches. Existing project constructions are reused verbatim.

Signatures of the reused definitions (verbatim before `:=`; the surrounding
universe and coefficient/derived-category binders are those of the published modules):

def-sfb-scalar-restriction-tensor-comparison-data:

```lean
def scalarRestrictionPull (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L Λ' f ⋙ V a X ≅ V a Y ⋙ L Λ f

def scalarRestrictionPush (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    F Λ' f ⋙ V a Y ⟶ V a X ⋙ F Λ f

def scalarCoefficientUnit (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    (V a T).obj (𝟙_ (DerivedCategory (Modules Λ' T))) ≅ B a T

def scalarCoefficientPull (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (L Λ f).obj (B a Y) ≅ B a X

def scalarTensorPull {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : DerivedCategory (Modules Λ Y)) :
    (L Λ f).obj (M ⊗ N) ⟶ (L Λ f).obj M ⊗ (L Λ f).obj N

```

def-sfb-scalar-section-push-comparison-data:

```lean
def scalarSectionPushComparison
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
    {U V : Scheme.{u}} (h : U ⟶ V) :
    F R h ⋙ ModuleRingedComparison.derivedFunctor R V ≅
      ModuleRingedComparison.derivedFunctor R U ⋙
        ModuleRingedComparison.derivedPushforward R h

```

def-sfb-section-scalar-tensor-normalization-data:

```lean
def sectionScalarRestriction (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) :
    V a T ⋙ (ModuleRingedComparison.derivedEquivalence Λ T).functor ≅
      (ModuleRingedComparison.derivedEquivalence Λ' T).functor ⋙
        SheafOfModules.scalarDerivedRestriction.{u + 1, u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (coefficientMap a T))

def sectionScalarTensor (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    DerivedCategory (ModuleRingedComparison.modules Λ T) ⥤
      DerivedCategory (ModuleRingedComparison.modules Λ T)

def sectionScalarCoefficient (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u}) :
    (ModuleRingedComparison.derivedEquivalence Λ T).functor.obj (B a T) ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
        ((ModuleRingedComparison.equivalence Λ T).functor.obj (B₀ a T)))

def SectionTensorNormalized (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (s : SectionScalarComparison a T) (t : TensorNormalization a T) : Prop

```

Validation: the unchanged Lean module compiled cleanly with scompile.py (sandbox
and library passes). The first repaired dry run requested import_flags on the new
node records; added empty lists, with no mathematical or Lean change. The metadata
self-check confirms exact citation/dependency agreement and no dependency cycle.

## Second reading by Q79

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
