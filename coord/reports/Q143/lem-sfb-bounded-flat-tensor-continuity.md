## Worker report

Item: lem-sfb-bounded-flat-tensor-continuity, Q143 stage 2.
Module: `Sheaf.Paper.BoundedFlatTensorContinuity`.
Namespace: `AlgebraicGeometry.ProEtale.BoundedFlatTensorContinuity`.

The module states the full strict tensor-presentation result in the section-ring
realization explicitly allowed by the node. `bounded_flat_tensor_continuity` carries
all clauses through the final actual-leg equation; `replacement_independence` states
its last independence clause using the specified natural zigzag. Both proofs are
`sorry`, with the eight-step DAG proof in their docstrings. No theorem is proved.
No statement correction, new node, or dependency repair is needed. Only the item's
`lean` field changes. The helper declarations belong to this node's strict-cocone
and comparison construction and are all listed in `lean.declarations`.

### Every hypothesis

| Informal hypothesis | Lean rendering |
| --- | --- |
| Prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| Field of characteristic p > 0, p different from ell | `(p : ℕ) (k : Type u) [Field k] [CharP k p] (_hp : 0 < p) (_hne : p ≠ ℓ)` |
| Separated finite-type k-schemes X and Y | `X Y : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))`, with `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on both structure maps |
| A qcqs k-morphism f | `f : X ⟶ Y` in that over category, `[QuasiCompact f.left] [QuasiSeparated f.left]` |
| Arbitrary commutative condensed ring R | Section variable `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, `[MonObj Λ] [IsCommMonObj Λ]`; this is the unbundled form of the recorded arbitrary `Profinite.CondensedRing`, not a topological-ring special case |
| Coefficients pulled back from the point | `ring Λ Z` and `modules Λ Z` are the existing `ModuleRingedComparison` section-ring and sheaf-module constructions for `condensedRingObj Λ Z` |
| Ordinary unbounded derived categories and the stipulated size convention | `DerivedCategory (modules Λ Z)` with `[∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ Z)]`; site objects have universe u+1 and site morphisms u, and module/derived morphisms and diagram sizes use u+1 |
| Small nonempty filtered index category | `{I : Type (u + 1)} [SmallCategory I] [IsFiltered I]`; `IsFiltered` includes nonemptiness |
| A coefficient diagram and its colimit with specified legs | `P : I ⥤ modules Λ Y.left`, `c : Cocone P`, `_hc : IsColimit c`; `C = c.pt`, `v_i = c.ι.app i` |
| All P_i flat | `_hP : ∀ i, exactFunctor _ _ ((curriedTensor _).obj (P.obj i))` |
| C flat | `_hC` with the same predicate at `c.pt` |
| All f*P_i flat | `_hfP` with the same predicate at `(pullback Λ f.left).obj (P.obj i)` |
| f*C flat | `_hfC` at `(pullback Λ f.left).obj c.pt` |
| K and a chosen representing complex | `K : DerivedCategory (modules Λ X.left)`, `Kc : CochainComplex (modules Λ X.left) ℤ`, `_eK : DerivedCategory.Q.obj Kc ≅ K` |
| A common strict lower bound | `(a : ℤ) (_hK : ∀ n : ℤ, n < a → IsZero (Kc.X n))` |

Flatness above is literally exactness of the published fixed-left-factor tensor
functor, the defining predicate exposed by def-pc-flat-sheaf-modules. The defining
fixed-right-factor convention is equivalent by the published symmetric braiding.
No flatness of Kc's terms, boundedness of GK or of J(E_i), properness of f,
constructibility of K, or finiteness of the coefficient presentation is imposed.
The HasDerivedCategory arguments specify the localization and its morphism universe,
as required by the recorded size convention, rather than extra mathematical data.

### Every conclusion and its maps

1. `Nonempty (IsColimit ((pullback Λ f.left).mapCocone c))` is the pulled-back
   module colimit, including exactly the legs f*(v_i).
2. `tensorWith Λ Z Kc` is the published signed direct-sum `totalTensor Λ Z`
   with its second variable restricted by `CochainComplex.singleFunctor _ 0`.
   `pulledTensor` first applies the actual `pullback`. Thus its objects are the
   strict E_i and E, and its maps are exactly `1 ⊗ f*(v_i)`, not arbitrary maps
   between isomorphic objects. The next two conjuncts assert `IsZero` below a
   separately for all E_i and for E.
3. `IsColimit ((pulledTensor ...).mapCocone c)` and the following universally
   quantified `HomologicalComplex.eval` colimit clause express the tensor colimit
   as a colimit of complexes and in every degree, with the same cocone.
4. `∃ A, IsKFlatIndependentCoefficients A ∧ (∀ n, exactFunctor ... (A.X n)) ∧
   Nonempty (Q.obj A ≅ (derivedPushforward Λ f.left).obj K)` states existence of
   a flat-term K-flat representative of GK. The universal next conjunct applies
   to every such A and every representative isomorphism, without a bound on A.
5. For every such A, `IsColimit ((tensorWith ... A).mapCocone c)` and
   `IsIso (colimit.desc (P ⋙ tensorWith ... A) ((tensorWith ... A).mapCocone c))`
   assert invertibility of the actual canonical map of complexes. `RepresentsCocone`
   gives endpoint representation isomorphisms with
   `derivedTensorWith Λ Y.left ((derivedPushforward Λ f.left).obj K)` and, for
   every i, the equation `Q.map (F.map v_i) ≫ e.hom = (ei i).hom ≫ D.map v_i`.
   This records the actual derived coefficient tensor maps simultaneously.
6. `∃ J η, ∀ M, QuasiIso (η.app M) ∧ (J.obj M).IsKInjective` gives a functorial
   K-injective replacement and natural augmentation. K-injectivity is precisely
   Mathlib's null-homotopy condition against every acyclic complex; testing shifts
   gives the equivalent Hom-complex acyclicity in the node. Injectivity of the
   individual terms is not required by the item's definition of a replacement.
7. The final nested `∃ e, ∃ ei` identifies Q(E) and all Q(E_i) with
   `derivedPulledTensor Λ f.left K`. That functor is the published derived
   pullback L applied to degree-zero coefficients, followed by the published
   derived tensor with K. The first equation intertwines each localized strict
   tensor leg with `1_K ⊗ Lv_i`. Flatness and exact pullback give the LP_i = f*P_i
   and LC = f*C identifications of proof step 3.
8. For *every* J and eta of the given kind, `replacedPush Λ f.left J` is J followed
   by actual termwise `pushforward`. The final `IsIso (Q.map (colimit.desc ...))`
   is exactly Q(colim f_*J(E_i)) -> Q(f_*J(E)). `replacementComparison` is real
   data: the inverse composite of `G.mapIso (asIso (Q.map (η.app M)))` and the
   existing `rightDerivedFunctorObjQIso (J.obj M)`. It identifies the target
   with G(Q(E)), and G(e) identifies this with G(K tensor^L LC).
9. The displayed equation following that `IsIso`, for every i, includes
   `Q.map (colimit.ι ... i)`, the same `Q.map (colimit.desc ...)`, the normalized
   `replacementComparison`, and `G.map e.hom`. Its right side uses the normalized
   computation at E_i and `G.map ((derivedPulledTensor ...).map v_i)`. Thus it
   identifies the actual composites of colimit legs with G(1_K tensor Lv_i).
10. `replacement_independence` uses the concrete zigzag
    `Functor.whiskerLeft J η' : J ⟶ J ⋙ J'` and
    `Functor.whiskerRight η J' : J' ⟶ J ⋙ J'`.
    The common augmentation is `η ≫ Functor.whiskerLeft J η'`; its K-injective
    quasi-isomorphism property is asserted by the existential hJJ'.
    `ReplacementCompatible` asserts invertibility of the *induced* localized
    colimit map, equality of the target identifications with the specified
    K-injective computations for every complex, and the square of the actual
    `colimit.desc` arrows. `colim.map` is induced by the natural replacement map,
    so its restrictions are exactly the maps on every colimit leg. This
    independence property does not require the lower bound or coefficient
    flatness; those are needed for continuity, not for comparison of resolutions.

All colimits inside Q are Mathlib colimits of cochain complexes over sheaves of
modules, constructed degreewise; none is a colimit in the triangulated derived
category. `RepresentsCocone` and `ReplacementCompatible` are predicates about
specified maps. None assumes the conclusion as data or selects an arbitrary map.

### Dependency declarations read and used

The complete item and every statement dependency were read, including the source
signatures and docstrings of the following declarations. Existing records are used
unchanged; no private copy or fallback notion is introduced.

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`. The setting
  is rendered by the explicit field, over-scheme and finiteness binders; no
  compactification is needed for this continuity lemma.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`, `condensedRingObj`.
- `def-weil-size-convention` is the recorded metatheoretic convention, not a Lean
  declaration. The universe choices are made explicitly as above.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward` and
  `moduleObjectDerivedPullback` (the actual derived underived composites).
- `Sheaf.Paper.ModuleRingedToposDerivedComparison`:
  `AlgebraicGeometry.ProEtale.ModuleRingedComparison.ordinary_exact_flat_kflat`,
  `ordinary_monoidal`, and `module_ringed_topos_derived_comparison`, reexporting
  the recorded section realization. Its `modules`, `ring`, `pullback`, `pushforward`,
  `derivedPullback`, `derivedPushforward`, `tensor`, and `totalTensor` are the
  exact existing constructions used throughout. In particular the ringed
  `derivedPushforward` is `(pushforward Λ f).rightDerivedFunctor`, and the exact
  `derivedPullback` is `(pullback Λ f).mapDerivedCategory`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.colimit`,
  `colimit.desc`, with the existing `Cocone`, `IsColimit`, and `CategoryTheory.IsFiltered`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite` and its defining `CategoryTheory.exactFunctor`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`,
  the direct-sum signed total tensor underlying the already published totalTensor.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, with `QuasiCompact` from its existing module.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated` (quasi-compact diagonal).
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.

Proof-only dependencies are imported explicitly: the recorded
`upperStarLowerStarAdjunction` in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`;
`flat_single_derived_normalization` in `Sheaf.Algebra.Homology.FlatSingleDerivedNormalization`;
`kFlat_fixed_tensor_triangulated` in `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`;
`tensorLeft_preservesColimits_independentCoefficients` in
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`;
`CategoryTheory.exists_rightDerived_of_enough_isKInjective` in
`Sheaf.CategoryTheory.KInjectiveTotalDerived`; the exact-colimit homology instance in
`WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits`;
`AlgebraicGeometry.Scheme.ProEt.boundedContinuityDirectImage` in
`Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage`;
`CategoryTheory.moduleSheaves_colimits_forgetful` in
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`;
and `CochainComplex.IsKInjective.Qh_map_bijective` in
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
The computational `rightDerivedFunctorObjQIso` is used directly from
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`.

### Sources, edge cases, searches, validation

Read Hemo--Richarz--Scholbach, Lemma 5.3(1), proof of (5.4), printed page 14,
from the local PDF, and the current blueprint rational proper base-change proof,
paragraph (1). Their continuity statement requires a common lower bound, exactly
as retained here. The module does not claim arbitrary unbounded continuity.

Checked: one-object filtered category and f = id; constant coefficient diagrams;
zero K and the zero coefficient ring; empty schemes; a negative bound a; complexes
nonzero in arbitrarily high degrees; an unbounded GK representative A; and
K-injective replacements unbounded below. Empty I is intentionally excluded by
`IsFiltered`, as in the node. There is no assumption that the coefficient objects
or any of these complexes be nonzero. The degree-zero coefficient at n = a is
allowed, since the vanishing condition uses n < a. The index and site object
universe is u+1, not the site's smaller morphism universe u.

Existing-notion searches (full wrapper output saved in `searches.jsonl`):

- msearch.py / LeanFinder: `uniformly bounded below flat tensor complexes filtered
  colimits derived direct image proetale` -> 8 generic flat-module and categorical
  flatness hits, including `Module.Flat.lTensor_shortComplex_exact` and
  `Module.Flat.iff_preservesFiniteLimits_tensorLeft`; no full statement.
- msearch.py / Loogle: `SheafOfModules, "colimit"` -> 7 sheaf-colimit existence,
  preservation and presentation declarations; none states the strict bounded
  tensor and derived qcqs comparison or replacement independence.
- msearch.py / grep: `bounded.*[Cc]ontinuity|[Ff]lat.*[Tt]ensor.*[Cc]olimit` ->
  9 unrelated analysis/topology hits, no match.
- msearch.py / LeanSearch: `A filtered colimit of flat sheaf coefficients tensors a
  uniformly bounded below complex and commutes with qcqs proetale derived direct
  image` -> 8 generic complex/sheaf colimit declarations, notably
  `HomologicalComplex.instHasFilteredColimitsOfSize`,
  `SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesValRingCat`, and
  `SheafOfModules.Presentation.isColimit`; no full statement.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for bounded continuity, flat tensor
  colimits, `BoundedFlatTensorContinuity`, `RepresentsCocone`, and
  `replacementComparison`: existing general continuity and tensor ingredients
  only, no duplicate of the item or its helper declaration names.
- grep for this blueprint id in `lean/WeilConjectures`: no hit. There is no
  repair note or earlier delivery for this item in the prescribed shared records.

Every definition contains real data or an explicit proposition. All variables and
universes are explicit, with `set_option autoImplicit false`; no local notation,
private definition, local instance, or diagnostic command is left in the module.
Initial scompile.py validation passed both sandbox and library compilation
(17.3 s and 12.9 s). Final validation and deliver2.py preflight are recorded below.

## Second reading by Q143

The dispatcher explicitly forbids starting other agents, so this section records
an author's second pass; it does not claim that another worker independently read
it. The maintainer supplies the independent mathematical delivery review.

Reopened the complete node and Lean file. Checked every row and numbered clause
above against the binders, nested conjunctions, and actual arrow endpoints. The
comparison equations include the localized strict legs and the specified derived
functor maps. The final comparison is `Q.map (colimit.desc ...)`, not an arbitrary
isomorphism with the same endpoints. Replacement independence compares the
specified natural zigzag and normalized computations, including its colimit
square. No bound is accidentally placed on J(E_i) or GK. Exactness is the
recorded tensor flatness predicate. The section-ring encoding uses the node's
recorded exact monoidal equivalence and ordinary unbounded derived categories.

One presentation issue found and repaired: the interrupted draft relied on
transitive imports for several recorded statement and proof dependencies. Added
their explicit public/ordinary imports as the stage requires. No mathematical
statement, helper construction, or node field other than lean was changed.
