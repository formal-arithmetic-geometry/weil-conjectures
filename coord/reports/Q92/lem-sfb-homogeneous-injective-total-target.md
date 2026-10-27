## Worker report

The module `Sheaf.CategoryTheory.HomogeneousInjectiveTotalTarget` states
`CategoryTheory.CondensedBar.homogeneous_injective_total_target`. Its only theorem
has proof `sorry`. All helper definitions and structures have complete data; in
particular nothing chooses a total complex, induction functor or homogeneous
function object from this theorem. The named structures are specifications of the
constructions asserted in this item, with the underlying objects and every map
fixed by the displayed formulas, rather than independent replacement notions.

The natural-language statement and its accepted proof are unchanged. The existing
nodes `def-sfb-condensed-free-module-generators`,
`def-weil-extension-by-zero-presheaf`, and
`def-weil-presheaf-modules-sheafification` are added to statement dependencies
because the statement uses their constructions directly. No new nodes or dependency
repairs are needed. No statement dispute was found.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Arbitrary commutative condensed ring A on the coherent profinite site | `A : CondensedBar.Ring.{u}`, the existing `CommMon` of abelian sheaves, not a constant or topologically presented ring |
| Size convention, small coherent site | Explicit `universe u`; `Profinite.{u}` with `coherentTopology`, abelian coefficients in `AddCommGrpCat.{u + 1}` and module objects at the existing coefficient size |
| Profinite group G and its condensed continuous sections | `G : Type u`, `Group`, `TopologicalSpace`, `IsTopologicalGroup`, `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace`; actions use `C(S,G)` |
| E, M, U, and internal invariants | Existing `Equivariant A G`, `Modules A`, `forgetAction`; the contextual F is the recorded normalized invariants notion, and no conclusion of this item uses F |
| Ordinary cochain categories and injective resolutions | Existing `CochainComplex`, `InjectiveResolution`, `I.cochainComplex`; Nat complexes encode nonnegativity and are extended by `embeddingUpNat` to the ordinary integer-indexed complexes |
| Free A[P] is the stated sheafification, equivalently extension by zero | `freePresentation` identifies `(sectionsFunctor A).obj (freeParameter A P)` with `homogeneousFreeSheaf A P`; this is precisely the existing sheafification of `extensionByZeroPresheaf` applied to the slice unit. Its sections before sheafification are the direct sum indexed by `V ⟶ P` |
| A[P] is flat for every profinite P | `flat` asserts preservation of finite limits and finite colimits for `tensorLeft (freeParameter A P)`, i.e. exactness of tensoring with that module |
| Translation induction L(M)=A[G] tensor M | `HomogeneousFreeInduction.functor` and the natural `underlying` isomorphism to the actual internal `tensorLeft`; `translation` states k([g] tensor m)=[kg] tensor m on every test S |
| L is an exact left adjoint to U, with the specified two formulas | `adjunction`, `exact`, `untranspose` ([g] tensor m maps to g.h(m)), and `transpose` (evaluation at [1]); `homogeneousParameterGenerator` uses the unit of the existing free-forgetful adjunction |
| U is exact and preserves injectives | `forgetExact`, `forgetInjective` |
| A nonnegative equivariant injective resolution exists for every N | `resolutions : ∀ N, Nonempty (InjectiveResolution N)` |
| For every such resolution, Us is an underlying injective resolution | `underlyingInjective` quantifies every N, I, q; `underlyingQuasiIso` is the mapped augmentation itself. The image of the single complex is canonically the underlying single complex, since U is additive. Thus these are exactly the terms and augmentation of Us, not an independently chosen resolution |
| I is K-injective | `kInjective` uses Mathlib's `IsKInjective` on `I.cochainComplex`, whose definition says every map from an acyclic complex is null-homotopic |
| T^(p,q) is the underived internal Hom with the displayed action | `functions p q : HomogeneousFunctions A.toMon G (I.X q) p`, plus equivariant `term` isomorphisms; the reused definition retains the actual slice `homObj`, actual free module and the full diagonal action formula |
| Horizontal alternating deletion and vertical postcomposition | `horizontal` and `vertical`, quantified over p,q,S,c,T,f and tuples of continuous maps; `homogeneousTargetValue` evaluates through the existing internal-Hom identification |
| Equivariance, square-zero differentials and commuting horizontal/vertical maps | The maps are arrows of `Equivariant A G`, and `double : HomologicalComplex₂ ... (.up ℕ) (.up ℕ)` supplies both square-zero laws and the commuting square law |
| First quadrant and finite-diagonal signed total | Nat bicomplex indices encode the first quadrant. The existing `double.total (.up ℕ)` is the sum over p+q=n with the existing signs d_h+(-1)^p d_v; `hasTotal` supplies its coproduct existence |
| Every bidegree and total term is equivariantly injective | `injective`, `totalInjective`; `negative` gives zero in each negative integer degree, which also implies injectivity there |
| T vanishes below zero | `negative` on the actual extension of `double.total` |
| Constants define an equivariant cochain map delta:I→T | `constants`, `constantValue`, `delta`, `delta_components`; the latter fixes delta by the (0,q) total coprojection |
| All action and adjunction formulas after every profinite base change | Homogeneous action already quantifies T→S; horizontal, vertical and constant formulas also quantify every T→S. Induction formulas quantify arbitrary S and their maps are internal module maps, hence restrict naturally; the action's own naturality field supplies the restriction law |

Abelianness is conclusion data, `[abelian : ActionAbelian A G]` inside
`HomogeneousInjectiveTargetData`. This is the dependency's fixed-addition interface,
so the theorem adds no abelianness or enough-injectives hypothesis. The helper
`HomogeneousInjectiveTotal` uses that interface only to type extension by zero.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, its actual actions,
  linear morphisms, regular module and forgetful functor.
- `Sheaf.CategoryTheory.CondensedActionModule`: `ActionModule`, `Modules`,
  `sectionModule`, `forgetAction`, the action category and its fixed addition.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: the ordinary cochain and
  localization convention; no alternate derived category is introduced.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`:
  `Injective`, `InjectiveResolution`; `.Abelian.Injective.Extend` provides
  `InjectiveResolution.cochainComplex`.
- `Sheaf.CategoryTheory.CondensedEquivariantBarData`: `Ring`, `Modules`,
  `Equivariant`, `sectionsFunctor`, `sections`, `freeParameter`, `ActionAbelian`.
- `Sheaf.CategoryTheory.CondensedHomogeneousFunctionsInjective`:
  `HomogeneousFunctions`, `homogeneousEvaluate`, and the proof input
  `homogeneous_functions_injective`.
- `Sheaf.CategoryTheory.CondensedInternalBarResolution`: `freeAdjunction`,
  `onSections`, `pureTensor`; only the explicit definitions are used, not a choice
  from its resolution-existence theorem.
- `WeilConjectures.CategoryTheory.DoubleComplexTotal`: the recorded
  `HomologicalComplex₂`, `total`, `ιTotal` interface, provided by Mathlib through
  this recorded module. Mathlib's total signs are horizontal + (-1)^p vertical.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`:
  `SheafOfModules.extensionByZeroPresheaf`; Mathlib's module sheafification module:
  `PresheafOfModules.sheafification`.
- Proof imports preserve the stated plan: `ExtensionByZeroFlat`
  (`isFlat_extensionByZero_unit`), `InternalSectionTensorComparison`
  (`internal_section_tensor_comparison`), `TensorClosed` (`tensorClosed`),
  `Injective.Preserves` (`Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits`),
  Mathlib `EnoughInjectives` (`IsGrothendieckAbelian.enoughInjectives`), and
  Mathlib `KInjective` (`CochainComplex.isKInjective_of_injective`).
  The free-linearization and action-infrastructure proof nodes have no recorded
  module in the read clone; their proof steps are retained in the theorem docstring.

Edge cases checked before writing: P empty yields the empty direct sum and zero
free module, so its tensor is exact; G trivial still has the one-point represented
parameter and all adjunction formulas; the zero ring and zero modules are admitted;
p=q=0 gives deletion f(h1)-f(h0), so constants have zero horizontal differential;
the sign at p=0 is +1; n=0 has one total summand, and negative n has none. No finite,
abelian or discrete condition is placed on G. No injectivity of section modules
J(S), no projectivity of A[P], and no assumption that sheafification remains
sectionwise free is used.

Searches for an existing whole statement (2026-10-24):

- `msearch.py ... leanfinder "Exact free induction for internal profinite group actions on condensed modules and homogeneous injective total complex"`: eight hits, including
  `Condensed.profiniteFree`, `Condensed.profiniteSolid`, and light condensed internal
  projectivity facts; none treats arbitrary internal ring objects and this total.
- `msearch.py ... loogle "CategoryTheory.InjectiveResolution, CategoryTheory.Functor.PreservesInjectiveObjects"`: zero hits for this combined query.
- `msearch.py ... grep "homogeneous|coinduc|injective" Condensed`: general condensed
  colimit, topology and light condensed results; no full statement.
- `msearch.py ... leansearch "Free induction exact for internal group actions on condensed modules and injective homogeneous total complex"`: eight hits, including
  ordinary-ring `Condensed.free` and `freeForgetAdjunction`, and continuous
  cohomology of topological module categories; these are different categories.
- `rg` over the named `lean/WeilConjectures` and `lean/Sheaf` trees for
  `homogeneous`, then narrowed to `homogeneous_functions_injective`,
  `HomogeneousFunctions`, homogeneous totals, and this item's exact id: found
  the reused homogeneous-functions module and the downstream
  `EquivariantResolutionBarNormalization` module. Its theorem is a derived
  comparison and its homogeneous bar uses trivial coefficient actions, so neither
  states this arbitrary-equivariant-resolution total-target assertion. The exact
  item-id search in `WeilConjectures` had no match.

The latest blueprint direct-images paragraph (3) was opened and read. This item is
an agent-expanded auxiliary statement, as its source already records; its exact
independent internal-bar reference remains WANTED. The supplied accepted eight-step
DAG proof is copied as a complete proof plan in the theorem docstring.

## Second reading by Q92

This is a single-worker consistency reread; independent review belongs to the
maintainer under the dispatch brief. I reopened the node and checked each clause
against the table and the full helper structures. In particular, the conclusion
quantifies over every resolution; homogeneous action is not replaced by an
arbitrary action; both adjunction directions retain generalized-generator formulas;
the total is Mathlib's signed finite-diagonal total; delta is a chain map fixed by
constants in the (0,q) summand. The initial compile identified the missing
abelian-category binder needed by the helper's extension by zero. That binder was
added to the helper, while the full assertion supplies the abelian data as part of
its conclusion. No node statement was changed and no mathematical case was removed.
