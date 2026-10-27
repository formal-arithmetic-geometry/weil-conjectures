## Worker report

The delivery states `CategoryTheory.CondensedBar.condensed_bar_scalar_resolution_comparison`
in `Sheaf.CategoryTheory.CondensedBarScalarResolutionComparison`. Its only postponed
proof is this theorem, with the complete twelve-step DAG argument in its docstring.
The item's statement, statement dependencies, proof and proof dependencies are unchanged.
No mathematical statement correction or dependency repair is needed.

The earlier worker's stale-assignment diagnosis confused a reviewed stage-1 proof split
with stage-2 completion. The current node has NH's reviewed proof but no `lean` record;
there is no re-split here. The new record supplies the missing Lean statement.
No repair note for this item exists in the read repository.

The source read is main-20261015, six-functors direct-images proof, paragraph (3).
It gives the open-direct-image coefficient argument, not an external proof of the
internal-condensed expansion. The node correctly labels that expansion agent-written
and says an external internal-condensed reference is wanted. The docstring reproduces
the expanded argument rather than falsely attributing it to the blueprint verbatim.

Hypothesis and clause correspondence:

* A commutative condensed ring on the coherent profinite site is exactly the dependency's
  `CondensedBar.Ring`: `CommMon (Sheaf (coherentTopology Profinite) AddCommGrpCat)`.
  `ScalarResolutionAssertion` quantifies over every such A and A', and every morphism a.
  The theorem's `G : Type u`, `Group`, `TopologicalSpace`, `IsTopologicalGroup`,
  `CompactSpace`, `T2Space`, and `TotallyDisconnectedSpace` encode an arbitrary profinite
  group. Compact Hausdorff totally disconnected groups are the inverse limits of finite
  groups meant here. No discrete, finite, countable, or extremally disconnected
  restriction is imposed.
* Internal modules, actions, U and invariants use the dependency's `Modules`,
  `Equivariant`, `forgetAction`, and `Model.invariants`. The latter is the landed
  normalized `Profinite.CondensedAction.Invariants`: its image is fixed after every
  profinite base change. No pointwise-only fixed-section substitute is introduced.
* Universes are explicit: test objects are `Profinite.{u}`, section abelian groups
  have universe u+1, and ordinary derived categories use `HasDerivedCategory.{u+2}`.
  The assertion uses the standard localization, as the existing bar assertion does.
  Action abelianness and the Grothendieck property are existential conclusions before
  the models; they are not added theorem hypotheses.
* A[S] is the existing `freeParameter A P`. `scalarFreeMap` is the same composite free
  functor on a map; `scalarFreeGenerator` is its existing adjunction unit.
  `scalarFreeSheaf` constructs, using Mathlib `PresheafOfModules.freeObj` and
  `PresheafOfModules.sheafification`, the sheafification of
  V maps to the free A(V)-module on Hom(V,P). The section-module equivalence identifies
  `freeParameter` with this sheaf via the first clause of `ScalarFreeProperties`.
* Flatness is `ObjectProperty.flat (freeParameter A P)`, i.e. exact tensoring on both
  sides in the existing symmetric relative tensor category. Degree-zero K-flatness is
  `(HomologicalComplex.quasiIso ... (.up ℤ)).kFlat` on the actual single complex.
  This is the generic K-flat predicate explicitly exposed by the recorded K-flat
  dependency. It works on internal modules without privately copying the specialized
  ringed-site predicate.
* `ScalarParameterComparison.free` is the ordinary A' tensor A[S] isomorphism to A'[S].
  `free_unit` fixes it on each unit generator over each test space, while
  `free_natural` is parameter naturality. `derived_free` asserts that the actual
  left-derived counit on A[S][0] is invertible; composing that counit with the single
  of `free` gives exactly A' tensor-derived A[S] isomorphic to A'[S]. This retains the
  canonical derived comparison rather than merely positing an arbitrary derived object.
* The underived scalar-Hom identification is `ScalarParameterComparison.hom`, a natural
  isomorphism of functors of A'-modules. `evaluation` fixes it by equality on every
  generalized section over every V to T and V to S. Thus it is the scalar-unit,
  restricted-evaluation identification. `parameter` expresses naturality in S.
  `InternalFunctions.internalHom` identifies these functors with the recorded `Mod.ihom`.
* `scalarRHom` uses the recorded
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions` on `InternalFunctions.functor P`.
  Its input `scalarEnoughKInjectives` is an explicit abbreviation using the published
  functorial K-injective replacement and its proven monomorphic quasi-isomorphism;
  it is not a new postponed theorem or a chosen module. `scalarHomUnit` is the recorded
  right-derived unit at the homotopy class of the actual complex.
* `ScalarParameterComparison.derived` is a natural isomorphism of ordinary unbounded
  derived-category functors. It gives the requested derived identification at M[0].
  `normalization` is precisely equation (*) of the DAG proof, with the exact functor's
  localization-factor isomorphisms written explicitly. It applies to EVERY complex L,
  not only to injectives. `scalarRHomPre` is the canonical unit-compatible parameter
  map obtained by inverting the dependency's proven universal bijection; its data
  are fully defined. `derived_parameter` makes the derived comparison natural in S.
* Compatibility with every face AND degeneracy is `ScalarResolutionComparison.cosimplicial`.
  This is an isomorphism of the whole cosimplicial objects, not just of alternating
  cochains. `cochain_terms` identifies its components with the recorded `ScalarModel.bar`;
  `cosimplicial_term` identifies those same components with `c.hom` through the actual
  underlying-module comparison. The existing bar object's generalized-section face
  and degeneracy formulas include the parameter-dependent first action face.
* Nonnegative equivariant resolutions are the existing Mathlib `InjectiveResolution`.
  `ScalarComputation.lifts` supplies a chain map beta with the degree-zero augmentation
  equation. This is exactly the full augmentation equation, since the source is
  concentrated in degree zero. Every beta, not just one selected lift, is quantified.
  `lift_quasiIso` states its quasi-isomorphism and `computation.columns` states every
  column quasi-isomorphism of D_A(beta). The displayed source identification comes
  from the same evaluation-normalized bar isomorphism above.
* The double complex and finite-diagonal total are the dependency's `doubleComplex`
  and `totalCochains`, with differential d_bar + (-1)^p d_resolution. The total map
  is the dependency's `scalarTotalChain`, fixed by `ScalarModel.summands`; invariants
  use `scalarInvariantChain`, fixed by the invariant-inclusion normalization.
* `restricted_unit` and `target_unit` assert invertibility of the ACTUAL canonical
  right-derived-unit comparisons on these columns, not just existence of an
  isomorphism between the objects. The naturality of the actual unit natural transformation is its commuting square
  for U(beta). Combined with `c.normalization` applied to U(J), this identifies the
  source with the restricted A'-resolution comparison through the displayed derived
  scalar-Hom identification. This is the actual localization identification demanded
  in the statement, not only a column quasi-isomorphism.
* `computation.totalQI` and `computation.invariantQI` assert both induced maps are
  quasi-isomorphisms. `chain_square` is an equality of actual chain maps and hence
  commutes term by term. `Model.computation.augmentation_quasiIso` supplies the K and J
  augmentations; `restricted_augmentation` supplies the restricted J augmentation.
  `computation.square` is precisely their square after localization and inversion.
* `independent` gives the two localized comparison equalities for EVERY pair of
  resolutions, EVERY augmentation-preserving j and i, and EVERY pair beta1, beta2.
  Taking identity j and i gives independence of beta. These two equalities and the
  chain-square normalization give independence of the square after inverting its
  augmentations. Resolution-change lifts exist by the same lifting theorem used
  in the DAG proof; no arbitrary isomorphism of unmarked resolutions is used.
* There is no assumption that A' is A-flat or that Res J has injective terms.
  In particular `restricted_unit` asserts exactly the derived comparison which
  replaces that invalid injectivity assumption.

All helper definitions are actual maps, abbreviations of recorded constructions, or
specifications of the clauses of this same theorem. They do not introduce an independent
mathematical notion needing a new DAG definition node. They are listed in
`lean.declarations`. There are no private definitions, local instances, local notations,
auto-bound variables, unnamed sorries, or objects defined using sorry.
`scalarComplexMonoidal` is an explicit alias for the existing published
`Mod.monoidalCategoryCochainComplex`, to avoid repeated tensor-instance searches.
It introduces no tensor data and no hypothesis. Generated size and injectivity
theorems for specifications are disabled to keep ordinary per-file elaboration small. The `letI`s
inside `ScalarResolutionAssertion` instantiate its preceding existential structures;
the public theorem signature contains no let binder.

Dependency declarations read and used:

* `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` (through A.toMon).
* `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, and their actual
  internal linear maps; the dependency's general notion is specialized, not copied.
* `Sheaf.CategoryTheory.CondensedActionModule`: `Profinite.CondensedAction.ActionModule`,
  `forgetAction`, `FixedAll`, and `Invariants` via the bar dependency aliases.
* `Sheaf.CategoryTheory.CondensedEquivariantBarData`: `Ring`, `Modules`, `freeParameter`,
  `InternalFunctions`, `BarDiagram`, `Model`, `ScalarModel`, `ScalarComputation`,
  `doubleComplex`, `totalCochains`, `scalarInvariantChain`, and `scalarTotalChain`.
* `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`: `Mod.extendScalars`,
  `Mod.comap`, `Mod.extendRestrictAdjunction`; its publicly imported derived extension
  gives `leftDerivedFunctorCounit` and restriction's `mapDerivedCategoryFactors`.
* `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: the publicly exposed generic
  `CategoryTheory.MorphismProperty.kFlat`, used with quasi-isomorphisms.
* `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`: `InjectiveResolution`,
  including `cocomplex`, `ι`, termwise injectivity and the augmentation quasi-isomorphism.
* `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded ordinary
  `rightDerivedFunctorOfQuasiIsoResolutions`, its unit and universal bijection.
* `WeilConjectures.CategoryTheory.DoubleComplexTotal`: the dependency's actual
  first-quadrant total framework, used through the recorded bar total.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`, `Qh`,
  `HasDerivedCategory.standard`; def-weil-size-convention is expressed by these universes.

The recorded modules of proof dependencies which already have local source files are
plain proof imports. Nodes without a recorded module are left out rather than invented;
they remain the named steps of the theorem's complete proof docstring. There is no
import of the downstream `CondensedDerivedInvariantBar` theorem and no import cycle.

Searches actually run:

* msearch LeanFinder: "Restriction of scalars comparison for internal condensed profinite
  bar resolutions, free profinite parameter modules flat, derived internal Hom and
  injective resolution total comparison". Eight hits, on `LightCondensed.ihomPoints`,
  internally projective light free modules, and `Condensed.profiniteFree/profiniteSolid`.
  None states the arbitrary internal condensed-ring scalar-resolution theorem.
* msearch Loogle: "Mod.comap, Mod.ihom, InjectiveResolution". Zero hits with the diagnostic
  "unknown identifier 'Mod.comap'"; this query is unavailable for the project namespace,
  not evidence that restriction or internal Hom is absent. The recorded source APIs
  were opened directly and are used.
* msearch grep: "condensed.*bar.*scalar|scalar.*bar.*comparison". Zero Mathlib hits.
* rg in project `Sheaf` and `WeilConjectures` for the exact item ID: no existing declaration.
  File/concept searches found `CondensedEquivariantBarData` and its specifications,
  `CondensedDerivedInvariantBar` (the downstream parent theorem, with weaker aggregate
  scalar computation), the scalar-Hom comparison modules, and the internal bar module.
  None is an exact statement of this node, and the parent theorem is not used circularly.
* The generic internal module, coefficient restriction, free adjunction, internal Hom,
  K-flat predicate, ordinary derived functor and total complex were all reused.

Edge cases read against the signature and formulas: P empty gives the zero free module
and zero internal functions; P a point gives the unit free module; p=0 uses Fin 0 and
retains the action first face into degree one; G trivial is allowed. Zero coefficients
and A'=0 are allowed, as are a=id and nonflat coefficient maps such as Z to Z/2.
No finite/profinite parameter is required nonempty. Naturality quantifies over all
profinite base changes, including empty ones. Resolutions are nonnegative but their
right-derived comparisons are in the ordinary Z-indexed derived category.

No STATEMENT-DISPUTED fault was found. Verification uses only the required scompile.py
wrapper; compile probes also used module mode. Final delivery and preflight results
are reported by the prescribed wrapper.

## Second reading by Q160

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
