## Worker report

The module Sheaf.Paper.CoefficientRingedSquareNormalization states
AlgebraicGeometry.ProEtale.CondensedRing.coefficient_ringed_square_normalization.
The theorem is postponed with sorry; all four helper definitions have real data.
The previous worker's stage-1 stale-dispatch diagnosis does not apply to this
stage-2 assignment: live has reviewed stage-1 split status and no lean binding.

Hypotheses and clauses:

- The prime ell is `ℓ : ℕ` with `Fact ℓ.Prime`. The field is `k : Type u` with
  `Field k`. Positive characteristic p distinct from ell is rendered by
  `Fact (ringChar k).Prime` and `Fact (ringChar k ≠ ℓ)`; a field's positive
  characteristic is prime, so this is equivalent to the source's convention.
- Separated finite-type k-schemes are `X₀ Y₀ : Over (Spec (CommRingCat.of k))`
  with `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on both structural
  maps. `f₀ : X₀ ⟶ Y₀` is precisely a k-morphism.
- R and S are abelian sheaves on the coherent Profinite site, with MonObj and
  IsCommMonObj instances, hence commutative condensed rings. `a : R ⟶ S` with
  `IsMonHom a` is a morphism of those rings. Exact extension on every scheme Z
  is `∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars
  (coefficientMap a Z))`; extension is already a left adjoint and right exact.
- Sites are exactly `Scheme.ProEt.topology`, with object universe u+1 and
  morphism universe u. Abelian sheaves and internal modules use u+1. The
  upstream canonical derived-category instances supply unbounded localization.
- The functors are the full upstream `lowerStar`, `upperStar`, `Mod.comap`, and
  `Mod.extendScalars`, with `rightDerivedFunctor`, `leftDerivedFunctor`, and
  `mapDerivedCategory`, respectively. These are the same operations as the
  recorded moduleObjectDerivedPushforward/moduleObjectDerivedPullback wrappers.
- The fixed internal/section equivalences are used as coordinates, not replaced
  by arbitrary equivalences. The ordinary direct-image bridge is exactly
  `comapLowerStarIso`, identity on underlying sections by
  `Mod.comapMapModComapIso_hom_app_hom`.
- `coefficientRingedDirectImageComparison` constructs C independently of e,
  from universal right-derived composition for both paths, deriving the inverse
  ordinary bridge, and then the canonical identification of derived exact
  restriction with termwise localization. The last path uses the universal
  right-derived composition with exact postcomposition. No hypothesis that
  geometric pushforward preserves K-injectives is introduced.
- `coefficientRingedPullbackComparison` uses the specified derived scalar and
  geometric adjunctions to conjugate that independently constructed C. This is
  the canonical ringed pullback comparison under the conjugacy assertion of
  lem-sfb-ringed-comparison-tensor-adjunction. It does not take the inverse of c
  as a definition, and does not accept an arbitrary pullback isomorphism.
- The first conjunct is equality of C.hom with derivedComapLowerStarIso.inv.
  The second is equality of theta.hom with derivedPullIso.inv, as natural
  transformations between the actual internal derived functors.
- The final forall quantifies over every K-injective S_X complex I.
  coefficientRingedSourceResolution identifies G_R U_X QI with Q(f_R* Res I),
  using the exact restriction factorization and the right-derived unit on Res I.
  coefficientRingedTargetResolution identifies U_Y G_S QI with Q(Res f_S* I),
  using the right-derived unit on I and then exact restriction. The two final
  equalities conjugate C and e by these identifications and equate them with
  Q of the inverse ordinary bridge and Q of the ordinary bridge, respectively.
  There is no assumption that f_S* I is K-injective.

Dependency declarations read and used:

- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible:
  compactificationOverField and its explicit Over-field setting (read; no
  compactification is needed by this normalization).
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients:
  coefficientMap, both coefficient-square equations, comapLowerStarIso,
  derivedComapLowerStarIso, derivedPullIso, and the restriction K-injective
  preservation instance.
- Sheaf.Paper.CondensedModuleDerivedPushpull: moduleObjectDerivedPushforward
  and moduleObjectDerivedPullback are definitionally the full derived functors
  used here. Publicly imported as the recorded operation interface.
- Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions:
  rightDerivedFunctorOfQuasiIsoResolutions and its universal unit signature
  (read). Concrete Grothendieck module categories use the specified upstream
  rightDerivedFunctor model and rightDerivedFunctorObjQIso normalization.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and ProEt.topology.
- def-weil-size-convention is explicitly a metatheoretic convention record.
- Sheaf.Paper.ModuleRingedToposDerivedComparison:
  derivedPullComparison, derivedPushComparison, derived_homEquiv,
  module_ringed_topos_derived_comparison; imported for the proof's faithful
  coordinate transfer. These are fixed operation and adjunction comparisons.
- Sheaf.CategoryTheory.InternalSectionScalarAdjunction:
  sectionScalarMap, InternalSectionScalarAdjunction,
  internal_section_scalar_adjunction; imported for the proof's scalar transfer.
- Sheaf.Paper.RingedComparisonTensorAdjunction:
  canonicalRingedDirectImageComparison, canonicalRingedPullbackComparison,
  ringedComparisonTensorAdjunction; imported for canonical path conjugacy.
- Mathlib.Algebra.Homology.HomotopyCategory.KInjective:
  CochainComplex.IsKInjective, the acyclic-source null-homotopy condition.
- Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition:
  ringedToposDerivedPushforwardComposition (proof dependency).
- Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses:
  grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
  (proof dependency; independent site universes are preserved).
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp,
  MapDerivedCategory and KInjective: rightDerivedFunctorCompIso,
  rightDerivedFunctorNatIso, rightDerivedFunctorIsoMapDerivedCategory,
  mapDerivedCategoryFactors, rightDerivedFunctorObjQIso.

No new nodes and no dependency record repairs. The helper definitions belong to
this item's canonical paths and resolution coordinates and are all listed in
lean.declarations. The generic ringed-tensor presentation has equal site
universes; this delivery does not instantiate it with the pro-etale site or
force u+1=u. Its canonical conjugacy statement explains the internal-coordinate
expression; the constructions here use upstream internal categories directly.
The as-yet-unstated scalar-tensor-realization proof dependency is not imported.

Edge cases checked before writing: a=id, f=id, S=0, zero complexes, the empty
scheme, and arbitrarily unbounded complexes. All four definitions retain these
cases. The resolution maps preserve the full complexes, with no degree bound.
The direction is checked: C goes Res_X then Rf_R* to Rf_S* then Res_Y, while e
has the reverse direction; theta goes T_Y then Lf_S* to Lf_R* then T_X.

Sources opened: local Stacks sites-cohomology.tex lines 3658 onwards (0D6D)
and 4011 onwards (0D6E), and main-20261015 rational proper-base-change proof
paragraph (3). No statement correction or mathematical dispute.

Searches:

- msearch leanfinder: “The canonical derived direct image path comparison for a
  commuting coefficient ringed topos square equals inverse restriction
  pushforward comparison”. Eight hits, ordinary SheafOfModules pushforwardComp,
  pullbackComp, pushforwardCongr and natural-isomorphism lemmas; none states
  the specified unbounded coefficient normalization.
- msearch loogle: `SheafOfModules.pullbackComp`. Five hits, ordinary pullbackComp,
  left/right identity, associativity, conjugateEquiv_pullbackComp_inv; no match.
- msearch grep: `pullbackComp|pushforwardComp` in
  Algebra/Category/ModuleCat/Sheaf. Ten hits in PullbackContinuous and
  PushforwardContinuous, ordinary path comparisons only. Read the signatures.
- msearch leansearch: “The derived restriction of scalars pushforward comparison
  of a coefficient ringed square is the inverse canonical ringed topos path
  comparison”. Eight hits about ordinary restriction and presheaf pushforward;
  no match.
- rg of `coefficientRinged|coefficient_ringed|ringedComparisonTensorAdjunction|
  ringed.square.normalization` in lean/Sheaf and lean/WeilConjectures, followed
  by broader coefficient/ringed/path patterns: no existing normalization.
- Exact blueprint-id search in lean/WeilConjectures: no hits.

Validation: scompile.py passed the final file cleanly under both its private
sandbox name (30.7 seconds) and its actual library module name (32.5 seconds),
within the unchanged 60-second limit. No warnings remained. The node copy
changes only lean; its signature is copied verbatim from the theorem, and the
four canonical helper definitions are recorded in lean.declarations.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
