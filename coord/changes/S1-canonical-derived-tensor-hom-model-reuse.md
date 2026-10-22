# Canonical derived tensor-Hom model: reuse identical adopted definitions

## Reason

The duplicate Sheaf model exceeds 60 seconds during checking of its existing data definitions.
Its six public definitions already exist in the adopted source module. A declaration-by-declaration
comparison confirms identical signatures and bodies after replacing the legacy predicate spelling
`IsAcyclicTensorKFlat` by the definitionally equal `IsKFlatTensor`. Use that canonical module through
the original Sheaf import path instead of rechecking duplicate constructions. Preserve the public
Sheaf pullback-comparison import, which also preserves the legacy K-flat API. No adopted source
file is edited, no data is chosen anew, and no mathematical definition or target meaning changes.
Both canonical predicates retain exactly their naturality and representative equations.

The six declarations are `AlgebraicGeometry.schemeHomKInjectiveResolution`,
`AlgebraicGeometry.schemeHomResolutionInverse`,
`AlgebraicGeometry.schemeDerivedInternalHomResolutionIso`,
`AlgebraicGeometry.schemeTensorHomUncurryComponent`,
`AlgebraicGeometry.IsCanonicalDerivedTensorHom`, and
`AlgebraicGeometry.IsCanonicalDerivedTensorHomMap`. The first four signatures and bodies are
textually identical after whitespace normalization; the last two differ only by that predicate
spelling. This fixes the duplicate data-definition compilation cost without splitting the file.

## Old

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Canonical derived tensor/internal-Hom bijections
Source: Stacks Project, cohomology.tex, Tag 08DJ (lemma-internal-hom).
(blueprint: def-pc-canonical-derived-tensor-hom-bijection).
The representative equation uses the actual Hom-complex projections, sheaf tensor-Hom
currying, the localization factorization, and the functorial K-injective resolution.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe uCD wCD
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- The functorial resolution already used by derived internal Hom, with the scheme's
Grothendieck instance supplied explicitly.
Source: Stacks, cohomology.tex, 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection). -/
def schemeHomKInjectiveResolution (X : Scheme.{uCD}) :
    CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ ⥤
      CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ :=
  haveI := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  CochainComplex.kInjectiveResolutionFunctor.{uCD} _

/-- Inverse of the localized quasi-isomorphism into the fixed resolution.
Source: Stacks, cohomology.tex, 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection). -/
def schemeHomResolutionInverse (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    (M : CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ) :
    DerivedCategory.Q.obj ((schemeHomKInjectiveResolution X).obj M) ⟶
      DerivedCategory.Q.obj M := by
  haveI := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  haveI := (DerivedCategory.isIso_Q_map_iff_quasiIso _
    ((CochainComplex.toKInjectiveResolution.{uCD}
      (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))).app M)).2
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{uCD}
        (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) M).2
  exact inv (DerivedCategory.Q.map
    ((CochainComplex.toKInjectiveResolution.{uCD} _).app M))

/-- The localization factorization for the fixed functorial K-injective model.
Source: Stacks, cohomology.tex, 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection). -/
def schemeDerivedInternalHomResolutionIso (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    (L M : CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ) :
    (derivedInternalHom (Opens.grothendieckTopology X) X.sheaf).obj
        (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj (homComplex (R := X.sheaf) L
        ((schemeHomKInjectiveResolution X).obj M)) := by
  haveI : IsGrothendieckAbelian.{uCD}
      (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian _
  exact (Localization.fac
    ((𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{uCD}
      (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))) ⋙
      Functor.uncurry.obj (homComplexFunctor (R := X.sheaf)) ⋙ DerivedCategory.Q)
    (derivedInternalHom_inverts (Opens.grothendieckTopology X) X.sheaf
      (CochainComplex.kInjectiveResolutionFunctor.{uCD}
        (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)))
      (CochainComplex.toKInjectiveResolution.{uCD} _)
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{uCD} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{uCD} _ M⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)).app (op L, M)

/-- The uncurried component of a map into the fixed Hom complex.
Source: Stacks Project, cohomology.tex, Tag 08DJ, componentwise evaluation.
(blueprint: def-pc-canonical-derived-tensor-hom-bijection). -/
def schemeTensorHomUncurryComponent (X : Scheme.{uCD})
    (P L M : CochainComplex (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M))
    (p q n : ℤ) (h' : q + p = n) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    P.X p ⊗ L.X q ⟶ ((schemeHomKInjectiveResolution X).obj M).X n :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.symmetricCategory X.sheaf
  (β_ (P.X p) (L.X q)).hom ≫
    (SheafOfModules.tensorHomEquiv (L.X q) (P.X p)
      (((schemeHomKInjectiveResolution X).obj M).X n)).symm
      (φ.f p ≫ (Classical.choose (Classical.choose_spec
        (homComplex_exists (R := X.sheaf)))) L
          ((schemeHomKInjectiveResolution X).obj M) p q n h')

/-- Naturality and the actual representative evaluation equation characterize the family.
The chain map ψ is fixed on every total-tensor summand by currying the degree-p
component of φ, projected to Hom(L^q,I(M)^(q+p)). The symmetry restores the order
P^p tensor L^q. The localization factorization and resolution map fix both targets.
Source: Stacks, cohomology.tex, Tag 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-bijection). -/
def IsCanonicalDerivedTensorHom (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    (e : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) ≃ (K ⊗ L ⟶ M)) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := schemeDerivedTensorMonoidal X
  letI := SheafOfModules.symmetricCategory X.sheaf
  (∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
    e K' L' M' (a ≫ f ≫
      (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).map (b.op, c)) =
      (a ⊗ₘ b) ≫ e K L M f ≫ c) ∧
  (∀ (P L M : CochainComplex
      (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ),
    P.IsAcyclicTensorKFlat →
    ∀ φ : P ⟶ homComplex (R := X.sheaf) L
        ((schemeHomKInjectiveResolution X).obj M),
      ∃ ψ : pullbackTensorTotal X P L ⟶
          (schemeHomKInjectiveResolution X).obj M,
        (∀ (p q n : ℤ) (h : p + q = n) (h' : q + p = n),
          HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ) p q n h ≫
            ψ.f n =
          schemeTensorHomUncurryComponent X P L M φ p q n h') ∧
        e (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
            (DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso X L M).inv) =
          pullbackTensorModelMap X P L ≫ DerivedCategory.Q.map ψ ≫
            schemeHomResolutionInverse X M)

/-- Naturality and the actual representative evaluation equation characterize the family.
The chain map ψ is fixed on every total-tensor summand by currying the degree-p
component of φ, projected to Hom(L^q,I(M)^(q+p)). The symmetry restores the order
P^p tensor L^q. The localization factorization and resolution map fix both targets.
Source: Stacks, cohomology.tex, Tag 08DJ
(blueprint: def-pc-canonical-derived-tensor-hom-model). -/
def IsCanonicalDerivedTensorHomMap (X : Scheme.{uCD})
    [HasDerivedCategory.{wCD} (SheafOfModules.{uCD} (moduleRings X.toRingedSpace))]
    (e : ∀ K L M : schemeDerivedCategory X,
      (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)) → (K ⊗ L ⟶ M)) : Prop :=
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := schemeDerivedTensorMonoidal X
  letI := SheafOfModules.symmetricCategory X.sheaf
  (∀ (K K' L L' M M' : schemeDerivedCategory X)
      (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
      (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op L, M)),
    e K' L' M' (a ≫ f ≫
      (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).map (b.op, c)) =
      (a ⊗ₘ b) ≫ e K L M f ≫ c) ∧
  (∀ (P L M : CochainComplex
      (SheafOfModules.{uCD} (moduleRings X.toRingedSpace)) ℤ),
    P.IsAcyclicTensorKFlat →
    ∀ φ : P ⟶ homComplex (R := X.sheaf) L
        ((schemeHomKInjectiveResolution X).obj M),
      ∃ ψ : pullbackTensorTotal X P L ⟶
          (schemeHomKInjectiveResolution X).obj M,
        (∀ (p q n : ℤ) (h : p + q = n) (h' : q + p = n),
          HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ) p q n h ≫
            ψ.f n =
          schemeTensorHomUncurryComponent X P L M φ p q n h') ∧
        e (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)
            (DerivedCategory.Q.map φ ≫ (schemeDerivedInternalHomResolutionIso X L M).inv) =
          pullbackTensorModelMap X P L ≫ DerivedCategory.Q.map ψ ≫
            schemeHomResolutionInverse X M)


end AlgebraicGeometry
```

## New

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomModel
public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison

/-! # Canonical derived tensor/internal-Hom bijections
Source: Stacks Project, cohomology.tex, Tag 08DJ (lemma-internal-hom).
(blueprint: def-pc-canonical-derived-tensor-hom-bijection).
The representative equation uses the actual Hom-complex projections, sheaf tensor-Hom
currying, the localization factorization, and the functorial K-injective resolution.
-/

@[expose] public section
```

The re-exported definitions are the unchanged declarations in
`WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomModel`. The former direct public
imports of derived internal Hom and monoidal closure remain publicly available through it.

## Users

Source audit: `tools/downstream.py ... --uses` for all six names, supplemented by whole-name
searches of live and quarantined project sources. Every source user is listed below. Their
applications retain the same terms and definitionally equal types; none needs adaptation.
All six names remain publicly available from the same Sheaf module. Archived users and their
DAG attachments remain preserved for their separate rework assignments.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomMapBijective | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomModel | unclaimed | Re-export the unchanged adopted definitions; preserve original import path and legacy K-flat API. |
| Sheaf.AlgebraicGeometry.DerivedPullbackEvaluationSections | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed; quarantined | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.AffineGlobalHomBaseChangeMap | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomMapBijective | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomMapExistence | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomModel | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomEvaluationNaturality | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomEvaluationPostcomposition | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomEvaluationPrecomposition | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomIdentityEvaluationCoherence | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryComponentNaturality | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescent | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentExtension | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentNaturality | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryLocalizedEvaluation | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.DerivedPullbackEvaluationSections | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.DerivedRestrictionTensorHomCoherence | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.DerivedTensorHomSectionsUnit | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.MixedPerfectInternalHomPullbackIsIso | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.NormalizedInternalHomPullbackComparison | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.OpenRestrictionClosedMonoidal | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.OpenRestrictionEvaluationMateIsIso | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.PerfectRHomEvaluationIsomorphisms | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationChainAction | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationChainMapExists | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationGradedAugmentation | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationUncurryCalculation | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |
| WeilConjectures.AlgebraicGeometry.SchemeTensorHomUncurrySummandNaturality | unclaimed | Same canonical declarations, constructions and definitionally equal types; source unchanged by this model repair. |

The accompanying node `def-pc-canonical-derived-tensor-hom-model` points to
`WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHomModel`, with
`existing: true` and its declaration signature copied verbatim. The semantic
statement, dependencies and other node fields are unchanged.

## Status

landed 20261022T025340-L-1290470 2026-10-22 (merge of deliver/S1/Sheaf.Algebra.Homology.KFlatResolution)
