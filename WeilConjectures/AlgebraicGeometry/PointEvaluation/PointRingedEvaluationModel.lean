/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointEvaluation.PointEvaluationTensorData
public import WeilConjectures.AlgebraicGeometry.PointEvaluation.PointEvaluationTensorCoherence
public import WeilConjectures.AlgebraicGeometry.PointEvaluation.PointEvaluationScalarTensor
public import WeilConjectures.AlgebraicGeometry.PointEvaluation.PointEvaluationScalarCoherence
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
public import WeilConjectures.SmoothPurity.PointSectionsPoint.PointIntegralSectionsPoint
public import WeilConjectures.SmoothPurity.RingedSitePointTensor
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.FinitePresentation
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Connected.Separation
public import WeilConjectures.Mathlib.RingTheory.Etale.Field
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.RingTheory.ProEtale.PullbackProfinite
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.WeakDimension
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.ProperBaseChange.GeometricFieldProfiniteDenseSubsite
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointDiscreteConstantComparison
public import WeilConjectures.AlgebraicGeometry.GeometricStalkToposPoint
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapComparison
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.CategoryTheory.Sites.UnitHomEval
public import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSite
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
public import WeilConjectures.CategoryTheory.ZetaWeil.SectionRingGlobalSections
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint

/-!
# Ringed geometric-point evaluation model

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-p-proper/sk-thm-sf-kunneth-relative/
thm-sf-kunneth-relative.md`, proof step 5; Stacks Project Tags 0991, 03EL and 07A4
(blueprint: lem-sf-point-ringed-evaluation-model)

This module records the complete ringed point package: the geometric-stalk point,
exact module sections, normalized signed tensor maps, their localization and scalar
compatibilities, and the condensed singleton specialization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.PointEvaluation
open CategoryTheory.CochainPullback

namespace AlgebraicGeometry.ProEtale.PointEvaluation

variable {k : Type u} [Field k]

/-- The ringed-site module category for a coefficient sheaf.
Source: Stacks Tags 03EL and 07A4 (blueprint: lem-sf-point-ringed-evaluation-model). -/
abbrev siteModules (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1}
    ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)

/-- Termwise point sections of a cochain complex.
Source: Stacks Tag 07A4 (blueprint: lem-sf-point-ringed-evaluation-model). -/
abbrev sectionComplex (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}) :=
  (pointModuleSections k B).mapHomologicalComplex (.up ℤ)

/-- The geometric stalk is identified with sections at the point, with restriction
maps fixed by the pointed lifts.
Source: Stacks Tag 0991 (blueprint: lem-sf-point-ringed-evaluation-model). -/
structure StalkEvaluation (k : Type u) [Field k] [IsAlgClosed k]
    (F : Sheaf (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1))) where
  iso : proEtaleGeometricSetStalk (𝟙 (Spec (.of k))) F ≃
    F.obj.obj (op (finalObject k))
  /-- The pointed lift is used as an actual pro-etale arrow in the restriction map. -/
  pointedLift : ∀ (U : Scheme.ProEt (Spec (.of k)))
    (x : Over.mk (𝟙 (Spec (.of k))) ⟶ (ProEt.forget (Spec (.of k))).obj U),
    finalObject k ⟶ U
  /-- The underlying scheme map of the chosen site arrow is the displayed pointed lift. -/
  pointedLift_underlying : ∀ (U : Scheme.ProEt (Spec (.of k)))
    (x : Over.mk (𝟙 (Spec (.of k))) ⟶ (ProEt.forget (Spec (.of k))).obj U),
    (pointedLift U x).left = x.left
  restrictionMap : ∀ (U : Scheme.ProEt (Spec (.of k)))
    (x : Over.mk (𝟙 (Spec (.of k))) ⟶ (ProEt.forget (Spec (.of k))).obj U),
    F.obj.obj (op U) → F.obj.obj (op (finalObject k))
  /-- Restriction is the presheaf map along the pointed site arrow, not a free map. -/
  restrictionMap_eq : ∀ (U : Scheme.ProEt (Spec (.of k)))
    (x : Over.mk (𝟙 (Spec (.of k))) ⟶ (ProEt.forget (Spec (.of k))).obj U),
    restrictionMap U x = F.obj.map (pointedLift U x).op
  restriction : ∀ (U : Scheme.ProEt (Spec (.of k)))
    (x : Over.mk (𝟙 (Spec (.of k))) ⟶ (ProEt.forget (Spec (.of k))).obj U)
    (s : F.obj.obj (op U)),
    iso (colimit.ι (proEtaleGeometricStalkDiagram (𝟙 (Spec (.of k))) F)
      (op (StructuredArrow.mk x)) s) = restrictionMap U x s

/-- The derived category of modules over the final section ring.
Source: Stacks Tag 07A4 (blueprint: lem-sf-point-ringed-evaluation-model). -/
abbrev pointSectionDerived (k : Type u) [Field k]
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}) :=
  DerivedCategory (ModuleCat.{u + 1} (sectionRing k B))

/-- The chain-level total tensor functor on point modules.
Source: Stacks Tags 03EL and 07A4 (blueprint: lem-sf-point-ringed-evaluation-model). -/
abbrev pointModuleTotal
    (k : Type u) [Field k]
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}) :=
  Functor.uncurry.obj
    ((curriedTensor (ModuleCat.{u + 1} (sectionRing k B))).map₂CochainComplex)

/-- The left-derived functor of exact point sections.
Source: Stacks Tag 07A4 (blueprint: lem-sf-point-ringed-evaluation-model). -/
abbrev pointDerivedSections
    (k : Type u) [Field k]
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
    [HasDerivedCategory.{u + 2} (ModuleSheaves B)]
    [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B))]
    [(pointModuleSections k B).Additive]
    [PreservesFiniteLimits (pointModuleSections k B)]
    [PreservesFiniteColimits (pointModuleSections k B)] :=
  Functor.mapDerivedCategory.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
    (C₁ := ModuleSheaves B) (C₂ := ModuleCat.{u + 1} (sectionRing k B))
    (pointModuleSections k B)

/-- The factor natural transformation for derived point sections.
Source: Stacks Tag 07A4 (blueprint: lem-sf-point-ringed-evaluation-model). -/
abbrev pointDerivedSectionsFactors
    (k : Type u) [Field k]
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
    [HasDerivedCategory.{u + 2} (ModuleSheaves B)]
    [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B))]
    [(pointModuleSections k B).Additive]
    [PreservesFiniteLimits (pointModuleSections k B)]
    [PreservesFiniteColimits (pointModuleSections k B)] :=
  Functor.mapDerivedCategoryFactors.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
    (C₁ := ModuleSheaves B) (C₂ := ModuleCat.{u + 1} (sectionRing k B))
    (pointModuleSections k B)

/-- The exact derived-section universal property and its normalized tensor comparison.
The representative square is the one supplied by the published canonical ringed-topos
pullback theorem, with the point's `T.b` as its component.
Source: the derived pullback step of `lem-sf-point-ringed-evaluation-model` in the
current blueprint. -/
def DerivedCompatible
    (k : Type u) [Field k] [IsAlgClosed k]
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
    (T : TensorModel B)
    [HasDerivedCategory.{u + 2} (ModuleSheaves B)]
    [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B))]
    [(pointModuleSections k B).Additive]
    [PreservesFiniteLimits (pointModuleSections k B)]
    [PreservesFiniteColimits (pointModuleSections k B)] : Prop :=
  (∀ (L : DerivedCategory (ModuleSheaves B) ⥤
        DerivedCategory (ModuleCat.{u + 1} (sectionRing k B)))
    (e : DerivedCategory.Q (C := ModuleSheaves B) ⋙ L ⟶ complexSections k B ⋙
      DerivedCategory.Q (C := ModuleCat.{u + 1} (sectionRing k B))),
    L.IsLeftDerivedFunctor e (HomologicalComplex.quasiIso (ModuleSheaves B) (.up ℤ)) →
    ∃ η : L ≅ (pointDerivedSections k B),
      e = Functor.whiskerLeft DerivedCategory.Q η.hom ≫
        (pointDerivedSectionsFactors k B).hom) ∧
  (∀ (S : DerivedCategory (ModuleSheaves B) × DerivedCategory (ModuleSheaves B) ⥤
      DerivedCategory (ModuleSheaves B))
    (rS : ((resolving B).ι.prod (resolving B).ι) ⋙
      SheafOfModules.KFlatTotalTensorModel.total B ⋙ DerivedCategory.Q ≅
      (((resolving B).ι ⋙ DerivedCategory.Q).prod
        ((resolving B).ι ⋙ DerivedCategory.Q)) ⋙ S)
    (U : DerivedCategory (ModuleCat.{u + 1} (sectionRing k B)) ×
      DerivedCategory (ModuleCat.{u + 1} (sectionRing k B)) ⥤
        DerivedCategory (ModuleCat.{u + 1} (sectionRing k B)))
    (r : ((moduleResolving B).ι.prod (moduleResolving B).ι) ⋙ pointModuleTotal k B ⋙
      DerivedCategory.Q ≅
      (((moduleResolving B).ι ⋙ DerivedCategory.Q).prod
        ((moduleResolving B).ι ⋙ DerivedCategory.Q)) ⋙ U),
    ∃! α : S ⋙ (pointDerivedSections k B) ≅
        ((pointDerivedSections k B).prod
          (pointDerivedSections k B)) ⋙ U,
      ∀ (P Q : Complexes B) (hP : resolving B P) (hQ : resolving B Q),
        (pointDerivedSections k B).map
            (rS.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)) ≫
          α.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          U.map (Prod.mkHom
            ((pointDerivedSectionsFactors k B).hom.app P)
            ((pointDerivedSectionsFactors k B).hom.app Q)) =
        (pointDerivedSectionsFactors k B).hom.app (totalObj B P Q) ≫
          DerivedCategory.Q.map (T.b P Q).hom ≫
          r.hom.app (⟨(complexSections k B).obj P, T.preserves_resolving P hP⟩,
            ⟨(complexSections k B).obj Q, T.preserves_resolving Q hQ⟩))

/-- The canonical derived scalar comparison, uniquely fixed by the balanced chain map.
The equation is on every resolving representative and therefore descends to all derived
objects; it is the derived version of the scalar square in `ScalarModel`.
Source: the derived scalar step of `lem-sf-point-ringed-evaluation-model` in the
current blueprint. -/
def ScalarDerivedCompatible
    (k : Type u) [Field k]
    {B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}}
    {B' : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}}
    (a : B ⟶ B') (T : TensorModel B) (T' : TensorModel B') (S : ScalarModel a T T')
    [HasDerivedCategory.{u + 2} (ModuleSheaves B)]
    [HasDerivedCategory.{u + 2} (ModuleSheaves B')]
    [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B))]
    [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B'))]
    [(pointModuleSections k B).Additive] [(pointModuleSections k B').Additive]
    [PreservesFiniteLimits (pointModuleSections k B)]
    [PreservesFiniteColimits (pointModuleSections k B)]
    [PreservesFiniteLimits (pointModuleSections k B')]
    [PreservesFiniteColimits (pointModuleSections k B')] : Prop :=
  ∀ (LS : DerivedCategory (ModuleSheaves B) ⥤ DerivedCategory (ModuleSheaves B'))
    (LM : DerivedCategory (ModuleCat.{u + 1} (sectionRing k B)) ⥤
      DerivedCategory (ModuleCat.{u + 1} (sectionRing k B')))
    (eS : (resolving B).ι ⋙ DerivedCategory.Q ⋙ LS ≅
      (resolving B).ι ⋙ extend.{u + 1, u + 1, u} a ⋙ DerivedCategory.Q)
    (eM : (moduleResolving B).ι ⋙ DerivedCategory.Q ⋙ LM ≅
      (moduleResolving B).ι ⋙ moduleExtend B a ⋙ DerivedCategory.Q),
    ∃! δ : LS ⋙ pointDerivedSections k B' ≅ pointDerivedSections k B ⋙ LM,
      ∀ (P : Complexes B) (hP : resolving B P),
        (pointDerivedSections k B').map (eS.hom.app ⟨P, hP⟩) ≫
            (pointDerivedSectionsFactors k B').hom.app ((extend a).obj P) ≫
            DerivedCategory.Q.map (S.κ.hom.app P) =
          δ.hom.app (DerivedCategory.Q.obj P) ≫
            LM.map ((pointDerivedSectionsFactors k B).hom.app P) ≫
            eM.hom.app ⟨(complexSections k B).obj P,
              T.preserves_resolving P hP⟩

/-- The canonical derived comparison package at the ringed geometric point.
Source: the canonical point pullback step of `lem-sf-point-ringed-evaluation-model` in
the current blueprint. -/
structure CanonicalDerivedPointComparison (k : Type u) [Field k] [IsAlgClosed k]
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
    (T : TensorModel B)
    [hasDerivedSheaves : HasDerivedCategory.{u + 2} (ModuleSheaves B)]
    [hasDerivedSections : HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B))]
    [sectionsAdditive : (pointModuleSections k B).Additive]
    [sectionsLimits : PreservesFiniteLimits (pointModuleSections k B)]
    [sectionsColimits : PreservesFiniteColimits (pointModuleSections k B)] where
  /-- The actual ringed point has the displayed module inverse image. -/
  point_module_pullback :
    (WeilConjectures.PointSectionsPoint.ringed k B).modules =
      pointModuleSections k B
  /-- The universal left-derived section and canonical two-variable tensor comparison
  supplied by `ringedTopoiCanonicalDerivedTensorPullback` at the point. -/
  canonical_ringed_topos_derived_pullback : DerivedCompatible k B T
/-- A bundled condensed ring exposes its underlying monoid object to the section-ring APIs.
Source: HRS Definition 3.5 (blueprint: lem-sf-point-ringed-evaluation-model). -/
noncomputable instance condensedRing_underlying_monObj
    (Λ : Profinite.CondensedRing.{u}) : MonObj Λ.X := Λ.mon

/-- The underlying coefficient ring object carries the monoid structure transported by
`upperStarFromPoint`; the published Basic module exposes its commutativity separately.
Source: HRS Definition 3.5 (blueprint: lem-sf-point-ringed-evaluation-model). -/
noncomputable instance condensedRingObj_monObj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) : MonObj (condensedRingObj Λ X) := by
  let M := (upperStarFromPoint X).mapMon.obj (Mon.mk Λ)
  exact M.mon

/-- The CommRing-valued coefficient sheaf obtained from the internal ring object
`Λ_s = p_s^*Λ`; its final section ring is the ring used by the point package.
Source: HRS Definition 3.5 (blueprint: lem-sf-point-ringed-evaluation-model). -/
abbrev condensedPointCoefficientSheaf (k : Type u) [Field k]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] :
    Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1} :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology (Spec (.of k)))
    (condensedRingObj Λ.X (Spec (.of k)))

/-- The canonical comparison between the point section ring and the condensed singleton
ring is built from the global-section map of the actual inverse-image functor. In
particular it does not choose an isomorphism from a mere `Nonempty` comparison.
Source: coefficient identification at the singleton (blueprint: lem-sf-point-ringed-evaluation-model). -/
noncomputable def canonicalCondensedScalarRingIso (k : Type u) [Field k] [IsAlgClosed k]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] :
    (condensedPointCoefficientSheaf k Λ).obj.obj (op (finalObject k)) ≃+*
      condensedScalarRing Λ.X := by
  letI : IsSepClosed k := IsSepClosed.of_isAlgClosed k
  let F := upperStarFromPoint (Spec (.of k))
  letI : F.IsEquivalence :=
    AlgebraicGeometry.ProEtale.isEquivalence_upperStarFromPoint (Ω := k)
  letI : F.Additive := Functor.additive_of_preserves_binary_products F
  let eF : MonObj.Γ Λ.X ≃+* MonObj.Γ (F.obj Λ.X) :=
    RingEquiv.ofBijective (MonObj.Γ.mapFunctor F (R := Λ.X))
      (InternalAbelianSheafModule.globalMapFunctor_bijective F
        (Functor.FullyFaithful.ofFullyFaithful
          (upperStarFromPoint (Spec (.of k)))) Λ.X)
  let e₀ := InternalAbelianSheafModule.sectionGlobalEquiv
    (coherentTopology Profinite.{u}) Λ.X (⊤_ Profinite.{u}) terminalIsTerminal
  let e₁ := InternalAbelianSheafModule.sectionGlobalEquiv
    (Scheme.ProEt.topology (Spec (.of k)))
    (condensedRingObj Λ.X (Spec (.of k))) (finalObject k)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale
      (Spec (.of k)))
  exact (e₀.symm.trans (eF.trans e₁)).symm

/-- The coefficient maps used by the naturality square are the maps of the actual
section-ring sheaves, evaluated at the indicated terminal objects.
Source: coefficient identification at the singleton (blueprint: lem-sf-point-ringed-evaluation-model). -/
noncomputable def canonicalCondensedPointSectionMap (k : Type u) [Field k]
    (Λ Λ' : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] [IsCommMonObj Λ'.X]
    (f : Λ ⟶ Λ') :
    (condensedPointCoefficientSheaf k Λ).obj.obj (op (finalObject k)) →+*
      (condensedPointCoefficientSheaf k Λ').obj.obj (op (finalObject k)) :=
  let m : condensedRingObj Λ.X (Spec (.of k)) ⟶
      condensedRingObj Λ'.X (Spec (.of k)) :=
    ((upperStarFromPoint (Spec (.of k))).mapMon.map f).hom
  ((InternalAbelianSheafModule.sectionScalarMap
    (Scheme.ProEt.topology (Spec (.of k)))
    m).hom.app
      (op (finalObject k))).hom

/-- The induced map on condensed singleton section rings.
Source: coefficient identification at the singleton (blueprint: lem-sf-point-ringed-evaluation-model). -/
noncomputable def canonicalCondensedScalarMap (Λ Λ' : Profinite.CondensedRing.{u})
    [IsCommMonObj Λ.X] [IsCommMonObj Λ'.X] (f : Λ ⟶ Λ') :
    condensedScalarRing Λ.X →+* condensedScalarRing Λ'.X :=
  ((InternalAbelianSheafModule.sectionScalarMap
    (coherentTopology Profinite.{u}) f.hom).hom.app
      (op (⊤_ Profinite.{u}))).hom

/-- Evaluation of the singleton section ring of the continuous-map coefficient at the
unique point of `⊤_ Profinite`. The equivalence is assembled from the published
constant-map global sections and the terminal section-ring comparison.
Source: the discrete constant-sheaf comparison in the condensed point coefficients
construction (blueprint: lem-sf-point-ringed-evaluation-model). -/
noncomputable def canonicalSingletonEvaluation (k : Type u) [Field k] [IsAlgClosed k]
    (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T] :
    condensedScalarRing (Profinite.continuousMapRingObj.{u} T) ≃+* T := by
  let hG : T ≃+* MonObj.Γ (Profinite.continuousMapRingObj.{u} T) :=
    RingEquiv.ofBijective (Profinite.continuousMapConstRingHom T) <| by
      apply Sheaf.ringHomΓSheafCompose_bijective
        (J := coherentTopology Profinite.{u})
        (S := Profinite.continuousMapRingSheaf.{u} T)
        (T := Profinite.of PUnit.{u + 1}) Profinite.isTerminalPUnit
        (Profinite.continuousMapConstSectionRingHom T) (fun _ _ ↦ rfl)
      constructor
      · intro x y h
        have h' := congrArg ULift.down h
        change ContinuousMap.const PUnit.{u + 1} x = ContinuousMap.const PUnit.{u + 1} y at h'
        simpa only [ContinuousMap.const_apply] using
          congrArg (fun f : C(PUnit.{u + 1}, T) => f PUnit.unit) h'
      · intro f
        refine ⟨f.down PUnit.unit, ?_⟩
        apply ULift.ext
        apply ContinuousMap.ext
        intro z
        change (ContinuousMap.const PUnit.{u + 1} (f.down PUnit.unit)) z = f.down z
        rw [ContinuousMap.const_apply]
  let hS : MonObj.Γ (Profinite.continuousMapRingObj.{u} T) ≃+*
      condensedScalarRing (Profinite.continuousMapRingObj.{u} T) :=
    InternalAbelianSheafModule.sectionGlobalEquiv
      (coherentTopology Profinite.{u}) (Profinite.continuousMapRingObj.{u} T)
      (⊤_ Profinite.{u}) terminalIsTerminal
  exact hS.symm.trans hG.symm

/-- The inverse of the published continuous-map comparison at the pro-etale point.
Source: the point coefficient comparison in `lem-sf-point-ringed-evaluation-model` in
the current blueprint. -/
noncomputable def canonicalPointComparison (k : Type u) [Field k] [IsAlgClosed k]
    (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [DiscreteTopology T] :
    (sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      (continuousMapRingSheaf (Spec (.of k)) T) |>.obj.obj (op (finalObject k)) →
      (condensedPointCoefficientSheaf k
        (Mon.mk (Profinite.continuousMapRingObj.{u} T))).obj.obj (op (finalObject k)) := by
  letI : IsIso (continuousMapComparison (Spec (.of k)) T) :=
    isIso_continuousMapComparison (Spec (.of k)) T
  exact fun x ↦ inv ((continuousMapComparison (Spec (.of k)) T).hom.app
    (op (finalObject k))) x

/-- The coefficient and scalar evaluations required at a geometric point.
Source: the condensed coefficient clause of `lem-sf-point-ringed-evaluation-model` in
the current blueprint. -/
structure CondensedPointEvaluation (k : Type u) [Field k] [IsAlgClosed k]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] where
  section_iso : MonObj.Γ (condensedRingObj Λ.X (Spec (.of k))) ≃+*
      (condensedPointCoefficientSheaf k Λ).obj.obj (op (finalObject k))
  section_iso_eq : section_iso =
      InternalAbelianSheafModule.sectionGlobalEquiv
        (Scheme.ProEt.topology (Spec (.of k)))
        (condensedRingObj Λ.X (Spec (.of k))) (finalObject k)
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale
          (Spec (.of k)))
  /-- The canonical singleton ring isomorphism is the explicit global-section comparison. -/
  canonical_scalar_ring :
    (condensedPointCoefficientSheaf k Λ).obj.obj (op (finalObject k)) ≃+*
      condensedScalarRing Λ.X
  canonical_scalar_ring_eq :
    canonical_scalar_ring = canonicalCondensedScalarRingIso k Λ
  /-- The maps induced by a coefficient morphism on point sections and singleton values. -/
  canonical_scalar_map : ∀ (Λ' : Profinite.CondensedRing.{u})
      [IsCommMonObj Λ'.X] (f : Λ ⟶ Λ'),
      (condensedPointCoefficientSheaf k Λ).obj.obj (op (finalObject k)) →+*
        (condensedPointCoefficientSheaf k Λ').obj.obj (op (finalObject k))
  canonical_scalar_map_eq : ∀ (Λ' : Profinite.CondensedRing.{u})
      [IsCommMonObj Λ'.X] (f : Λ ⟶ Λ'),
      canonical_scalar_map Λ' f = canonicalCondensedPointSectionMap k Λ Λ' f
  canonical_singleton_map : ∀ (Λ' : Profinite.CondensedRing.{u})
      [IsCommMonObj Λ'.X] (f : Λ ⟶ Λ'),
      condensedScalarRing Λ.X →+* condensedScalarRing Λ'.X
  canonical_singleton_map_eq : ∀ (Λ' : Profinite.CondensedRing.{u})
      [IsCommMonObj Λ'.X] (f : Λ ⟶ Λ'),
      canonical_singleton_map Λ' f = canonicalCondensedScalarMap Λ Λ' f
  /-- Naturality of the canonical family with the maps induced by `f`. -/
  canonical_scalar_ring_natural : ∀ (Λ' : Profinite.CondensedRing.{u})
      [IsCommMonObj Λ'.X] (f : Λ ⟶ Λ') (x :
        (condensedPointCoefficientSheaf k Λ).obj.obj (op (finalObject k))),
    canonicalCondensedScalarRingIso k Λ'
        (canonical_scalar_map Λ' f x) =
      canonical_singleton_map Λ' f (canonical_scalar_ring x)
  /-- Evaluation on a continuous coefficient is transported from singleton functions. -/
  continuous_evaluation : ∀ (T : Type u) [TopologicalSpace T] [CommRing T]
      [IsTopologicalRing T],
      ∃ e : (Profinite.continuousMapRingSheafOfUniverse.{u, u} T).obj.obj
          (op (⊤_ Profinite.{u})) ≃+* T,
        (∀ f, e f = f.down
          ((terminalIsTerminal.from (Profinite.of PUnit.{u + 1})) PUnit.unit)) ∧
        (∀ t : T, e.symm t = ULift.up
          (ContinuousMap.const (⊤_ Profinite.{u}) t))
  /-- The pulled-back point ring is evaluated by the same singleton map, with constant inverse. -/
  continuous_point_evaluation : ∀ (T : Type u) [TopologicalSpace T] [CommRing T]
      [IsTopologicalRing T],
    ∃ e₀ : (Profinite.continuousMapRingSheafOfUniverse.{u, u} T).obj.obj
          (op (⊤_ Profinite.{u})) ≃+* T,
      (∀ f, e₀ f = f.down
          ((terminalIsTerminal.from (Profinite.of PUnit.{u + 1})) PUnit.unit)) ∧
      (∀ t : T,
        (canonicalCondensedScalarRingIso k
          (Mon.mk (Profinite.continuousCoefficientRingObj T))).symm (e₀.symm t) =
          (canonicalCondensedScalarRingIso k
            (Mon.mk (Profinite.continuousCoefficientRingObj T))).symm
            (ULift.up (ContinuousMap.const (⊤_ Profinite.{u}) t)))
  /-- For a discrete coefficient, the constant section is sent through the published
  constant-sheaf comparison, the canonical point comparison, the canonical singleton
  ring isomorphism, and evaluation at the point. -/
  discrete_constant : ∀ (T : Type) [TopologicalSpace T] [CommRing T]
      [IsTopologicalRing T] [DiscreteTopology T],
      ∀ t : T,
      (canonicalSingletonEvaluation k T)
        ((canonicalCondensedScalarRingIso k
          (Mon.mk (Profinite.continuousMapRingObj.{u} T)))
          (canonicalPointComparison k T
            (((constantSheafIsoContinuousMapRingSheaf (Spec (.of k)) T).hom.hom.app
              (op (finalObject k)))
            (((constantSheafAdj (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1}
              (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale
                (Spec (.of k)))).unit.app (AddCommGrpCat.of (ULift.{u + 1} T))).hom
              (ULift.up t))))) = t

/-- Identity and composition laws for the actual scalar maps and their squares.
Source: Stacks Tags 03EL and 07A4 (blueprint: lem-sf-point-ringed-evaluation-model). -/

structure ScalarFunctoriality (k : Type u) [Field k]
    (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
    (T : TensorModel B) where
  identity_map : scalarMap B (𝟙 B) = RingHom.id _
  composition_map : ∀ (B' B'' : Sheaf (Scheme.ProEt.topology (Spec (.of k)))
      CommRingCat.{u + 1}) (a : B ⟶ B') (a' : B' ⟶ B''),
    scalarMap B (a ≫ a') = (scalarMap B' a').comp (scalarMap B a)
  identity_square : ∃ S : ScalarModel (𝟙 B) T T,
    ScalarCoherent (𝟙 B) T T S
  identity_square_unique : ∀ (S S' : ScalarModel (𝟙 B) T T),
    ScalarCoherent (𝟙 B) T T S → ScalarCoherent (𝟙 B) T T S' →
      S.κ.hom = S'.κ.hom
  composition_square : ∀ (B' B'' : Sheaf (Scheme.ProEt.topology (Spec (.of k)))
      CommRingCat.{u + 1}) (T' : TensorModel B') (T'' : TensorModel B'')
      (a : B ⟶ B') (a' : B' ⟶ B''),
    ∃ S : ScalarModel (a ≫ a') T T'',
      ScalarCoherent (a ≫ a') T T'' S
  composition_square_unique : ∀ (B' B'' : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
      (T'' : TensorModel B'')
      (a : B ⟶ B') (a' : B' ⟶ B'') (S S' : ScalarModel (a ≫ a') T T''),
    ScalarCoherent (a ≫ a') T T'' S → ScalarCoherent (a ≫ a') T T'' S' →
      S.κ.hom = S'.κ.hom

/-- The complete ringed-point evaluation package.
Source: Stacks Tags 0991, 03EL and 07A4
(blueprint: lem-sf-point-ringed-evaluation-model). -/
structure PointRingedEvaluationModel (k : Type u) [Field k] [IsAlgClosed k] where
  /-- The stalk equivalence is pinned on every colimit injection to the restriction map. -/
  stalk_sections : ∀ F : Sheaf (Scheme.ProEt.topology (Spec (.of k))) (Type (u + 1)),
    StalkEvaluation k F
  /-- Exact point sections and the termwise derived pullback comparison. -/
  exact_sections : ∀ B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1},
    PreservesFiniteLimits (pointModuleSections k B) ∧
    PreservesFiniteColimits (pointModuleSections k B) ∧
    (∀ (K L : CochainComplex (siteModules B) ℤ) (f : K ⟶ L), QuasiIso f →
      QuasiIso ((sectionComplex B).map f))
  /-- The normalized K-flat total tensor comparison. -/
  tensor : ∀ B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1},
    TensorModel B
  /-- Signed associativity, braiding, and both unitors. -/
  tensor_coherent : ∀ B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1},
    TensorCoherent B (tensor B)
  /-- The canonical derived alpha, representative square, naturality, and model independence. -/
  derived : ∀ (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
    [HasDerivedCategory.{u + 2} (ModuleSheaves B)]
    [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B))]
    [(pointModuleSections k B).Additive]
    [PreservesFiniteLimits (pointModuleSections k B)]
    [PreservesFiniteColimits (pointModuleSections k B)],
    CanonicalDerivedPointComparison k B (tensor B)
  /-- The chain scalar square and its derived localization. -/
  scalar : ∀ (B B' : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
    (a : B ⟶ B'),
    ∃ S : ScalarModel a (tensor B) (tensor B'),
      ScalarCoherent a (tensor B) (tensor B') S ∧
      (∀ (P Q : Complexes B),
        DerivedCategory.Q.map ((complexSections k B').map (epsilon a P Q).hom ≫
          ((tensor B').b ((extend a).obj P) ((extend a).obj Q)).hom ≫
          (S.κ.hom.app P ⊗ₘ S.κ.hom.app Q)) =
        DerivedCategory.Q.map (S.κ.hom.app (totalObj B P Q) ≫
          (moduleExtend B a).map ((tensor B).b P Q).hom ≫
          (S.ε ((complexSections k B).obj P) ((complexSections k B).obj Q)).hom))
  /-- Identity and composition compatibility for scalar squares. -/
  scalar_functorial : ∀ B, ScalarFunctoriality k B (tensor B)
  /-- The canonical derived scalar comparison, including its normalized left-derived pair. -/
  derived_scalar : ∀ (B B' : Sheaf (Scheme.ProEt.topology (Spec (.of k)))
      CommRingCat.{u + 1}) (a : B ⟶ B')
    [HasDerivedCategory.{u + 2} (ModuleSheaves B)]
    [HasDerivedCategory.{u + 2} (ModuleSheaves B')]
    [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B))]
    [HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} (sectionRing k B'))]
    [(pointModuleSections k B).Additive] [(pointModuleSections k B').Additive]
    [PreservesFiniteLimits (pointModuleSections k B)]
    [PreservesFiniteColimits (pointModuleSections k B)]
    [PreservesFiniteLimits (pointModuleSections k B')]
    [PreservesFiniteColimits (pointModuleSections k B')],
    ∃ S : ScalarModel a (tensor B) (tensor B'),
      ScalarCoherent a (tensor B) (tensor B') S ∧
      ScalarDerivedCompatible k a (tensor B) (tensor B') S
  /-- The point unit is evaluation of B itself. -/
  unit : ∀ B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1},
    ∀ x : sectionRing k B, (tensor B).moduleUnit.hom x = x
  /-- The condensed coefficient comparison, including geometric-field and point-coefficient
  identifications, the section-ring map at the pro-etale final object, its singleton value,
  naturality, continuous evaluation and the discrete constant-sheaf case. -/
  condensed : ∀ (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X],
    CondensedPointEvaluation k Λ
  /-- The generic derived comparison is instantiated at `Λ_s` after the canonical
  CommRing-valued section-ring reconstruction. -/
  condensed_derived : ∀ (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    [HasDerivedCategory.{u + 2} (ModuleSheaves (condensedPointCoefficientSheaf k Λ))]
    [HasDerivedCategory.{u + 2}
      (ModuleCat.{u + 1} (sectionRing k (condensedPointCoefficientSheaf k Λ)))]
    [(pointModuleSections k (condensedPointCoefficientSheaf k Λ)).Additive]
    [PreservesFiniteLimits (pointModuleSections k (condensedPointCoefficientSheaf k Λ))]
    [PreservesFiniteColimits (pointModuleSections k (condensedPointCoefficientSheaf k Λ))],
    CanonicalDerivedPointComparison k (condensedPointCoefficientSheaf k Λ)
      (tensor (condensedPointCoefficientSheaf k Λ))
/-- Ringed geometric-point evaluation exists with all the displayed normalizations.

The identity pointed neighbourhood is initial, so the geometric stalk is sections at
`Spec k`; the ringed stalk gives `R` and `Γ_s`. Exact sections descend termwise to the
unbounded derived category. The canonical K-flat total tensor map has section tensor as
its inverse, preserves the signed associator, unitors and braiding, and its scalar
extension square is the balanced rule on pure tensors. At a condensed point, final
sections are singleton sections; continuous functions on the singleton are `T`, with
the discrete case as the constant-sheaf specialization.

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-p-proper/sk-thm-sf-kunneth-relative/
thm-sf-kunneth-relative.md`, proof step 5;
Stacks Project Tags 0991, 03EL and 07A4.
(blueprint: lem-sf-point-ringed-evaluation-model)
-/
theorem point_ringed_evaluation_model (k : Type u) [Field k] [IsAlgClosed k] :
    Nonempty (PointRingedEvaluationModel k) := by
  sorry

end AlgebraicGeometry.ProEtale.PointEvaluation
