/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AffineCohomologyComparisonData
public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf

import Sheaf.AlgebraicGeometry.UnitScalarRawEvaluation

/-! # Structural scalar normalization of a given coherent realization -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] RingedSpace.moduleCohomology tensorPullback tensorPullbackObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

/-- The usual cohomology map of a localized coefficient endomorphism, with its
restricted cohomology group kept bundled.
Source: Stacks Project, Tag 03Q8.
(blueprint: new-unit-realization-scalar-normalization). -/
def unitRealizationCohomologyMap {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : S.Etale)
    (μ : (Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).obj F ⟶
      (Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).obj F) :
    Etale.rawAffineRestrictedCohomology f q F U ⟶
      Etale.rawAffineRestrictedCohomology f q F U :=
  (Etale.cohomology AddCommGrpCat.{u + 1} (Limits.pullback U.hom f) (q : ℤ)).map
    (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map μ))

/-- The fixed degree-one image functor used to transport coefficient isomorphisms.
Source: Stacks Project, Tags 03Q8 and 03P2.
(blueprint: new-unit-realization-scalar-normalization). -/
def unitRealizationImageFunctor {X S : Scheme.{u}} (f : X ⟶ S) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙
    Etale.rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f ⋙
      DerivedCategory.Plus.homologyFunctor _ 1

/-- The fixed higher image of actual additive structural functions. -/
def unitRealizationImage {X S : Scheme.{u}} (f : X ⟶ S) :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (unitRealizationImageFunctor f).obj X.etaleAdditiveSheaf

/-- The native group of raw structural cohomology classes.
Source: Stacks Project, Tags 03Q8 and 03P2.
(blueprint: new-unit-realization-scalar-normalization). -/
def unitRealizationRawGroup {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale) :
    AddCommGrpCat.{u + 1} :=
  (Etale.abelianHigherDirectImageRawPresheaf f 1 X.etaleAdditiveSheaf).obj (op U)

/-- Evaluate the actual canonical class through the specified higher-image isomorphism.
Source: Stacks Project, Tags 03Q8 and 03P2.
(blueprint: new-unit-realization-scalar-normalization). -/
def unitRealizationValue {X S : Scheme.{u}} (f : X ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent]
    (Φ : unitRealizationImage f ≅ liftedCoherentEtaleSheaf E)
    (U : S.Etale) (z : unitRealizationRawGroup f U) :
    (liftedCoherentEtaleSheaf E).obj.obj (op U) :=
  Φ.hom.hom.app (op U) (Etale.abelianHigherDirectImageClass f 1 X.etaleAdditiveSheaf U z)

/-- Canonical multiplication on the native lifted coherent-section group.
Source: Stacks Project, Tags 03Q8 and 03P2.
(blueprint: new-unit-realization-scalar-normalization). -/
def unitRealizationSectionSmul {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
    (U : S.Etale) (a : Γ(U.left, ⊤))
    (x : (liftedCoherentEtaleSheaf E).obj.obj (op U)) :
    (liftedCoherentEtaleSheaf E).obj.obj (op U) :=
  ULift.up (a • @id Γ((tensorPullback U.hom).obj E, ⊤) x.down)

/-- Structural multiplication is the literal lifted section-module multiplication.
Source: Stacks Project, Tags 03Q8 and 03P2.
(blueprint: new-unit-realization-scalar-normalization). -/
theorem unitRealizationSectionSmul_eq {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
    (U : S.Etale) (a : Γ(U.left, ⊤))
    (x : (liftedCoherentEtaleSheaf E).obj.obj (op U)) :
    unitRealizationSectionSmul E U a x =
      ULift.up (a • @id Γ((tensorPullback U.hom).obj E, ⊤) x.down) := rfl

/-- The native normalization of scalar multiplication on localized structural functions.
Source: Stacks Project, Tags 03Q8 and 03P2.
(blueprint: new-unit-realization-scalar-normalization). -/
def UnitRealizationLocalScalar {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Etale) (a : Γ(U.left, ⊤))
    (μ : (Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).obj
      X.etaleAdditiveSheaf ⟶
      (Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).obj
        X.etaleAdditiveSheaf) : Prop :=
  ∀ (T : (Limits.pullback U.hom f).Etale)
          (x : ((Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).obj
            X.etaleAdditiveSheaf).obj.obj (op T)),
          (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
            (pullback.snd U.hom f) inferInstance).hom.app X.etaleAdditiveSheaf).hom.app
              (op T)) (μ.hom.app (op T) x) =
          ULift.up (@id Γ(T.left, ⊤) ((T.hom ≫ pullback.fst U.hom f).appTop a) *
            (@id Γ(T.left, ⊤) ((((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
              (pullback.snd U.hom f) inferInstance).hom.app X.etaleAdditiveSheaf).hom.app
                (op T)) x).down))

/-- Structural scalar normalization on the actual raw higher-image classes.
Source: Stacks Project, Tags 03Q8 and 03P2.
(blueprint: new-unit-realization-scalar-normalization). -/
def UnitRealizationScalar {X S : Scheme.{u}} (f : X ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent] (Φ : unitRealizationImage f ≅
          liftedCoherentEtaleSheaf E) : Prop :=
      ∀ (U : S.Etale) (a : Γ(U.left, ⊤))
        (μ : (Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).obj
          X.etaleAdditiveSheaf ⟶
          (Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom f)).obj
          X.etaleAdditiveSheaf),
        UnitRealizationLocalScalar f U a μ →
        ∀ (z z' : unitRealizationRawGroup f U),
          Etale.rawRestrictedCohomologyComparison f 1 X.etaleAdditiveSheaf U z' =
            unitRealizationCohomologyMap f 1 X.etaleAdditiveSheaf U μ
              (Etale.rawRestrictedCohomologyComparison f 1 X.etaleAdditiveSheaf U z) →
          unitRealizationValue f E Φ U z' =
          unitRealizationSectionSmul E U a
            (unitRealizationValue f E Φ U z)

/-- Transport a coherent realization with its prescribed class action to actual additive
structural functions. This statement assumes the coherent realization and constructs no
module action from a bare additive isomorphism.

Source: Stacks Project, Etale Cohomology, Tags 03P2 and 03Q8; Sheaves, Tags 0096 and 0097.
(blueprint: new-unit-realization-scalar-normalization).

Proof: The actual adjoint map from the pulled-back unit to the unit is an isomorphism.
On top sections these maps commute with tensor restriction, so they give an isomorphism
from the associated unit etale sheaf to actual lifted additive functions. Apply the
higher-image functor to its inverse and compose with the given realization. For a local
scalar endomorphism, evaluate the coherent restriction isomorphism on each etale test
object. Its section-normalized tensor unit identifies its coordinates with structural
functions. Hence conjugation by the coefficient isomorphism identifies this endomorphism
with the coherent endomorphism induced by multiplication by the pulled-back base scalar.
Naturality of derived evaluation with respect to coefficient maps gives the same
conjugation square on raw restricted cohomology. The Ext-to-derived evaluation is
bijective, so the hypothesized raw equality becomes the equality of coherent Ext
classes under this multiplication. Naturality of the canonical higher-image class map
identifies their images with the classes for the actual structural coefficient. Apply
ha to those coherent classes and then hl to get the desired scalar formula. The maps
are fixed by their section values; no arbitrary coefficient identification is used.
The argument also applies to the empty scheme and zero groups. -/
theorem exists_unitRealizationScalar_of_coherentAction {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (E : S.Modules) [E.IsQuasicoherent]
    (action : ∀ V : S.Etale,
      Module (ULift.{u + 1} Γ(V.left, ⊤))
        ((affineRealizationHigherImage f (SheafOfModules.unit X.ringCatSheaf) 1).obj.obj
          (op V)))
    (Φ : affineRealizationHigherImage f (SheafOfModules.unit X.ringCatSheaf) 1 ≅
      liftedCoherentEtaleSheaf E)
    (ha : ∀ (V : S.Etale) (a : Γ(V.left, ⊤))
      (x : Sheaf.H (liftedCoherentEtaleSheaf
        (affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) V)) 1),
      affineRealizationSmul (action V) (ULift.up a)
        (affineRealizationClass f (SheafOfModules.unit X.ringCatSheaf) 1 V x) =
      affineRealizationClass f (SheafOfModules.unit X.ringCatSheaf) 1 V
        (Sheaf.H.map (coherentEtaleMap _ _
          ((affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) V).smulHom
            ((pullback.fst V.hom f).appTop a))) 1 x))
    (hl : ∀ (V : S.Etale) (a : ULift.{u + 1} Γ(V.left, ⊤))
      (x : (affineRealizationHigherImage f
        (SheafOfModules.unit X.ringCatSheaf) 1).obj.obj (op V)),
      Φ.hom.hom.app (op V) (affineRealizationSmul (action V) a x) =
        ULift.up (a.down • (@id Γ((tensorPullback V.hom).obj E, ⊤)
          (Φ.hom.hom.app (op V) x).down))) :
    ∃ Ψ : unitRealizationImage f ≅ liftedCoherentEtaleSheaf E,
      UnitRealizationScalar f E Ψ := by
  let e := (unitRealizationImageFunctor f).mapIso (unitStructureCoefficientIso X).symm
  refine ⟨e ≪≫ Φ, ?_⟩
  intro U a μ hμ z z' hz
  let x := affineRealizationRawEvaluation f (SheafOfModules.unit X.ringCatSheaf) 1 U
    (unitCoherentRawClass f 1 U z)
  let x' := affineRealizationRawEvaluation f (SheafOfModules.unit X.ringCatSheaf) 1 U
    (unitCoherentRawClass f 1 U z')
  have hs : x' = Sheaf.H.map (coherentEtaleMap _ _
      ((affineRealizationCoefficient f (SheafOfModules.unit X.ringCatSheaf) U).smulHom
        ((pullback.fst U.hom f).appTop a))) 1 x :=
    unitCoherentRawClass_scalar f U a μ hμ z z' hz
  have hc (t : unitRealizationRawGroup f U) :
      e.hom.hom.app (op U)
        (Etale.abelianHigherDirectImageClass f 1 X.etaleAdditiveSheaf U t) =
      affineRealizationClass f (SheafOfModules.unit X.ringCatSheaf) 1 U
        (affineRealizationRawEvaluation f (SheafOfModules.unit X.ringCatSheaf) 1 U
          (unitCoherentRawClass f 1 U t)) :=
    unitCoherentRawClass_class f 1 U t
  change Φ.hom.hom.app (op U) (e.hom.hom.app (op U)
      (Etale.abelianHigherDirectImageClass f 1 X.etaleAdditiveSheaf U z')) =
    unitRealizationSectionSmul E U a
      (Φ.hom.hom.app (op U) (e.hom.hom.app (op U)
        (Etale.abelianHigherDirectImageClass f 1 X.etaleAdditiveSheaf U z)))
  rw [hc z', hc z]
  change Φ.hom.hom.app (op U)
      (affineRealizationClass f (SheafOfModules.unit X.ringCatSheaf) 1 U x') = _
  rw [hs, ← ha U a x]
  exact hl U (ULift.up a)
    (affineRealizationClass f (SheafOfModules.unit X.ringCatSheaf) 1 U x)

end
end AlgebraicGeometry.Scheme.Modules
