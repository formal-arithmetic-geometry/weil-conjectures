/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeScalarRingModel
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeScalarRestriction.NativeScalarOrdinaryRestrictionCube
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeScalarDerivedRestriction.NativeScalarInverseDerivedRestrictionCube

/-! # Restriction and direct image under a coefficient-ring presentation

## References

* [Stacks, Tag 03D6]
* [Stacks, Tag 03D7]
* [Stacks, Tag 0D6E]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.EquivalenceCubeTransport

namespace NativeScalarProof
universe u wA wB

private theorem liftFunctor
    {A B : Type (u + 1)} [Category.{u} A] [Category.{u} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (e : A ≌ B) [e.functor.Additive] [e.inverse.Additive] :
    (liftEquivalence e).functor = e.functor.mapDerivedCategory := rfl
end NativeScalarProof

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AlgebraicGeometry.ProEtale
open TwoSquare

attribute [local instance] nativeScalarModuleClosed nativeScalarModuleSymmetric
  nativeScalarModuleFlatResolution nativeScalarModuleLeftColimits nativeScalarModuleRightColimits
  nativeScalarModuleTensorFour nativeScalarModuleGoodTensorLeft nativeScalarModuleGoodTensorRight
  nativeScalarIntegralExact

/-- The exact derived restriction along the two condensed coefficient inclusions, in order. -/
def nativeScalarCompositeRestriction (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) (T : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) T)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj l E.1) T)) :=
  (Mod.comap (coefficientMap
    (Profinite.padicSubfieldRingObjToPadicAlgCl l E) T)).mapDerivedCategory ⋙
    (Mod.comap (padicIntegersToPadicSubfield T l E)).mapDerivedCategory

/-- The pasted inverse restriction/direct-image square. Its construction uses only
restriction and right derived direct image, not either scalar-extension mate. -/
def nativeScalarCompositeRestrictionSquare (l : ℕ) [Fact l.Prime]
    (E : Index l (PadicAlgCl l)) {U V : Scheme.{u}} (g : U ⟶ V) :
    TwoSquare (nativeScalarCompositeRestriction l E U)
      (CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj l) g)
      (CondensedRing.moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj l E.1) g)
      (nativeScalarCompositeRestriction l E V) :=
  TwoSquare.mk _ _ _ _
      (CondensedRing.derivedComapLowerStarIso
        (Profinite.padicSubfieldRingObjToPadicAlgCl l E) g).inv ≫ₕ
    TwoSquare.mk _ _ _ _
      (CondensedRing.derivedComapLowerStarIso
        (padicIntegersRingObjToContinuousMapRingObj l E) g).inv

/-- The inverse of the specified native restriction/direct-image comparison. -/
def nativeRingRestrictionSquare {R S : PurCompactSupport.Coefficients.{u}}
    (a : PurCompactSupport.Change R S) {U V : Scheme.{u}} (g : U ⟶ V) :
    TwoSquare (proEtaleRingRestrictScalars (a.map U)).mapDerivedCategory
      (proEtaleRingDerivedDirectImage g (S.ring V) (S.ring U) (S.pull g))
      (proEtaleRingDerivedDirectImage g (R.ring V) (R.ring U) (R.pull g))
      (proEtaleRingRestrictScalars (a.map V)).mapDerivedCategory :=
  TwoSquare.mk _ _ _ _
    (proEtaleRingRestrictionDerivedDirectImage g
      (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).inv

-- The concrete coefficient functors require elaborating the site and ring transports.
/-- Natural ring diagrams transport the restriction/direct-image cube.
The source and target coefficient systems are arbitrary. Only their ordinary ring
isomorphisms, coefficient square, and precomposition naturality are supplied.
No scalar-extension functor or scalar mate occurs in the conclusion. -/
theorem nativeScalarRestrictionCube
    (l : ℕ) [Fact l.Prime] (E : Index l (PadicAlgCl l))
    {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S)
    (P : NativeScalarRingModel l E a) :
    ∃ k : ∀ T : Scheme.{u},
        (proEtaleRingRestrictScalars (a.map T)).mapDerivedCategory ⋙
            (P.integralEquivalence T).functor.mapDerivedCategory ≅
          (P.closureEquivalence T).functor.mapDerivedCategory ⋙
            nativeScalarCompositeRestriction l E T,
      ∀ {U V : Scheme.{u}} (g : U ⟶ V),
        ∃ (x : proEtaleRingDerivedDirectImage g (R.ring V) (R.ring U) (R.pull g) ⋙
              (P.integralEquivalence V).functor.mapDerivedCategory ≅
            (P.integralEquivalence U).functor.mapDerivedCategory ⋙
              CondensedRing.moduleObjectDerivedPushforward
                (Profinite.padicIntegersRingObj l E.1) g)
          (y : proEtaleRingDerivedDirectImage g (S.ring V) (S.ring U) (S.pull g) ⋙
              (P.closureEquivalence V).functor.mapDerivedCategory ≅
            (P.closureEquivalence U).functor.mapDerivedCategory ⋙
              CondensedRing.moduleObjectDerivedPushforward
                (Profinite.padicAlgClRingObj l) g),
          ((nativeRingRestrictionSquare a g ≫ᵥ
              TwoSquare.mk _ _ _ _ (k V).hom).whiskerLeft y.hom) =
            ((TwoSquare.mk _ _ _ _ (k U).hom ≫ᵥ
                nativeScalarCompositeRestrictionSquare l E g).whiskerRight x.hom) := by
  let ordinary := NativeScalarRestriction.nativeScalarOrdinaryRestrictionCube.{u} l E a P
  let k := ordinary.choose
  have hk := @Exists.choose_spec _ _ ordinary
  refine ⟨NativeScalarDerivedRestriction.forwardRestriction l E a P k, ?_⟩
  intro U V g
  let x := (hk g).choose
  let y := (hk g).choose_spec.choose
  have h := (hk g).choose_spec.choose_spec
  refine ⟨NativeScalarDerivedRestriction.forwardIntegralPush l E a P g x,
    NativeScalarDerivedRestriction.forwardClosurePush l E a P g y, ?_⟩
  refine NatTrans.ext (funext fun N ↦ ?_)
  have hf := forwardCube
    (liftEquivalence (P.closureEquivalence U)) (liftEquivalence (P.integralEquivalence U))
    (liftEquivalence (P.closureEquivalence V)) (liftEquivalence (P.integralEquivalence V))
    (proEtaleRingRestrictScalars (a.map U)).mapDerivedCategory
    (proEtaleRingRestrictScalars (a.map V)).mapDerivedCategory
    (proEtaleRingModuleDirectImage g (S.ring V) (S.ring U) (S.pull g)).rightDerivedFunctor
    (proEtaleRingModuleDirectImage g (R.ring V) (R.ring U) (R.pull g)).rightDerivedFunctor
    (NativeScalarDerivedRestriction.compositeRestriction l E U)
    (NativeScalarDerivedRestriction.compositeRestriction l E V)
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) g).rightDerivedFunctor
    (CondensedRing.lowerStar (Profinite.padicIntegersRingObj l E.1) g).rightDerivedFunctor
    (NativeScalarDerivedRestriction.inverseRestriction l E a P k U)
    (NativeScalarDerivedRestriction.inverseRestriction l E a P k V)
    (NativeScalarDerivedRestriction.inverseIntegralPush l E a P g x)
    (NativeScalarDerivedRestriction.inverseClosurePush l E a P g y)
    (proEtaleRingRestrictionDerivedDirectImage g
      (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g))
    (NativeScalarDerivedRestriction.positiveSquare l E g)
    (NativeScalarDerivedRestriction.inverseCube l E a P k g x y h) N
  simpa only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    TwoSquare.hComp, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.map_id, Category.id_comp, Category.comp_id,
    nativeRingRestrictionSquare, nativeScalarCompositeRestrictionSquare,
    NativeScalarDerivedRestriction.positiveSquare, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    NativeScalarDerivedRestriction.forwardRestriction,
    NativeScalarDerivedRestriction.forwardIntegralPush,
    NativeScalarDerivedRestriction.forwardClosurePush, NativeScalarProof.liftFunctor,
    Category.assoc,
    proEtaleRingDerivedDirectImage, CondensedRing.moduleObjectDerivedPushforward,
    nativeScalarCompositeRestriction, NativeScalarDerivedRestriction.compositeRestriction,
    Functor.whiskerLeft, Functor.whiskerRight, Functor.associator] using hf

end WeilConjectures.LocallyFiniteAdicCompactSupport
