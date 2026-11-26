/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.SystemRestrictionInverseMateEvaluation
import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CompactSupportScalarProofs
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Ordinary compact-support coefficient system transport

This file defines whole-system compact support `systemSupport` (extension by zero followed by
derived proper direct image) on the ringed sequence site of finite coefficient quotients, the
exact restriction `systemRestriction` along a coefficient map `i : E → F`, and the comparison
isomorphisms between restriction and pullback, proper pushforward, open extension and compact
support. It ends with the coefficient projection `systemProjection`, the scalar-adjunction mate
of the compact-support restriction square.

## Implementation details

The restriction comparisons are identities on underlying sections; none of them needs flatness
of the finite quotients, and coefficient restriction is not required to preserve K-injectives.

## References

* Zheng, Construction 4.1 and 4.10.
* Stacks Project, Tags 03D7, 03DI, 03EK, 0D6E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true

set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
  WeilConjectures.SemilinearSections.moduleAbelian WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CompactSupportCondensedRealization

attribute [local irreducible] HasDerivedCategory.standard DerivedCategory.Q DerivedCategory.Qh
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftAdjoint constantSheaf

private theorem normalized_square
    {A B D E M N : Type u} (hA : A = M) (hB : B = N) (hD : D = M) (hE : E = N)
    (a : A → B) (b : B → E) (c : A → D) (d : D → E) (t : M → N)
    (ha : HEq a t) (hb : HEq b (fun x : N ↦ x))
    (hc : HEq c (fun x : M ↦ x)) (hd : HEq d t) :
    (fun x ↦ b (a x)) = (fun x ↦ d (c x)) := by
  subst A B D E
  rw [eq_of_heq ha, eq_of_heq hb, eq_of_heq hc, eq_of_heq hd]

section DerivedUnit
universe a av b bv d dv e ev h hv z zv w
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{w} B]
  [Abelian.HasKInjectiveResolutions A] (G : A ⥤ B) [G.Additive]

/-- The universal right-derived unit `Q(G K) ⟶ RG(Q K)` on a complex `K`, including the
canonical homotopy quotient comparisons. -/
def rightUnitApp (K : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      G.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso B).inv.app
      ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
    G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
    G.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).hom.app K)

/-- Naturality of `rightUnitApp` in chain maps. -/
theorem rightUnitApp_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f) ≫ rightUnitApp G L =
      rightUnitApp G K ≫ G.rightDerivedFunctor.map (DerivedCategory.Q.map f) := by
  change _ ≫ G.rightDerivedFunctorUnitQ L = G.rightDerivedFunctorUnitQ K ≫ _
  exact G.rightDerivedFunctorUnitQ_naturality f

/-- The universal right-derived unit as a natural transformation on complexes. -/
def rightUnit : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ G.rightDerivedFunctor where
  app := rightUnitApp G
  naturality := fun _ _ f ↦ rightUnitApp_naturality G f

end DerivedUnit

private theorem composed_rightUnit_naturality
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions B]
    (V : A ⥤ B) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (G : B ⥤ C) [G.Additive]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    DerivedCategory.Q.map
        ((G.mapHomologicalComplex (.up ℤ)).map
          ((V.mapHomologicalComplex (.up ℤ)).map f)) ≫
        (rightUnit G).app ((V.mapHomologicalComplex (.up ℤ)).obj L) ≫
        G.rightDerivedFunctor.map (V.mapDerivedCategoryFactors.inv.app L) =
      ((rightUnit G).app ((V.mapHomologicalComplex (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (V.mapDerivedCategoryFactors.inv.app K)) ≫
        G.rightDerivedFunctor.map (V.mapDerivedCategory.map (DerivedCategory.Q.map f)) := by
  change _ ≫ rightUnitApp G _ ≫ _ = _
  rw [← Category.assoc, rightUnitApp_naturality]
  simp only [Category.assoc, ← Functor.map_comp]
  apply congrArg ((rightUnit G).app ((V.mapHomologicalComplex (.up ℤ)).obj K) ≫ ·)
  exact congrArg G.rightDerivedFunctor.map
    (V.mapDerivedCategoryFactors.inv.naturality f)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite coefficient quotient rings, lifted to the site universe. -/
abbrev quotientRings (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))

/-- The transition maps between adjacent finite coefficient quotients. -/
def quotientMaps (n : ℕ) : quotientRings l E (n + 1) ⟶ quotientRings l E n :=
  CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((Padic.coefficientExtensionTransition l E (n + 1)).comp ULift.ringEquiv.toRingHom))

/-- Whole-system compact support along a compactification: extension by zero followed by
derived proper direct image, on the ringed sequence site. -/
def systemSupport {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    coefficientSequenceDerived.{u, u} l E X ⥤ coefficientSequenceDerived.{u, u} l E Y :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.J (quotientRings l E) (quotientMaps l E) c.i ⋙
    AlgebraicGeometry.ProEtale.SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) c.g

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E F : Type u) [NormedField E] [NormedField F]
  [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The finite scalar maps commute with the adjacent quotient transitions, even when the
extension is ramified. -/
theorem scalarQuotients_commute (W : Scheme.{u}) (n : ℕ) :
    integralScalarQuotientSheafMap.{u, u} l E F i W (n + 1) ≫
        coefficientSequenceCommRingTransition.{u, u} l F W n =
      coefficientSequenceCommRingTransition.{u, u} l E W n ≫
        integralScalarQuotientSheafMap.{u, u} l E F i W n := by
  unfold integralScalarQuotientSheafMap
  have h (K : Type u) [NormedField K] [NormedAlgebra ℚ_[l] K]
      [FiniteDimensional ℚ_[l] K] :
      coefficientSequenceCommRingTransition.{u, u} l K W n =
        (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
          (quotientMaps l K n) := rfl
  rw [h E, h F, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext x
  exact RingHom.congr_fun (integralScalarQuotientMap_transition l E F i n) x.down

/-- The coefficient ring map on the whole sequence site induced by the finite scalar maps. -/
def scalarSystemMap (W : Scheme.{u}) :=
  SemilinearSections.systemMap (ProEt.topology W)
    (integralCoefficientCommRingSheaf.{u, u} l E W)
    (coefficientSequenceCommRingTransition.{u, u} l E W)
    (integralCoefficientCommRingSheaf.{u, u} l F W)
    (coefficientSequenceCommRingTransition.{u, u} l F W)
    (integralScalarQuotientSheafMap.{u, u} l E F i W) (scalarQuotients_commute l E F i W)

/-- Exact restriction of semilinear systems along the coefficient map. -/
abbrev systemRestriction (W : Scheme.{u}) :=
  SemilinearSections.res (scalarSystemMap l E F i W)

/-- Derived coefficient restriction on semilinear systems. -/
abbrev derivedSystemRestriction (W : Scheme.{u}) :=
  (systemRestriction l E F i W).mapDerivedCategory

/-- The universal, K-flat normalized scalar extension on semilinear systems. -/
def systemScalarData (W : Scheme.{u}) :
    SemilinearSections.ScalarSystems.{u + 1, u, u + 1} (ProEt.topology W)
      (integralCoefficientCommRingSheaf.{u, u} l E W)
      (coefficientSequenceCommRingTransition.{u, u} l E W)
      (integralCoefficientCommRingSheaf.{u, u} l F W)
      (coefficientSequenceCommRingTransition.{u, u} l F W)
      (integralScalarQuotientSheafMap.{u, u} l E F i W)
      (scalarQuotients_commute l E F i W) :=
  (SemilinearSections.semilinearDerivedSections.{u + 1, u, u + 1} (ProEt.topology W)
    (integralCoefficientCommRingSheaf.{u, u} l E W)
    (coefficientSequenceCommRingTransition.{u, u} l E W)).some.coefficientExtension
      (integralCoefficientCommRingSheaf.{u, u} l F W)
    (coefficientSequenceCommRingTransition.{u, u} l F W)
      (integralScalarQuotientSheafMap.{u, u} l E F i W) (scalarQuotients_commute l E F i W)

attribute [local irreducible] systemScalarData HasDerivedCategory.standard
  completedIntegralCommRingSheafUnrestricted DerivedCategory.Q DerivedCategory.Qh

-- The remaining constructions use the canonical functors through their APIs.

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem scalarSystemMap_app (W : Scheme.{u}) (n : ℕ) (U : W.ProEtᵒᵖ) :
    (scalarSystemMap l E F i W).hom.app (op (n, U.unop)) =
      (integralScalarQuotientSheafMap l E F i W n).hom.app U :=
  (SemilinearSections.systemMap_existsUnique (ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W)
    (coefficientSequenceCommRingTransition l E W)
    (integralCoefficientCommRingSheaf l F W)
    (coefficientSequenceCommRingTransition l F W)
    (integralScalarQuotientSheafMap l E F i W)
    (scalarQuotients_commute l E F i W)).exists.choose_spec n U

attribute [local irreducible] scalarSystemMap

attribute [local irreducible] constantSheaf

private theorem scalarSystemMap_push_square {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SemilinearProperOpen.coefficientMap (quotientRings l E) (quotientMaps l E) f ≫
        ((SemilinearProperOpen.siteMap f).sheafPushforwardContinuous CommRingCat.{u + 1}
          (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceTopology (ProEt.topology X))).map
            (scalarSystemMap l E F i X) =
      scalarSystemMap l E F i Y ≫
        SemilinearProperOpen.coefficientMap (quotientRings l F) (quotientMaps l F) f := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have hE := eq_of_heq ((SemilinearProperOpen.coefficientMap_existsUnique
    (quotientRings l E) (quotientMaps l E) f).choose_spec.1 U.unop.1 U.unop.2)
  have hF := eq_of_heq ((SemilinearProperOpen.coefficientMap_existsUnique
    (quotientRings l F) (quotientMaps l F) f).choose_spec.1 U.unop.1 U.unop.2)
  have hX := scalarSystemMap_app l E F i X U.unop.1
    (op ((proEtaleBaseChange f).obj U.unop.2))
  have hY := scalarSystemMap_app l E F i Y U.unop.1 (op U.unop.2)
  have h := congrArg (fun t ↦ t.hom.app (op U.unop.2))
    (VaryingRing.constantMap_naturality f (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
        ((integralScalarQuotientMap l E F i U.unop.1).comp
          (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))))
  exact (congrArg₂ (fun a b ↦ a ≫ b) hE hX).trans
    (h.symm.trans (congrArg₂ (fun a b ↦ a ≫ b) hY hF).symm)

private theorem restriction_push_iso
    {A B : Type*} [Category A] [Category B]
    {J : GrothendieckTopology A} {K : GrothendieckTopology B}
    (T : A ⥤ B) [T.IsContinuous J K]
    {RX SX : Sheaf K RingCat.{u + 1}} {RY SY : Sheaf J RingCat.{u + 1}}
    (aX : RX ⟶ SX) (aY : RY ⟶ SY)
    (bE : RY ⟶ (T.sheafPushforwardContinuous RingCat.{u + 1} J K).obj RX)
    (bF : SY ⟶ (T.sheafPushforwardContinuous RingCat.{u + 1} J K).obj SX)
    (h : bE ≫ (T.sheafPushforwardContinuous RingCat.{u + 1} J K).map aX = aY ≫ bF) :
    ∃! d : SheafOfModules.restrictScalars.{u + 1} aX ⋙ SheafOfModules.pushforward bE ≅
        SheafOfModules.pushforward bF ⋙ SheafOfModules.restrictScalars aY,
      ∀ (M : SheafOfModules.{u + 1} SX) (U : Aᵒᵖ)
        (x : M.val.obj (T.op.obj U)), (d.hom.app M).val.app U x = x := by
  let d : SheafOfModules.restrictScalars.{u + 1} aX ⋙ SheafOfModules.pushforward bE ≅
      SheafOfModules.pushforward bF ⋙ SheafOfModules.restrictScalars aY :=
    SheafOfModules.pushforwardComp (F := T) (G := 𝟭 B) bE aX ≪≫
      SheafOfModules.pushforwardCongr h ≪≫
        (SheafOfModules.pushforwardComp (F := 𝟭 A) (G := T) aY bF).symm
  apply ExistsUnique.intro d (fun _ _ _ ↦ rfl)
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact (hd' M U x).trans (show (d.hom.app M).val.app U x = x from rfl).symm

attribute [-instance] WeilConjectures.completedOrdinaryScalarExtension_additive in
/-- There is a unique isomorphism between restriction followed by ordinary pushforward and
pushforward followed by restriction that is the identity on sections. -/
theorem systemRestrictionPush_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! d : systemRestriction l E F i X ⋙
          SemilinearProperOpen.push (quotientRings l E) (quotientMaps l E) f ≅
        SemilinearProperOpen.push (quotientRings l F) (quotientMaps l F) f ⋙
          systemRestriction l E F i Y,
      ∀ (M : coefficientSequenceModules.{u, u} l F X) (n : ℕ) (U : Y.ProEt)
        (x : ((systemRestriction l E F i X ⋙
          SemilinearProperOpen.push (quotientRings l E) (quotientMaps l E) f).obj M).val.obj
            (op (n, U))),
        HEq ((d.hom.app M).val.app (op (n, U)) x) x := by
  let a (W : Scheme.{u}) := (sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (scalarSystemMap l E F i W)
  let b (K : Type u) [NormedField K] [NormedAlgebra ℚ_[l] K]
      [FiniteDimensional ℚ_[l] K] := (sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (SemilinearProperOpen.coefficientMap (quotientRings l K) (quotientMaps l K) f)
  have he : b E ≫ ((SemilinearProperOpen.siteMap f).sheafPushforwardContinuous
      RingCat.{u + 1} (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).map (a X) = a Y ≫ b F := by
    exact congrArg (fun t ↦ (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map t)
        (scalarSystemMap_push_square l E F i f)
  obtain ⟨d, hd, hu⟩ := restriction_push_iso (SemilinearProperOpen.siteMap f)
    (a X) (a Y) (b E) (b F) he
  apply ExistsUnique.intro d
  · intro M n U x
    exact heq_of_eq (hd M (op (n, U)) x)
  intro d' hd'
  exact hu d' (fun M U x ↦ eq_of_heq (hd' M U.unop.1 U.unop.2 x))

/-- The ordinary inverse-image comparison, the adjunction mate of the pushforward
comparison. -/
def systemRestrictionPullInv {X Y : Scheme.{u}} (f : X ⟶ Y) :
    systemRestriction l E F i Y ⋙
        SemilinearProperOpen.pull (quotientRings l E) (quotientMaps l E) f ⟶
      SemilinearProperOpen.pull (quotientRings l F) (quotientMaps l F) f ⋙
        systemRestriction l E F i X :=
  (mateEquiv
    (SemilinearProperOpen.ordinaryAdj (quotientRings l F) (quotientMaps l F) f)
    (SemilinearProperOpen.ordinaryAdj (quotientRings l E) (quotientMaps l E) f)).symm
      (systemRestrictionPush_existsUnique l E F i f).choose.inv

attribute [local irreducible] systemRestrictionPullInv

section PullbackIso
private theorem system_restriction_eval (W : Scheme.{u}) (n : ℕ) :
    ∃ e : systemRestriction l E F i W ⋙
        VaryingRing.eval (quotientRings l E) (quotientMaps l E) W n ≅
      VaryingRing.eval (quotientRings l F) (quotientMaps l F) W n ⋙
        SemilinearSections.res (integralScalarQuotientSheafMap l E F i W n),
      ∀ M U, HEq (fun x ↦ (e.hom.app M).val.app U x)
        (fun x : M.val.obj (op (n, U.unop)) ↦ x) := by
  obtain ⟨e, he, -⟩ := SemilinearSections.restrictionEvaluation_existsUnique
    (ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
    (coefficientSequenceCommRingTransition l E W)
    (integralCoefficientCommRingSheaf l F W)
    (coefficientSequenceCommRingTransition l F W)
    (integralScalarQuotientSheafMap l E F i W) (scalarQuotients_commute l E F i W) n
  unfold systemRestriction scalarSystemMap
  exact ⟨e, he⟩

private theorem system_pull_inverse_evaluation_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (M : VaryingRing.Modules (quotientRings l F) (quotientMaps l F) Y) :
    IsIso ((VaryingRing.eval (quotientRings l E) (quotientMaps l E) X n).map
      ((systemRestrictionPullInv l E F i f).app M)) := by
  obtain ⟨eX, heX⟩ := system_restriction_eval l E F i X n
  obtain ⟨eY, heY⟩ := system_restriction_eval l E F i Y n
  have hs : (StrictTower.constantRingIso ((quotientRings l E) n) f).hom ≫
      integralScalarQuotientSheafMap l E F i X n =
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
      (integralScalarQuotientSheafMap l E F i Y n) ≫
        (StrictTower.constantRingIso ((quotientRings l F) n) f).hom := by
    exact (proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom
        ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
          ((integralScalarQuotientMap l E F i n).comp
            (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom)))).symm
  unfold systemRestrictionPullInv
  exact restriction_inverse_mate_eval_isIso
    (quotientRings l E) (quotientRings l F) (quotientMaps l E) (quotientMaps l F) f n
    (scalarSystemMap l E F i X) (scalarSystemMap l E F i Y)
    (integralScalarQuotientSheafMap l E F i X n)
    (integralScalarQuotientSheafMap l E F i Y n) hs
    (systemRestrictionPush_existsUnique l E F i f).choose
    (fun N U x ↦ (systemRestrictionPush_existsUnique l E F i f).choose_spec.1 N
      U.unop.1 U.unop.2 x) eX heX eY heY M

universe evalObj evalHom evalRing

private theorem evaluations_reflect_iso
    {C : Type evalObj} [Category.{evalHom} C] [EssentiallySmall.{evalRing} C]
    (J : GrothendieckTopology C)
    (B : ℕ → Sheaf J CommRingCat.{evalRing}) (τ : ∀ n, B (n + 1) ⟶ B n)
    {M N : SemilinearSections.Systems.{evalObj, evalHom, evalRing} J B τ} (g : M ⟶ N)
    (h : ∀ n, IsIso ((SemilinearSections.evaluation J B τ n).map g)) : IsIso g := by
  let T := SheafOfModules.forget.{evalRing} (SemilinearSections.ring
    (coefficientSequenceTopology J) (SemilinearSections.systemRing J B τ)) ⋙
    PresheafOfModules.toPresheaf _
  have hh (U : (ℕ × C)ᵒᵖ) : IsIso ((T.map g).app U) := by
    have := h U.unop.1
    let Tn := SheafOfModules.evaluation.{evalRing}
      (SemilinearSections.ring J (B U.unop.1)) (op U.unop.2)
    have : IsIso (Tn.map ((SemilinearSections.evaluation J B τ U.unop.1).map g)) :=
      Functor.map_isIso Tn _
    have hb := ConcreteCategory.bijective_of_isIso
      (Tn.map ((SemilinearSections.evaluation J B τ U.unop.1).map g))
    exact (ConcreteCategory.isIso_iff_bijective ((T.map g).app U)).mpr hb
  have hT : IsIso (T.map g) := (NatTrans.isIso_iff_isIso_app _).mpr hh
  have : IsIso ((PresheafOfModules.toPresheaf _).map
      ((SheafOfModules.forget _).map g)) := hT
  have : IsIso ((SheafOfModules.forget _).map g) :=
    isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)
  exact isIso_of_reflects_iso g (SheafOfModules.forget _)

/-- The ordinary inverse-image comparison is an isomorphism. -/
@[instance] theorem systemRestrictionPullInv_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (systemRestrictionPullInv l E F i f) := by
  have hM (M : VaryingRing.Modules (quotientRings l F) (quotientMaps l F) Y) :
      IsIso ((systemRestrictionPullInv l E F i f).app M) :=
    evaluations_reflect_iso (ProEt.topology X)
      (VaryingRing.coefficients (quotientRings l E) X)
      (VaryingRing.coefficientTransition (quotientRings l E) (quotientMaps l E) X) _
      (fun n ↦ system_pull_inverse_evaluation_isIso l E F i f n M)
  exact (NatTrans.isIso_iff_isIso_app _).mpr hM

end PullbackIso

/-- The ordinary pullback of semilinear systems is additive. -/
instance systemPullAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (SemilinearProperOpen.pull (quotientRings l E) (quotientMaps l E) f).Additive :=
  (SemilinearProperOpen.pull_exact (quotientRings l E) (quotientMaps l E) f).1

attribute [-instance] systemPullAdditive

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The derived pullback/restriction square, induced by the ordinary one. -/
def systemRestrictionPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SemilinearProperOpen.P (quotientRings l F) (quotientMaps l F) f ⋙
        derivedSystemRestriction l E F i X ≅
      derivedSystemRestriction l E F i Y ⋙
        SemilinearProperOpen.P (quotientRings l E) (quotientMaps l E) f :=
  letI := systemPullAdditive l E f
  letI := systemPullAdditive l F f
  letI := (SemilinearProperOpen.pull_exact (quotientRings l E) (quotientMaps l E) f).2.1
  letI := (SemilinearProperOpen.pull_exact (quotientRings l E) (quotientMaps l E) f).2.2
  letI := (SemilinearProperOpen.pull_exact (quotientRings l F) (quotientMaps l F) f).2.1
  letI := (SemilinearProperOpen.pull_exact (quotientRings l F) (quotientMaps l F) f).2.2
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (asIso (systemRestrictionPullInv l E F i f)).symm ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

attribute [local irreducible] systemRestrictionPull

/-- The proper direct image/restriction comparison, the derived adjunction mate of
`systemRestrictionPull`. -/
def systemRestrictionPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SemilinearProperOpen.R (quotientRings l F) (quotientMaps l F) f ⋙
        derivedSystemRestriction l E F i Y ⟶
      derivedSystemRestriction l E F i X ⋙
        SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) f :=
  mateEquiv (SemilinearProperOpen.adj (quotientRings l F) (quotientMaps l F) f)
    (SemilinearProperOpen.adj (quotientRings l E) (quotientMaps l E) f)
      (systemRestrictionPull l E F i f).inv

attribute [local irreducible] systemRestrictionPush

attribute [-instance] WeilConjectures.completedOrdinaryScalarExtension_additive in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalar_push_resolution {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : CochainComplex (coefficientSequenceModules.{u, u} l F X) ℤ) [I.IsKInjective]
    (J : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ) [J.IsKInjective]
    (j : ((systemRestriction l E F i X).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    QuasiIso (((SemilinearProperOpen.push (quotientRings l E)
      (quotientMaps l E) f).mapHomologicalComplex (.up ℤ)).map j) := by
  have : RepresentablyFlat (proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  have : RepresentablyFlat (SemilinearProperOpen.siteMap f) := by
    constructor
    intro U
    exact IsCofiltered.of_equivalence
      (StructuredArrow.prodEquivalence U.1 U.2 (𝟭 ℕ) (proEtaleBaseChange f)).symm
  exact continuous_scalar_resolution
    (coefficientSequenceTopology (ProEt.topology Y))
    (coefficientSequenceTopology (ProEt.topology X)) (SemilinearProperOpen.siteMap f)
    (SemilinearProperOpen.ringSystem (quotientRings l F) (quotientMaps l F) X)
    (SemilinearProperOpen.ringSystem (quotientRings l E) (quotientMaps l E) X)
    (SemilinearProperOpen.ringSystem (quotientRings l E) (quotientMaps l E) Y)
    (scalarSystemMap l E F i X)
    (SemilinearProperOpen.coefficientMap (quotientRings l E) (quotientMaps l E) f) I J j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] WeilConjectures.completedOrdinaryScalarExtension_additive in
/-- The proper direct image/restriction comparison is an isomorphism. -/
@[instance] theorem systemRestrictionPush_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (systemRestrictionPush l E F i f) := by
  let e := asIso (systemRestrictionPullInv l E F i f)
  have he : IsIso (mateEquiv
      (SemilinearProperOpen.ordinaryAdj (quotientRings l F) (quotientMaps l F) f)
      (SemilinearProperOpen.ordinaryAdj (quotientRings l E) (quotientMaps l E) f)
      (TwoSquare.mk _ _ _ _ e.hom)) := by
    have hm : (mateEquiv
        (SemilinearProperOpen.ordinaryAdj (quotientRings l F) (quotientMaps l F) f)
        (SemilinearProperOpen.ordinaryAdj (quotientRings l E) (quotientMaps l E) f)
        (TwoSquare.mk _ _ _ _ e.hom)) =
        (systemRestrictionPush_existsUnique l E F i f).choose.inv := by
      dsimp only [e, asIso_hom]
      unfold systemRestrictionPullInv
      exact Equiv.apply_symm_apply _ _
    rw [hm]
    infer_instance
  have h := derived_mate_isIso_of_resolution
    (SemilinearProperOpen.ordinaryAdj (quotientRings l F) (quotientMaps l F) f)
    (SemilinearProperOpen.ordinaryAdj (quotientRings l E) (quotientMaps l E) f) e
    (fun I hI J hJ j hj ↦ by
      have := hI
      have := hJ
      have := hj
      exact scalar_push_resolution l E F i f I J j)
  unfold systemRestrictionPush systemRestrictionPull
  exact h

attribute [local irreducible] SemilinearProperOpen.J SemilinearProperOpen.jAdj

/-- The extension-by-zero/restriction comparison along an open immersion, the inverse mate of
`systemRestrictionPull`. -/
def systemRestrictionOpenInv {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    derivedSystemRestriction l E F i X ⋙
        SemilinearProperOpen.J (quotientRings l E) (quotientMaps l E) j ⟶
      SemilinearProperOpen.J (quotientRings l F) (quotientMaps l F) j ⋙
        derivedSystemRestriction l E F i Z :=
  (mateEquiv (SemilinearProperOpen.jAdj (quotientRings l F) (quotientMaps l F) j)
    (SemilinearProperOpen.jAdj (quotientRings l E) (quotientMaps l E) j)).symm
      (systemRestrictionPull l E F i j).hom

attribute [local irreducible] systemRestrictionOpenInv

attribute [-instance] WeilConjectures.completedOrdinaryScalarExtension_additive in
/-- The extension-by-zero/restriction comparison is an isomorphism. -/
@[instance] theorem systemRestrictionOpenInv_isIso {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] : IsIso (systemRestrictionOpenInv l E F i j) := by
  have := SemilinearProperOpen.jAdj_unit_isIso (quotientRings l F) (quotientMaps l F) j
  have := SemilinearProperOpen.jAdj_unit_isIso (quotientRings l E) (quotientMaps l E) j
  let ff := (SemilinearProperOpen.jAdj (quotientRings l E)
    (quotientMaps l E) j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have hc (M : coefficientSequenceDerived.{u, u} l F X) :
      IsIso ((SemilinearProperOpen.jAdj (quotientRings l E) (quotientMaps l E) j).counit.app
        ((derivedSystemRestriction l E F i Z).obj
          ((SemilinearProperOpen.J (quotientRings l F) (quotientMaps l F) j).obj M))) := by
    apply (SemilinearProperOpen.jAdj (quotientRings l E)
      (quotientMaps l E) j).isIso_counit_app_iff_mem_essImage.mpr
    exact scalarRestriction_openSupported
      (quotientRings l E) (quotientRings l F) (quotientMaps l E) (quotientMaps l F)
      j (scalarSystemMap l E F i Z) M
  unfold systemRestrictionOpenInv
  exact inverse_mate_isIso_of_support
    (SemilinearProperOpen.jAdj (quotientRings l F) (quotientMaps l F) j)
    (SemilinearProperOpen.jAdj (quotientRings l E) (quotientMaps l E) j)
    (derivedSystemRestriction l E F i X) (derivedSystemRestriction l E F i Z)
    (systemRestrictionPull l E F i j) hc

/-- The isomorphism between restriction followed by compact support and compact support
followed by restriction. -/
def systemSupportRestriction {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    derivedSystemRestriction l E F i X ⋙ systemSupport l E c ≅
      systemSupport l F c ⋙ derivedSystemRestriction l E F i Y :=
  Functor.isoWhiskerRight (asIso (systemRestrictionOpenInv l E F i c.i))
      (SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) c.g) ≪≫
    Functor.isoWhiskerLeft
      (SemilinearProperOpen.J (quotientRings l F) (quotientMaps l F) c.i)
      (asIso (systemRestrictionPush l E F i c.g)).symm

attribute [local irreducible] systemSupportRestriction

attribute [local semireducible] scalarSystemMap

/-- The coefficient projection for compact support, the scalar-adjunction mate of
`systemSupportRestriction`. -/
def systemProjection {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    systemSupport l E c ⋙ (systemScalarData l E F i Y).scalar.T ⟶
      (systemScalarData l E F i X).scalar.T ⋙ systemSupport l F c :=
  ((mateEquiv (systemScalarData l E F i X).scalar.adjunction
    (systemScalarData l E F i Y).scalar.adjunction).symm
      (TwoSquare.mk _ (systemSupport l F c) (systemSupport l E c) _
        (systemSupportRestriction l E F i c).hom))

end WeilConjectures.CompactSupportCondensedRealization
