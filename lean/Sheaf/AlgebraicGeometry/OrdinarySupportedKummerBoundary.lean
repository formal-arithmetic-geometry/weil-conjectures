/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Sites.EtalePicard
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

public import WeilConjectures.AlgebraicGeometry.TensorPullback
/-!
# Relative supported Cartier Kummer boundary

Source: Stacks Project, Tags 03PL and 0A45; blueprint
sec-smooth-purity/sk-prop-sf-cbc/lem-amb-cartier-kummer-map.md
(blueprint: def-asd-ordinary-supported-kummer-boundary).

## Main definitions

* `supportedDivisorSection`: the section dual to the ideal inclusion.
* `SupportedKummerBoundary`: the normalized relative torsor-extension boundary.
* `supportedConstantExchange`: the canonical closed exchange on constants.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The adjunction unit on the constant sheaf, with its canonical constant comparison.
Source: Stacks 0A45 (blueprint: def-asd-ordinary-supported-kummer-boundary). -/
def supportedConstantUnit (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    ordinaryFiniteConstant A T ⟶
      (lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D) :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app
      (ModuleCat.of A A)).hom

/-- The integral constant sheaf used to evaluate a supported class on one.
Source: Stacks 03FD (blueprint: def-asd-ordinary-supported-kummer-boundary). -/
abbrev supportedIntegralConstant (T : Scheme.{u}) :=
  (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- Integral unit for a closed support, with the same inverse-image adjunction.
Source: Stacks 0A45 (blueprint: def-asd-ordinary-supported-kummer-boundary). -/
def supportedIntegralUnit {D T : Scheme.{u}} (i : D ⟶ T) :
    supportedIntegralConstant T ⟶
      (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D) :=
  (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).homEquiv _ _
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom

/-- The section one of the integral constant sheaf.
Source: Stacks 03FD (blueprint: def-asd-ordinary-supported-kummer-boundary). -/
def supportedIntegralOne (T : Scheme.{u}) :
    (supportedIntegralConstant T).obj.obj (op (Scheme.Etale.mk (𝟙 T))) :=
  (toSheafify T.smallEtaleTopology
    ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
      (op (Scheme.Etale.mk (𝟙 T))) (ULift.up 1)

/-- Map from the supported integral coefficient sheaf to the underlying A-coefficients.
Source: Stacks 03FD (blueprint: def-asd-ordinary-supported-kummer-boundary). -/
def supportedIntegralGenerator (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D) ⟶
      (RawModuleScalarComparison.forget A T).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D)) :=
  (lowerStar AddCommGrpCat.{u + 1} i).map (ordinaryFiniteIntegralGenerator A D)

/-- The canonical section of O(D), transposed from the inclusion of its ideal.
Source: blueprint lem-amb-cartier-kummer-map, paragraph 1
(blueprint: def-asd-ordinary-supported-kummer-boundary). -/
def supportedDivisorSection {D T : Scheme.{u}} (i : D ⟶ T) :
    Scheme.Modules.unit T ⟶ Scheme.Modules.dual i.ker.toModules :=
  (SheafOfModules.unitHomEquiv _).symm
    ((SheafOfModules.homObjSectionsEquiv i.ker.toModules (Scheme.Modules.unit T)).symm
      i.ker.toModulesι)

/-- Restriction of the canonical divisor section, transported to the recorded frame
 torsor's ordinary-pullback interface by uniqueness of left adjoints.
Source: blueprint lem-amb-cartier-kummer-map, paragraph 1
(blueprint: def-asd-ordinary-supported-kummer-boundary). -/
def supportedDivisorSectionPullback {D T : Scheme.{u}} (i : D ⟶ T) (W : T.Opens) :
    (Scheme.Modules.pullback W.ι).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback W.ι).obj (Scheme.Modules.dual i.ker.toModules) :=
  let e := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction W.ι)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction W.ι)
  (e.app (Scheme.Modules.unit T)).inv ≫
    (Scheme.Modules.tensorPullback W.ι).map (supportedDivisorSection i) ≫
      (e.app (Scheme.Modules.dual i.ker.toModules)).hom

/-- The actual finite-coefficient Chern class, before the module/abelian comparison.
Source: Stacks 03PL (blueprint: def-asd-ordinary-supported-kummer-boundary). -/
@[irreducible]
def supportedKummerChern (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) {D T : Scheme.{u}} (i : D ⟶ T)
    (hI : i.ker.IsInvertible) (hT : IsUnit (N : Γ(T, ⊤))) :
    Sheaf.H ((RawModuleScalarComparison.forget A T).obj
      (Scheme.finiteEtaleTateLine T N A hA)) 2 :=
  letI := hI.isInvertible_dual_toModules
  Sheaf.H.map (ordinaryFiniteRootMap A N hA T) 2
    (T.kummerδ₁ N hT (Scheme.Pic.toCohomologicalPicardGroup T
      (Scheme.Pic.ofIsInvertible (Scheme.Modules.dual i.ker.toModules))))

section

-- Share the instance proofs used by the recorded unbounded derived category.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- The relative Kummer specification, in the extension model of relative cohomology.
The lifting torsor of E at the supported section one is the frame torsor of O(D),
and its specified section over the complementary open is sent to zero in E.
Thus it remembers the trivialization, not merely the ordinary Picard class.
Source: Stacks 03AJ, 03PL, 0A45 and blueprint lem-amb-cartier-kummer-map, paragraphs 1--4
(blueprint: def-asd-ordinary-supported-kummer-boundary). -/
@[irreducible]
def SupportedKummerBoundary (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (N : Γ(T, ⊤)))
    (c : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2) : Prop :=
  letI := hI.isInvertible_dual_toModules
  letI := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual i.ker.toModules)
  ∀ (W : T.Opens) (_hW : (W : Set T) = (Set.range i.base)ᶜ),
    ∃ (τ : (Scheme.Modules.etaleIsoTorsor (Scheme.Modules.dual i.ker.toModules)).sheaf.obj.obj
          (op (Scheme.Etale.mk W.ι)))
      (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
      (a : T.gmSheaf ⟶ E)
      (b : E ⟶ (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D))
      (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
      (f : (Scheme.Modules.etaleIsoTorsor (Scheme.Modules.dual i.ker.toModules)).sheaf ⟶
        (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj E),
      Scheme.Modules.etaleIsoTorsorVal (Scheme.Modules.dual i.ker.toModules) τ =
        supportedDivisorSectionPullback i W ∧
      (∀ (U : T.Etaleᵒᵖ) (g : T.gmSheaf.obj.obj U)
        (p : (Scheme.Modules.etaleIsoTorsor
          (Scheme.Modules.dual i.ker.toModules)).sheaf.obj.obj U),
        @id (E.obj.obj U) (f.hom.app U ((Scheme.Modules.etaleIsoTorsor
          (Scheme.Modules.dual i.ker.toModules)).vadd U g p)) =
          a.hom.app U g + (@id (E.obj.obj U) (f.hom.app U p))) ∧
      (∀ (U : T.Etaleᵒᵖ) (p : (Scheme.Modules.etaleIsoTorsor
          (Scheme.Modules.dual i.ker.toModules)).sheaf.obj.obj U),
        b.hom.app U (f.hom.app U p) =
          ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D)).obj.map
            ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T).from U.unop).op
            ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
              (supportedIntegralOne T))) ∧
      @id (E.obj.obj (op (Scheme.Etale.mk W.ι)))
        (f.hom.app (op (Scheme.Etale.mk W.ι)) τ) = 0 ∧
      (Ext.mk₀ (supportedIntegralGenerator A i)).comp
          (c.mapExactFunctor (RawModuleScalarComparison.forget A T)) (zero_add 2) =
        (hE.extClass.comp (T.kummerSequence_shortExact N hT).extClass (rfl : 1 + 1 = 2)).comp
          (Ext.mk₀ (ordinaryFiniteRootMap A N hA T)) (add_zero 2)

/-- The canonical closed-immersion exchange on the constant sheaf.
Source: Stacks 0A45, base change (blueprint: def-asd-ordinary-supported-kummer-boundary). -/
def supportedConstantExchange (A : Type (u + 1)) [CommRing A]
    {D D' T T' : Scheme.{u}} (i : D ⟶ T) (i' : D' ⟶ T')
    (v : T' ⟶ T) (w : D' ⟶ D) (sq : CommSq w i' i v) :
    (upperStar (ModuleCat.{u + 1} A) v).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i').obj (ordinaryFiniteConstant A D') :=
  (baseChangeMap (ModuleCat.{u + 1} A) sq).app (ordinaryFiniteConstant A D) ≫
    (lowerStar (ModuleCat.{u + 1} A) i').map
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) w).app
        (ModuleCat.of A A)).hom


end

end AlgebraicGeometry.Etale
