/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.IntrinsicCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCoefficientTwists
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameClass
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothTrace
public import WeilConjectures.SmoothPurity.AdicSmoothDualizing.AdicSmoothDualizingFiniteComparison
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated

/-! # Adic and rational smooth dualizing complexes

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-cor-sp-all-coefficients/cor-pur-adic-and-rational-smooth-dualizing-complexes.md
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
universe u v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w₁ w₂
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures
namespace AdicSmoothDualizing

open AlgebraicGeometry.Scheme

attribute [local irreducible] PurCompactSupport.image
  sfIntrinsicModuleEquivalence ProEtale.comparisonUpperStar

/-- The source's completed coefficient unit with Tate twist and even shift.
Only its finite-Tor membership is asserted here; its data is the existing root
line tensor power in a genuine single complex.
Source: corollary proof, the completed unit and its twist
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: the root line is locally free of rank one and derived complete. The signed
twist definition at nonnegative d is exactly line P T d. Its finite reductions
are flat lines in degree zero. The shift gives common Tor interval [-2d,-2d].
Thus this is in the recorded complete finite-Tor constructible subcategory. -/
theorem integralTwist_mem (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (d : ℕ) :
    finiteTorConstructibleIntegral P.coefficients.l P.extension T
      (((DerivedCategory.singleFunctor _ 0).obj (line P T d))⟦2 * (d : ℤ)⟧) := by
  let : ∀ x : T, Invertible (P.coefficients.l : T.residueField x) := fun x ↦
    (show IsUnit (P.coefficients.l : T.residueField x) by
      simpa only [map_natCast] using
        (P.coefficientPrime_isUnit_stalk T aT x).map (T.residue x).hom).invertible
  rw [← (integral_residue_tor P.field P.coefficients.l P.coefficients.different
    P.extension T).2]
  apply (sfIntegralConstructible P.coefficients.l P.extension T).le_shift
    (2 * (d : ℤ)) _
  exact intrinsicIntegralCoefficientTwist_mem P.field P.coefficients.l
    P.coefficients.different P.extension T (d : ℤ)

/-- The full-subcategory restriction of the existing completed Tate coefficient object.
Source: corollary proof, Lambda_X(d)[2d]
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def integralTwist (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (d : ℕ) :
    finiteTorConstructibleIntegralCategory P.coefficients.l P.extension T :=
  ⟨((DerivedCategory.singleFunctor _ 0).obj (line P T d))⟦2 * (d : ℤ)⟧,
    integralTwist_mem P T aT d⟩

/-- The actual quotient projection, transposed under the tensor-unit-normalized
coefficient adjunction and then shifted. Its target is identified with the finite
purity twist through the root-normalized finite comparison above.
Source: corollary proof, reduction-normalized integral reconstruction
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
@[irreducible]
def twistReduction (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (n d : ℕ) :
    (pbcDerivedExtend (PurCompactSupport.projection P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n) T)).obj (integralTwist P T aT d).obj ⟶
      (sfIntrinsicDerivedEquivalence T
        (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
        ((levelSetting P n).diagonalTwist T d) :=
  let φ := PurCompactSupport.projection P.coefficients.l P.extension
    (n + 1) (Nat.succ_pos n) T
  letI := PurCompactSupport.scalarCommShift φ
  ((pbcDerivedExtend φ).commShiftIso (2 * (d : ℤ))).hom.app _ ≫
    (shiftFunctor _ (2 * (d : ℤ))).map
      (((pbcDerivedScalarAdjunction φ).homEquiv _ _).symm
        ((DerivedCategory.singleFunctor _ 0).map (lineProjection P T n d) ≫
          ((pbcRestrict φ).mapDerivedCategorySingleFunctor 0).inv.app _)) ≫
    (finitePowerComparison P T aT n d).inv

/-- The finite coefficient unit is bounded below after exact site comparison.
Source: corollary proof, finite counit
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: exact comparison carries the degree-zero constant sheaf to its degree-zero
inverse image. All negative cohomology sheaves vanish, so zero is a lower bound. -/
theorem finiteUnitPlus (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    DerivedCategory.TStructure.t.plus
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
        (Etale.ordinaryFiniteUnit P.Coefficient T)) := by
  refine ⟨0, ?_⟩
  change DerivedCategory.IsGE
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
      (Etale.ordinaryFiniteUnit P.Coefficient T)) 0
  exact Functor.isGE_mapDerivedCategory_obj _ _ 0

variable (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]

/-- The recorded Nagata compactification of the structure morphism.
Source: corollary proof, compact-support functor
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def compactification : Compactification (X ↘ Spec (.of P.field.k)) :=
  letI := hasCompactification_of_finiteType_over_field P.field.k X
    (Spec (.of P.field.k)) (X ↘ Spec (.of P.field.k))
  HasCompactification.compactification (X ↘ Spec (.of P.field.k))

/-- The normalized finite integration map. Its orientation is the published
coordinate-counit-normalized diagonal purity isomorphism. Every other factor is a
specified proper/open or coefficient-realization comparison and the actual counit.
Source: corollary proof, normalized finite trace at the coefficient unit
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
@[irreducible]
def finiteIntegration (n d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n)) (compactification P X)).obj
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
          ((levelSetting P n).diagonalTwist X d)) ⟶
      (levelSetting P n).coefficientUnit (Spec (.of P.field.k)) :=
  letI := hasCompactification_of_finiteType_over_field P.field.k X
    (Spec (.of P.field.k)) (X ↘ Spec (.of P.field.k))
  letI : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (levelSetting P n).Coefficient)
      (HasCompactification.compactification (X ↘ Spec (.of P.field.k)))).IsLeftAdjoint :=
    inferInstanceAs (Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} (levelSetting P n).Coefficient) (X ↘ Spec (.of P.field.k))).IsLeftAdjoint
  (PurCompactSupport.finiteImageIso P.coefficients.l P.extension n
      (compactification P X)).hom.app _ ≫
    (ProEtale.sfIntrinsicCompactSupportComparison (levelSetting P n).Ring
      (compactification P X)).hom.app _ ≫
    (sfIntrinsicDerivedEquivalence (Spec (.of P.field.k)) (levelSetting P n).Ring).functor.map
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} (levelSetting P n).Coefficient)
        (X ↘ Spec (.of P.field.k))).map
        (((levelSetting P n).diagonalDualizingObject d (X ↘ Spec (.of P.field.k))
          (𝟙 (Spec (.of P.field.k)))).inv ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (levelSetting P n).Coefficient)
          X).mapDerivedCategory.map
          (((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (levelSetting P n).Coefficient)
              (HasCompactification.compactification (X ↘ Spec (.of P.field.k))))).rightAdjointUniq
            (Etale.rightDerivedUpperShriekAdjunction (levelSetting P n).Coefficient
              (X ↘ Spec (.of P.field.k)))).hom.app
            ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} (levelSetting P n).Coefficient)
              (Spec (.of P.field.k))).rightDerivedFunctor.obj
              ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (levelSetting P n).Coefficient)
                (Spec (.of P.field.k))).mapDerivedCategory.obj
                (Etale.ordinaryFiniteUnit (levelSetting P n).Coefficient
                  (Spec (.of P.field.k))))))) ≫
        ProEtale.rightDerivedUpperShriekCounit (Λ := (levelSetting P n).Coefficient)
          (X ↘ Spec (.of P.field.k)) _ (finiteUnitPlus (levelSetting P n) (Spec (.of P.field.k))))

/-- An integral integration map is normalized precisely when its reductions are the
specified finite integration maps, through actual scalar-extension and root comparisons.
Source: corollary proof, adic reconstruction of the normalized counit
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def IsNormalizedIntegralIntegration (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))]
    (t : (PurCompactSupport.image
        (PurCompactSupport.completed P.coefficients.l P.extension) (compactification P X)).obj
          (integralTwist P X (X ↘ Spec (.of P.field.k)) d).obj ⟶
      (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0).obj) : Prop :=
  ∀ n : ℕ,
    (PurCompactSupport.comparison (PurCompactSupport.reduction P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n)) (compactification P X)).app
          (integralTwist P X (X ↘ Spec (.of P.field.k)) d).obj ≫
      (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n)) (compactification P X)).map
          (twistReduction P X (X ↘ Spec (.of P.field.k)) n d) ≫
      finiteIntegration P X n d =
    (pbcDerivedExtend (PurCompactSupport.projection P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n) (Spec (.of P.field.k)))).map t ≫
        twistReduction P (Spec (.of P.field.k)) (𝟙 _) n 0

/-- The selected finite extension in the coefficient-system coordinates.
Source: corollary coefficient conventions
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev fieldStage : ConstructibleExceptionalCoefficients.FieldStage.{u} P.coefficients.l where
  carrier := P.extension

/-- The structure morphism is a morphism over its base field.
Source: the structure-morphism convention of the corollary
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes).
Proof: the structure morphism of Spec k over itself is Spec.map of the identity,
which is the identity by Spec.map_id, so the required triangle commutes by the
right identity law. -/
theorem structureIsOver : (X ↘ Spec (.of P.field.k)).IsOver (Spec (.of P.field.k)) := by
  have _ : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) := inferInstance
  have _ : QuasiCompact (X ↘ Spec (.of P.field.k)) := inferInstance
  have _ : IsSeparated (X ↘ Spec (.of P.field.k)) := inferInstance
  apply (Scheme.Hom.isOver_iff _).2
  change (X ↘ Spec (.of P.field.k)) ≫ Spec.map
    (CommRingCat.ofHom (algebraMap P.field.k P.field.k)) = _
  have h : CommRingCat.ofHom (algebraMap P.field.k P.field.k) =
      𝟙 (CommRingCat.of P.field.k) := rfl
  rw [h, Spec.map_id, Category.comp_id]

attribute [instance] structureIsOver

variable (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
  P.field P.coefficients.different (f := X ↘ Spec (.of P.field.k)))

/-- The exceptional coefficient operation in any of the three stages of the corollary.
This is the recorded normalized constructible adjunction, not a new choice of adjoint.
Source: corollary, Ra_X! and Ra_X^!
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
abbrev operation (s : ConstructibleExceptionalCoefficients.Stage.{u} P.coefficients.l) :=
  S.ring.operation (compactification P X) s

/-- The integral counit read on the twisted coefficient object through an identification
of the dualizing complex. This expression retains the actual adjunction counit.
Source: corollary, integral counit clause
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
def integralCounit (d : ℕ)
    (e : (operation P X S (.integral (fieldStage P))).G.obj
        (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
      integralTwist P X (X ↘ Spec (.of P.field.k)) d) :=
  (operation P X S (.integral (fieldStage P))).F.map e.inv ≫
    (operation P X S (.integral (fieldStage P))).adjunction.counit.app
      (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0)

/-- The same counit in ordinary completed-coefficient compact-support coordinates.
The left realization is normalized by the proper/open construction in the existing system.
Source: corollary, RΓ_c and the completed coefficient unit
(blueprint: cor-pur-adic-and-rational-smooth-dualizing-complexes). -/
@[irreducible]
def integralCounitAmbient (d : ℕ)
    (e : (operation P X S (.integral (fieldStage P))).G.obj
        (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
      integralTwist P X (X ↘ Spec (.of P.field.k)) d) :
    (PurCompactSupport.image
        (PurCompactSupport.completed P.coefficients.l P.extension) (compactification P X)).obj
          (integralTwist P X (X ↘ Spec (.of P.field.k)) d).obj ⟶
      (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0).obj :=
  (S.ring.left (compactification P X)
      (.integral (fieldStage P))).inv.app
        (integralTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
    (finiteTorConstructibleIntegral P.coefficients.l P.extension
      (Spec (.of P.field.k))).ι.map (integralCounit P X S d e)

/-- The ambient counit pairing of an arbitrary arrow into the integral exceptional unit.
Source: the exceptional adjunction, read in ordinary compact-support coordinates
(blueprint: def-pur-adic-smooth-dualizing-integral-data). -/
def integralTrace (d : ℕ)
    (g : integralTwist P X (X ↘ Spec (.of P.field.k)) d ⟶
      (operation P X S (.integral (fieldStage P))).G.obj
        (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0)) :
    (PurCompactSupport.image
        (PurCompactSupport.completed P.coefficients.l P.extension) (compactification P X)).obj
          (integralTwist P X (X ↘ Spec (.of P.field.k)) d).obj ⟶
      (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0).obj :=
  (S.ring.left (compactification P X) (.integral (fieldStage P))).inv.app
      (integralTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
    (finiteTorConstructibleIntegral P.coefficients.l P.extension
      (Spec (.of P.field.k))).ι.map
        (((operation P X S (.integral (fieldStage P))).adjunction.homEquiv _ _).symm g)

end AdicSmoothDualizing
end WeilConjectures
