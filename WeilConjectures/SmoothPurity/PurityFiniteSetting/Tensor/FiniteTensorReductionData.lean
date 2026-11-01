/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.TransposedFamilyData.TransposedFamilyData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.SupportedEtaleTensorOrigin.SupportedEtaleTensorOrigin
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

/-! # Finite reduction of signed twists and tensor presentations

Source: main-20261015, thm-pur-finite-reduction-of-purity, proof Step 2;
Stacks Tags 07A4, 0FPT, 0FNH, 03EK and 03EM.
(blueprint: def-pur-finite-tensor-reduction-data)

## Main declarations

- `finiteTensorReduction`
- `finiteTensorLine`
- `FiniteTensorLineMapsNormalized`
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures.PurityFiniteSetting

/-- The published finite signed line, reindexed from exponent n+1 to a positive level.
Source: def-coefficient-twists-detailed, finite clause
(blueprint: def-pur-finite-tensor-reduction-data). -/
def finiteTensorFirstLine (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    proEtaleRingModules T (proEtaleConstantRing T P.Ring) :=
  Eq.mp (congrArg (fun n : ℕ ↦ proEtaleRingModules T
    (proEtaleConstantRing T (Padic.coefficientExtensionRing P.coefficients.l P.extension n)))
      (Nat.sub_add_cancel P.level_pos))
    (finiteCoefficientTwist P.coefficients.l P.extension T (P.level - 1) 1)

/-- The existing powers and internal duals of the prescribed first coefficient line.
Source: def-coefficient-twists-detailed
(blueprint: def-pur-finite-tensor-reduction-data). -/
def finiteTensorLine (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (r : ℤ) :
    proEtaleRingModules T (proEtaleConstantRing T P.Ring) :=
  coefficientTwistLine T (R := proEtaleConstantRing T P.Ring) (P.finiteTensorFirstLine T) r

/-- The degree-zero signed sheaf in the published fixed-scalar realization.
Source: def-coefficient-twists-detailed
(blueprint: def-pur-finite-tensor-reduction-data). -/
def finiteTensorFixedSheaf (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (r : ℤ) :
    Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient) :=
  (sfIntrinsicModuleEquivalence T P.Ring).inverse.obj (P.finiteTensorLine T r)

/-- Fixed-scalar coordinates of the same signed line in degree zero.
Source: def-coefficient-twists-detailed and the intrinsic realization
(blueprint: def-pur-finite-tensor-reduction-data). -/
def finiteTensorFixedLine (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) (r : ℤ) :
    _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) :=
  (_root_.DerivedCategory.singleFunctor _ 0).obj
    (P.finiteTensorFixedSheaf T r)

/-- The actual scalar extension in fixed-scalar coordinates, retaining its target action.
Its scalarPresentation identifies it with the published intrinsic finiteReduction.
Source: Stacks 06YY; def-pur-finite-reduction-root-charts
(blueprint: def-pur-finite-tensor-reduction-data). -/
def finiteTensorReduction (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) :
    _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) ⥤
      _root_.DerivedCategory (Sheaf (ProEt.topology T)
        (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient)) :=
  ProEtale.SupportedEtaleTensorOrigin.fixedScalar (P.finiteReductionRingHom m hm hmn) T

/-- The actual scalar adjunction, with its fixed-coordinate functor type shared.
Source: def-pur-finite-reduction-root-charts, scalar extension adjunction
(blueprint: def-pur-finite-tensor-reduction-data). -/
def finiteTensorAdjunction (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) :
    P.finiteTensorReduction m hm hmn T ⊣
      ProEtale.SupportedEtaleTensorOrigin.fixedRestriction
        (P.finiteReductionRingHom m hm hmn) T :=
  Adjunction.ofIsRightAdjoint
    (ProEtale.SupportedEtaleTensorOrigin.fixedRestriction
      (P.finiteReductionRingHom m hm hmn) T)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact scalar restriction's adjunction specifies the integer shift on scalar extension.
Source: Stacks 06YY (blueprint: def-pur-finite-tensor-reduction-data). -/
instance finiteTensorReductionCommShift (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) :
    (P.finiteTensorReduction m hm hmn T).CommShift ℤ :=
  (P.finiteTensorAdjunction m hm hmn T).leftAdjointCommShift ℤ

/-- The actual scalar-shift isomorphism with its specified adjunction instance supplied
explicitly. This avoids searching for a shift structure on an opaque left adjoint.
Source: Stacks 06YY, blueprint proof Step 6
(blueprint: def-pur-finite-tensor-reduction-data). -/
def finiteTensorScalarShift (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) (s : ℤ) :
    shiftFunctor _ s ⋙ P.finiteTensorReduction m hm hmn T ≅
      P.finiteTensorReduction m hm hmn T ⋙ shiftFunctor _ s :=
  letI := P.finiteTensorReductionCommShift m hm hmn T
  (P.finiteTensorReduction m hm hmn T).commShiftIso s

/-- The constant integral-to-finite coefficient map, at the actual positive level.
Source: def-coefficient-twists-detailed, ordinary finite reduction
(blueprint: def-pur-finite-tensor-reduction-data). -/
def finiteTensorIntegralMap (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.mk
      (Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level))))

/-- Semilinear maps of the actual signed coefficient sheaves.
Source: blueprint proof Steps 3--5
(blueprint: def-pur-finite-tensor-reduction-data). -/
abbrev FiniteTensorLineMaps (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) :=
  ∀ r : ℤ, P.finiteTensorLine T r ⟶
    (proEtaleCoefficientRestrictScalars T (P.finiteReductionRingHom m hm hmn)).obj
      ((P.finiteReductionSetting m hm).finiteTensorLine T r)

/-- The actual underlying section map, forgetting only the restricted scalar action.
Source: blueprint proof Steps 3--5, exact scalar restriction
(blueprint: def-pur-finite-tensor-reduction-data). -/
def finiteTensorLineSectionMap (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) (c : P.FiniteTensorLineMaps m hm hmn T)
    (r : ℤ) (U : T.ProEtᵒᵖ) :
    (P.finiteTensorLine T r).val.obj U →
      ((P.finiteReductionSetting m hm).finiteTensorLine T r).val.obj U :=
  (c r).val.app U

/-- Unit, integral balancing, positive powers, and negative dual evaluation fix all maps.
The heterogeneous equality in degree one only transports the positive-level indexing;
it retains the actual ordinary tensor of the integral line with the quotient ring.
Source: blueprint proof Steps 3--5; Stacks 03EK and 03EM
(blueprint: def-pur-finite-tensor-reduction-data). -/
def FiniteTensorLineMapsNormalized (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) (c : P.FiniteTensorLineMaps m hm hmn T) : Prop :=
  (∀ (U : T.ProEtᵒᵖ) (a : (proEtaleConstantRing T P.Ring).obj.obj U),
    P.finiteTensorLineSectionMap m hm hmn T c 0 U a =
      (proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn)).hom.app U a) ∧
  (∀ (U : T.ProEtᵒᵖ) (a : (proEtaleConstantRing T P.Ring).obj.obj U)
      (x : (purTwistIntegralOne T P.coefficients.l P.extension).val.obj U)
      (z : (P.finiteTensorFirstLine T).val.obj U),
    HEq z (SheafOfModules.scalarExtensionSection
      (P.finiteTensorIntegralMap T) (purTwistIntegralOne T P.coefficients.l P.extension) U a x) →
    HEq (P.finiteTensorLineSectionMap m hm hmn T c 1 U z)
      (SheafOfModules.scalarExtensionSection
        ((P.finiteReductionSetting m hm).finiteTensorIntegralMap T)
        (purTwistIntegralOne T P.coefficients.l P.extension) U
        ((proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn)).hom.app U a)
        x)) ∧
  (∀ (j : ℕ) (U : T.ProEtᵒᵖ)
      (x : (P.finiteTensorLine T (Int.ofNat (j + 1))).val.obj U)
      (y : (P.finiteTensorFirstLine T).val.obj U)
      (xB : ((P.finiteReductionSetting m hm).finiteTensorLine T
        (Int.ofNat (j + 1))).val.obj U)
      (yB : ((P.finiteReductionSetting m hm).finiteTensorFirstLine T).val.obj U),
    HEq (P.finiteTensorLineSectionMap m hm hmn T c (Int.ofNat (j + 1)) U x) xB →
    HEq (P.finiteTensorLineSectionMap m hm hmn T c 1 U y) yB →
    HEq (P.finiteTensorLineSectionMap m hm hmn T c (Int.ofNat (j + 2)) U
      (SheafOfModules.siteSheafTensorTmul (A := proEtaleConstantRing T P.Ring)
        (P.finiteTensorLine T (Int.ofNat (j + 1))) (P.finiteTensorFirstLine T) U x y))
      (SheafOfModules.siteSheafTensorTmul
        (A := proEtaleConstantRing T (P.finiteReductionSetting m hm).Ring)
        ((P.finiteReductionSetting m hm).finiteTensorLine T (Int.ofNat (j + 1)))
        ((P.finiteReductionSetting m hm).finiteTensorFirstLine T) U xB yB)) ∧
  ∀ (j : ℕ) (U : T.ProEtᵒᵖ)
      (φ : (P.finiteTensorLine T (Int.negSucc j)).val.obj U)
      (x : (P.finiteTensorLine T (Int.ofNat (j + 1))).val.obj U)
      (φB : ((P.finiteReductionSetting m hm).finiteTensorLine T (Int.negSucc j)).val.obj U)
      (xB : ((P.finiteReductionSetting m hm).finiteTensorLine T
        (Int.ofNat (j + 1))).val.obj U),
    HEq (P.finiteTensorLineSectionMap m hm hmn T c (Int.negSucc j) U φ) φB →
    HEq (P.finiteTensorLineSectionMap m hm hmn T c (Int.ofNat (j + 1)) U x) xB →
    (φB.app (Opposite.op (Over.mk (𝟙 U.unop)))) xB =
      (proEtaleConstantRingMap (T := T) (P.finiteReductionRingHom m hm hmn)).hom.app U
        ((φ.app (Opposite.op (Over.mk (𝟙 U.unop)))) x)

/-- The same semilinear sheaf map in fixed-scalar coordinates, via the normalized
inverse realization/restriction square. Source: Stacks 00YV and 03DA
(blueprint: def-pur-finite-tensor-reduction-data). -/
def finiteTensorFixedLineMap (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) (c : P.FiniteTensorLineMaps m hm hmn T) (r : ℤ) :=
  (sfIntrinsicModuleEquivalence T P.Ring).inverse.map (c r) ≫
    (sfInverseRealizationRestriction T (P.finiteReductionRingHom m hm hmn)).hom.app
      ((P.finiteReductionSetting m hm).finiteTensorLine T r)

/-- The actual adjunction and single-complex transpose values of finite signed reduction.
The values are constructed from the same fixed sheaf map and exact-restriction comparison.
Source: Stacks 06YY; blueprint proof Steps 3--5
(blueprint: def-pur-finite-tensor-reduction-data). -/
@[irreducible] def finiteTensorLineComparisonData (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u}) :
    TransposedFamilyData (P.finiteTensorReduction m hm hmn T)
      (ProEtale.SupportedEtaleTensorOrigin.fixedRestriction
        (P.finiteReductionRingHom m hm hmn) T)
      (P.finiteTensorFixedLine T)
      ((P.finiteReductionSetting m hm).finiteTensorFixedLine T)
      (P.FiniteTensorLineMaps m hm hmn T) where
  adjunction := P.finiteTensorAdjunction m hm hmn T
  valueType := fun _ ↦ _
  value := fun c r ↦
    (_root_.DerivedCategory.singleFunctor.{u + 1} _ 0).map
      (P.finiteTensorFixedLineMap m hm hmn T c r) ≫
    (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 1}
      (sfFixedRestriction.{u, u + 1, u + 1} T
        (P.finiteReductionRingHom m hm hmn)) 0).inv.app
      ((sfIntrinsicModuleEquivalence T (P.finiteReductionSetting m hm).Ring).inverse.obj
        ((P.finiteReductionSetting m hm).finiteTensorLine T r))

/-- Adjoint transpose on single complexes specifies the derived line comparison.
This excludes an arbitrary isomorphism of its two endpoints. The single-complex
comparison uses the same localization universes as the scalar adjunction.
Source: Stacks 06YY, blueprint proof Steps 3--4
(blueprint: def-pur-finite-tensor-reduction-data). -/
def FiniteTensorLineComparisonNormalized (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) (c : P.FiniteTensorLineMaps m hm hmn T)
    (b : ∀ r : ℤ, (P.finiteTensorReduction m hm hmn T).obj (P.finiteTensorFixedLine T r) ≅
      (P.finiteReductionSetting m hm).finiteTensorFixedLine T r) : Prop :=
  (P.finiteTensorLineComparisonData m hm hmn T).Normalized c b

/-- The native total-complex scalar-first tensor map before any coefficient quotient.
Its formula on a homogeneous summand is b tensor (x tensor y) sent to
(b tensor x) tensor (1 tensor y). Source: Stacks 07A4 and 0FPT
(blueprint: def-pur-finite-tensor-reduction-data). -/
@[irreducible] def finiteTensorCochainComparison {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (C D : CochainComplex (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    ((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj (C ⊗ D) ⟶
      ((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj C ⊗
        ((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj D :=
  (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
    (ProEtale.sheafExtendScalars φ T)).app C).app D)

end WeilConjectures.PurityFiniteSetting
