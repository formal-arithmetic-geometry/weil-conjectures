/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantCtf
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleUnit
import WeilConjectures.AlgebraicGeometry.Finite.FiniteIntrinsicDirectTensorComparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The section invariant in intrinsic finite-coefficient coordinates

Source: blueprint master, sec-smooth-purity/sk-def-purity-conv/def-pur-section-invariant.md
(blueprint: def-pur-section-invariant).

This equivalent interface uses the canonical constant-ring realization and the
published finite exceptional functor. It avoids mixing the retired pro-etale
pullback API with the finite-coefficient API. The data remain Ls* Rg! A_B.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MonoidalCategory

namespace WeilConjectures.PurityFiniteSetting

/-- The original site fits its object universe, with no extra scalar universe to infer.
Source: small pro-etale site convention (blueprint: def-pur-section-invariant). -/
instance (priority := 2000) intrinsicSiteSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} T.ProEt

/-- Finiteness of the actual positive coefficient quotient, by the published theorem.
Source: finite coefficient convention (blueprint: def-pur-section-invariant). -/
instance intrinsicCoefficientFinite (P : PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- The constant coefficient object in degree zero in the recorded intrinsic category.
Source: section-invariant definition, Lambda_B (blueprint: def-pur-section-invariant). -/
def intrinsicCoefficientUnit (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    proEtaleDerivedCategory T P.Ring :=
  (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit _)

/-- Actual exceptional image of the coefficient unit, using the specified etale adjoint
and the two canonical site comparisons. Source: omega_g in the section-invariant definition
(blueprint: def-pur-section-invariant). -/
def intrinsicDualizing (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g] : proEtaleDerivedCategory V P.Ring :=
  (ProEtale.sfFiniteExceptional P.Ring (HasCompactification.compactification g)).obj
    (P.intrinsicCoefficientUnit B)

/-- The actual derived pullback Ls* Rg! A_B, with no choice of an orientation.
Source: section-invariant displayed definition (blueprint: def-pur-section-invariant). -/
def sectionInvariantIntrinsic (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g] (s : B ⟶ V) :
    proEtaleDerivedCategory B P.Ring :=
  (Scheme.sfIntrinsicDerivedPullback P.Ring s).obj (P.intrinsicDualizing g)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
attribute [local irreducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option synthInstance.maxSize 4096 in
private noncomputable def comparison_unit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (n : ℕ) :
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison T
      (Padic.coefficientExtensionRing l E (n + 1))).obj (𝟙_ _) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E T n)) := by
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite B := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let A := ModuleCat.{u + 1} (ULift.{u + 1} B)
  let ν := ProEtale.comparisonUpperStar A T
  let R := ProEtale.finiteCoefficientIntrinsicRealization T B
  let F := ProEtale.finiteCoefficientIntrinsicComparison T B
  let e : F.obj (𝟙_ _) ≅ SheafOfModules.unit (integralCoefficientSheaf l E T n) := by
    change R.obj (ν.obj (𝟙_ _)) ≅ _
    exact R.mapIso ((Functor.Monoidal.εIso ν).symm ≪≫
      (Functor.Monoidal.εIso (constantSheaf (ProEt.topology T) A)).symm) ≪≫
      proEtaleConstantModuleUnit T B
  change F.mapDerivedCategory.obj (𝟙_ _) ≅ _
  exact F.mapDerivedCategory.mapIso (Etale.singleFunctorObjUnitIso A T).symm ≪≫
    (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option synthInstance.maxSize 4096 in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option synthInstance.maxSize 4096 in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option synthInstance.maxSize 4096 in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option synthInstance.maxSize 4096 in
private noncomputable def exceptional_origin_iso (P : PurityFiniteSetting.{u})
    [Finite P.Ring] (X Y : Scheme.{u})
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (G : Etale.DerivedCategoryModule P.Coefficient Y)
    (hG : _root_.DerivedCategory.TStructure.t.plus G)
    (K : proEtaleDerivedCategory Y P.Ring)
    (e : K ≅ (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y P.Ring).obj G) :
    (ProEtale.sfFiniteExceptional P.Ring (HasCompactification.compactification f)).obj K ≅
      (ProEtale.finiteCoefficientIntrinsicDerivedComparison X P.Ring).obj
        ((Etale.rightDerivedUpperShriek P.Coefficient f).obj G) := by
  let E := ProEtale.finiteCoefficientIntrinsicRealization Y P.Ring
  have : E.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact
    Y P.Ring).1
  have hE : E.Additive := ProEtale.finiteCoefficientIntrinsicRealization_additive Y P.Ring
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  let eComp := @Functor.mapDerivedCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ ν E
    inferInstance hE inferInstance inferInstance
    (ProEtale.finiteCoefficientIntrinsicRealization_exact Y P.Ring).2.2.1
    (ProEtale.finiteCoefficientIntrinsicRealization_exact Y P.Ring).2.2.2
  have : E.asEquivalence.functor.Additive :=
    ProEtale.finiteCoefficientIntrinsicRealization_additive Y P.Ring
  have : E.asEquivalence.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  let Rν := (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor
  let F := Etale.rightDerivedUpperShriek P.Coefficient f
  let e₁ : E.asEquivalence.inverse.mapDerivedCategory.obj K ≅
      ν.mapDerivedCategory.obj G :=
    E.asEquivalence.inverse.mapDerivedCategory.mapIso e ≪≫
    E.asEquivalence.inverse.mapDerivedCategory.mapIso
      (eComp.app G) ≪≫
    E.asEquivalence.mapDerivedCategory.unitIso.symm.app _
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} P.Coefficient) Y G hG
  let e₂ : Rν.obj (ν.mapDerivedCategory.obj G) ≅ G :=
    (asIso ((ProEtale.derivedComparisonAdjunction
      (ModuleCat.{u + 1} P.Coefficient) Y).unit.app G)).symm
  let νX := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X
  let EX := (sfIntrinsicModuleEquivalence X P.Ring).functor
  have hEX : EX.Additive := sfIntrinsicModuleEquivalence_functor_additive P.Ring X
  let c := @Functor.mapDerivedCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ νX EX
    inferInstance hEX inferInstance inferInstance
    (ProEtale.finiteCoefficientIntrinsicRealization_exact X P.Ring).2.2.1
    (ProEtale.finiteCoefficientIntrinsicRealization_exact X P.Ring).2.2.2
  exact EX.mapDerivedCategory.mapIso
      (νX.mapDerivedCategory.mapIso (F.mapIso (Rν.mapIso e₁ ≪≫ e₂))) ≪≫
    c.symm.app _

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option synthInstance.maxSize 4096 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
/-- Nagata supplies the compactification from the source hypotheses, with no added
exceptional-adjoint condition. Source: section-invariant finite-type setting
(blueprint: def-pur-section-invariant).
Proof: B is Noetherian since it is finite type over a field. The separated finite-type
map g therefore admits a compactification by Nagata. Smoothness in particular supplies
local finite type; quasi-compactness supplies finite type. -/
theorem sectionCompactifiable (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    HasCompactification g := by
  exact (P.finiteComparedCompactification g aB).hasCompactification

/-- The section invariant on precisely the finite-type domain of the source.
Compactifiability is a consequence, rather than an additional assumption.
Source: displayed definition C(g,s) (blueprint: def-pur-section-invariant). -/
def sectionInvariantFinite (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    proEtaleDerivedCategory B P.Ring :=
  let _ := hs
  letI := P.sectionCompactifiable g aB
  P.sectionInvariantIntrinsic g s

end WeilConjectures.PurityFiniteSetting
