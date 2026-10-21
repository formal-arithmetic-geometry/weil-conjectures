/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.Paper.PurityFrameKummer
public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.SupportLongExact
public import Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare

import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
import Sheaf.Paper.ComparisonPullbackExact
public import Sheaf.Paper.SupportedCup
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.ClosedSupportHom
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Linear.Yoneda
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.CategoryTheory.ExtExactFunctorCocycle
import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.Paper.ShiftedTensorMorphismCalculus
import Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.Paper.SupportedCohomologyHom
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor

/-!
# Pullback and symmetry of supported Kummer cup products

Source: Stacks Project, Tags 0FPL, 0FPM, 09XP, 03PL and 0G78; blueprint
main-20261015, lem-pur-frame-independence, unit multiples, permutations and shears
(blueprint: lem-pur-supported-cup-functoriality).

The Boolean site parameter is false for the small etale site and true for the
small pro-etale site. All constructions use the published sites, coefficients,
Kummer classes, exact inverse images and derived tensors.

## Main definitions and statement

* `functorialCupPullback`: the canonically normalized supported pullback.
* `functorialCup`: the prescribed tensor-morphism cup product on either site.
* `FunctorialCupAlgebraLaws`, `FunctorialCupLocalizationLaws`, and
  `FunctorialCupComparisonLaws`: the clauses of the statement.
* `supportedCupFunctoriality`: all these clauses for both sites.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u c v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

set_option backward.isDefEq.respectTransparency true in
private theorem functorialSingleTensor_isIso {C : Type c} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [hD : HasDerivedCategory.{v} C]
    [HasColimitsOfSize.{0, 0} C] [hM : MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C]
    [hB : BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] (L M : C) (hL : ObjectProperty.flat L) :
    IsIso (ProEtale.cupSingleTensorMap L M) := by
  let K := (HomologicalComplex.single C (.up ℤ) 0).obj L
  let T := (HomologicalComplex.single C (.up ℤ) 0).obj M
  let H := HomotopyCategory.quotient C (.up ℤ)
  have hK : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat (H.obj K) :=
    (HomotopyCategory.kFlat_quotient_obj_iff K).2
      ((CochainComplex.kFlat_single_obj_iff_flat L 0).2 hL)
  have := DerivedCategory.isIso_μ_Qh_of_kFlat (H.obj K) (H.obj T) hK
  have : IsIso (Functor.LaxMonoidal.μ (H ⋙ DerivedCategory.Qh) K T) := by
    rw [Functor.LaxMonoidal.comp_μ]
    infer_instance
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q K T) := by
    change IsIso (tensorHom _ _ ≫
      Functor.LaxMonoidal.μ (H ⋙ DerivedCategory.Qh) K T ≫ _)
    infer_instance
  dsimp only [K, T] at this
  unfold ProEtale.cupSingleTensorMap
  have hμ : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
      ((HomologicalComplex.single C (.up ℤ) 0).obj L)
      ((HomologicalComplex.single C (.up ℤ) 0).obj M)) := this
  have hmap : IsIso (DerivedCategory.Q.map
      ((((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) L).app
          ((HomologicalComplex.single C (.up ℤ) 0).obj M)) ≪≫
        ((HomologicalComplex.singleMapHomologicalComplex (tensorLeft L) (.up ℤ) 0).app M)).hom)) :=
    inferInstance
  have ht : IsIso (tensorIso ((DerivedCategory.singleFunctorIsoCompQ C 0).app L)
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app M)).hom := inferInstance
  have hi : IsIso ((DerivedCategory.singleFunctorIsoCompQ C 0).app (L ⊗ M)).inv :=
    inferInstance
  exact IsIso.comp_isIso' ht (IsIso.comp_isIso' hμ (IsIso.comp_isIso' hmap hi))

set_option backward.isDefEq.respectTransparency true in
private theorem functorialDerivedCoefficient_isIso {C : Type c} [Category.{v} C]
    [Abelian C] [IsGrothendieckAbelian.{v} C] [hD : HasDerivedCategory.{v} C]
    [HasColimitsOfSize.{0, 0} C] [hM : MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [hB : BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    {L M N : C} (μ : L ⊗ M ⟶ N) [hμ : IsIso μ] (hL : ObjectProperty.flat L) :
    IsIso (ProEtale.cupDerivedCoefficientMap μ) := by
  have h := functorialSingleTensor_isIso L M hL
  unfold ProEtale.cupDerivedCoefficientMap
  exact IsIso.comp_isIso' h (Functor.map_isIso _ μ)


set_option backward.isDefEq.respectTransparency true in
private theorem functorialDerivedPair_isIso {C : Type c} [hCat : Category.{v} C]
    [hAb : Abelian C] [IsGrothendieckAbelian.{v} C] [hD : HasDerivedCategory.{v} C]
    [HasColimitsOfSize.{0, 0} C] [hM : MonoidalCategory C] [hMP : MonoidalPreadditive C]
    [hClosed : MonoidalClosed C] [hB : BraidedCategory C]
    [hFlat : Abelian.HasFunctorialFlatResolution C]
    (p : Σ m : MonoidalCategory (DerivedCategory C),
      letI := m
      (DerivedCategory.Q (C := C)).LaxMonoidal)
    (e : p = ⟨inferInstance, inferInstance⟩)
    {L M N : C} (μ : L ⊗ M ⟶ N) [hμ : IsIso μ] (hL : ObjectProperty.flat L) :
    letI := p.1
    letI := p.2
    IsIso (ProEtale.cupDerivedCoefficientMap μ) := by
  subst p
  exact functorialDerivedCoefficient_isIso μ hL

/-- The two existing sheaf categories. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
abbrev functorialCupSheaves (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :=
  match pro with
  | false => Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
  | true => Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)

/-- The existing category structure, by cases on the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupCategory (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    Category.{u + 1} (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance

/-- The existing abelian structure. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupAbelian (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    Abelian (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance

/-- The existing small localization. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupHasDerived (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : HasDerivedCategory.{u + 1} (P.functorialCupSheaves pro X) := by
  cases pro <;> infer_instance

/-- The existing derived category, with its localization shared explicitly.
Source: supported tensor construction (blueprint: lem-pur-supported-cup-functoriality). -/
abbrev FunctorialCupDerived (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :=
  @DerivedCategory (P.functorialCupSheaves pro X) _ _ (P.functorialCupHasDerived pro X)

/-- The existing finite constant module. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupConstant (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    P.functorialCupSheaves pro X :=
  match pro with
  | false => P.constantEtale X
  | true => P.constant X

/-- The published comparison inverse image, with its actual exact structure.
Source: Stacks 099R (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupComparisonFunctor (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    P.functorialCupSheaves false X ⥤ P.functorialCupSheaves true X :=
  ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X

/-- Additivity of the same exact site comparison, with selected-site endpoints.
Source: finite site comparison (blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupComparisonFunctor_additive (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) : (P.functorialCupComparisonFunctor X).Additive :=
  inferInstanceAs ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).Additive)

/-- Left exactness of the same canonical comparison.
Source: finite site comparison (blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupComparisonFunctor_limits (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) : PreservesFiniteLimits (P.functorialCupComparisonFunctor X) :=
  inferInstanceAs (PreservesFiniteLimits
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X))

/-- Right exactness of the same canonical comparison.
Source: finite site comparison (blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupComparisonFunctor_colimits (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) : PreservesFiniteColimits (P.functorialCupComparisonFunctor X) :=
  inferInstanceAs (PreservesFiniteColimits
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X))

/-- The existing strong monoidal structure of the canonical site comparison.
Source: finite site comparison (blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupComparisonFunctor_monoidal (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) : (P.functorialCupComparisonFunctor X).Monoidal :=
  inferInstanceAs ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).Monoidal)

/-- The signed finite Tate sheaf at the actual annihilator ell^n. Source: the
arbitrary-index Kummer prescription in def-pur-frame-class
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupTwist (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) (r : ℤ) : P.functorialCupSheaves pro X :=
  match pro with
  | false => Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
      P.diagonalExponent_annihilates r
  | true => (P.functorialCupComparisonFunctor X).obj
      (Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
        P.diagonalExponent_annihilates r)

/-- The existing degree-zero embedding. Source: supported tensor construction
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupSingle (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :=
  @DerivedCategory.singleFunctor (P.functorialCupSheaves pro X) _ _
    (P.functorialCupHasDerived pro X) 0

/-- The actual underived direct image of constants from the closed support.
Source: def-pur-supported-cup, supported-Hom model
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupSource (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) : P.functorialCupSheaves pro X :=
  match pro with
  | false => (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale C)
  | true => (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant C)

/-- Restriction of local constants, exactly the coefficient map of the supported cup.
Source: def-pur-supported-cup and the etale coefficient lemma
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupRestriction (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    P.functorialCupConstant pro X ⟶ P.functorialCupSource pro i :=
  match pro with
  | false => Etale.closedConstantSectionMap P.Coefficient i
  | true => ProEtale.cupCoefficientRestriction P i

/-- Supported cohomology in the published Hom model, for arbitrary integer degrees.
Source: lem-pur-supported-hom and lem-amb-closed-support-hom
(blueprint: lem-pur-supported-cup-functoriality). -/
abbrev FunctorialCupH (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) (a r : ℤ) :=
  (P.functorialCupSingle pro X).obj (P.functorialCupSource pro i) ⟶
    ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r))⟦a⟧

/-- The actual exact inverse image of fixed-scalar modules. Source: Stacks 03Q1
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupInverseImage (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) :
    P.functorialCupSheaves pro X ⥤ P.functorialCupSheaves pro Y :=
  match pro with
  | false => Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v
  | true => ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v

/-- Additivity of the existing inverse image. Source: Stacks 03Q1
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupInverseImage_additive (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) : (P.functorialCupInverseImage pro v).Additive := by
  cases pro <;> dsimp [functorialCupInverseImage] <;> infer_instance

/-- Left exactness of the existing inverse image. Source: Stacks 03Q1
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupInverseImage_limits (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) :
    PreservesFiniteLimits (P.functorialCupInverseImage pro v) := by
  cases pro <;> dsimp [functorialCupInverseImage] <;> infer_instance

/-- Right exactness of the existing inverse image. Source: Stacks 03Q1
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupInverseImage_colimits (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) :
    PreservesFiniteColimits (P.functorialCupInverseImage pro v) := by
  cases pro <;> dsimp [functorialCupInverseImage] <;> infer_instance


/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupGrothendieck (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance

/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupMonoidal (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    MonoidalCategory (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance

/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupMonoidalPreadditive (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) :
    MonoidalPreadditive (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance

/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupSymmetric (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    SymmetricCategory (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance

/-- The published sheaf structure, selected by the site. Source: purity conventions
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupClosed (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    MonoidalClosed (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance

/-- The published functorial flat resolutions, selected by the site.
Source: K-flat tensor construction (blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupFlatResolutions (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : Abelian.HasFunctorialFlatResolution (P.functorialCupSheaves pro X) := by
  cases pro <;> infer_instance

/-- The existing derived monoidal structure. Source: supported tensor construction
(blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupDerivedMonoidal (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) : MonoidalCategory (P.FunctorialCupDerived pro X) := inferInstance

/-- The coefficient multiplication fixed by restriction and local scalar multiplication.
Source: def-pur-supported-cup and its etale analogue
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupMultiplication (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    P.functorialCupSource pro i ⊗ P.functorialCupSource pro j ⟶
      P.functorialCupSource pro (ProEtale.cupIntersection i j) :=
  match pro with
  | false => Etale.closedConstantTensorMap P.Coefficient i j
  | true => ProEtale.cupCoefficientMap P i j

/-- The signed product family together with the equations that uniquely normalize it.
All data are projected from the published signed-twist theorem, with the unit,
positive-power, evaluation, associativity and symmetry equations retained.
Source: Stacks 03PK, 07A4 (blueprint: lem-pur-supported-cup-functoriality). -/
structure FunctorialCupTwistProducts (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) where
  product : ∀ (X : Scheme.{u}), IsUnit (m : Γ(X, ⊤)) → ∀ r s : ℤ,
    Scheme.finiteEtaleTateSheaf A m X hA r ⊗ Scheme.finiteEtaleTateSheaf A m X hA s ≅
      Scheme.finiteEtaleTateSheaf A m X hA (r + s)
  left_unit : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (r : ℤ),
    product X hX 0 r = λ_ (Scheme.finiteEtaleTateSheaf A m X hA r) ≪≫
      eqToIso (congrArg (Scheme.finiteEtaleTateSheaf A m X hA) (zero_add r).symm)
  right_unit : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (r : ℤ),
    product X hX r 0 = ρ_ (Scheme.finiteEtaleTateSheaf A m X hA r) ≪≫
      eqToIso (congrArg (Scheme.finiteEtaleTateSheaf A m X hA) (add_zero r).symm)
  positive : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (n : ℕ),
    product X hX (.ofNat (n + 1)) 1 = Iso.refl _
  associativity : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (r s t : ℤ),
    (product X hX r s).hom ▷ Scheme.finiteEtaleTateSheaf A m X hA t ≫
        (product X hX (r + s) t).hom =
      (α_ (Scheme.finiteEtaleTateSheaf A m X hA r)
        (Scheme.finiteEtaleTateSheaf A m X hA s)
        (Scheme.finiteEtaleTateSheaf A m X hA t)).hom ≫
      Scheme.finiteEtaleTateSheaf A m X hA r ◁ (product X hX s t).hom ≫
        (product X hX r (s + t)).hom ≫
          eqToHom (congrArg (Scheme.finiteEtaleTateSheaf A m X hA) (add_assoc r s t).symm)
  symmetry : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (r s : ℤ),
    (β_ (Scheme.finiteEtaleTateSheaf A m X hA r)
        (Scheme.finiteEtaleTateSheaf A m X hA s)).hom ≫
        (product X hX s r).hom ≫
        eqToHom (congrArg (Scheme.finiteEtaleTateSheaf A m X hA) (add_comm s r)) =
      (product X hX r s).hom
  evaluation : ∀ (X : Scheme.{u}) (hX : IsUnit (m : Γ(X, ⊤))) (n : ℕ),
    (product X hX (.ofNat (n + 1)) (.negSucc n)).hom ≫
        eqToHom (congrArg (Scheme.finiteEtaleTateSheaf A m X hA)
          (add_neg_cancel (Int.ofNat (n + 1)))) =
      (ihom.ev (Scheme.finiteEtaleTateSheaf A m X hA (.ofNat (n + 1)))).app
        (Scheme.finiteEtaleTateSheaf A m X hA 0)

/-- Extract one coherent normalized family, retaining its characterizing equations.
Source: lem-asd-etale-finite-twist-pullback
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupTwistProducts (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) : FunctorialCupTwistProducts A m hA :=
  Classical.choice ((Scheme.etaleFiniteTwistPullback A m hm hA).elim fun _ hr ↦
    hr.elim fun _ hc ↦ hc.elim fun p hp ↦
      ⟨{ product := p
         left_unit := hp.2.2.2.2.2.2.2.2.1
         right_unit := hp.2.2.2.2.2.2.2.2.2.1
         positive := hp.2.2.2.2.2.2.2.2.2.2.1
         associativity := hp.2.2.2.2.2.2.2.2.2.2.2.1
         symmetry := hp.2.2.2.2.2.2.2.2.2.2.2.2.1
         evaluation := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1 }⟩)

/-- The canonical signed product, projected from its normalized family.
Source: Stacks 03PK, 07A4 (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupTwistProductGeneral (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) (X : Scheme.{u})
    (hX : IsUnit (m : Γ(X, ⊤))) (r s : ℤ) :=
  (functorialCupTwistProducts A m hm hA).product X hX r s

/-- Normalized etale twist multiplication from the signed-root prescription.
This selects the witness together with its generator, evaluation and tensor
normalizations, never an uncharacterized isomorphism. Source: Stacks 03PK and 07A4,
lem-asd-etale-finite-twist-pullback
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupEtaleTwistProduct (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (r s : ℤ) :=
  functorialCupTwistProductGeneral P.Coefficient P.diagonalExponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
    P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit a) r s

/-- The same normalized twist multiplication, transported through the canonical
strong monoidal site comparison on the pro-etale site. Source: Stacks 07A4
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupTwistProduct (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (r s : ℤ) :
    P.functorialCupTwist pro X r ⊗ P.functorialCupTwist pro X s ≅
      P.functorialCupTwist pro X (r + s) :=
  match pro with
  | false => P.functorialCupEtaleTwistProduct X a r s
  | true => (asIso (Functor.OplaxMonoidal.δ
      (P.functorialCupComparisonFunctor X)
        (P.functorialCupTwist false X r) (P.functorialCupTwist false X s))).symm ≪≫
      (P.functorialCupComparisonFunctor X).mapIso
        (P.functorialCupEtaleTwistProduct X a r s)

section CoefficientProof

set_option backward.isDefEq.respectTransparency true

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupHasDerived functorialCupDerivedMonoidal
  functorialCupMonoidal functorialCupAbelian functorialCupCategory
  functorialCupMonoidalPreadditive functorialCupSymmetric functorialCupClosed
  functorialCupFlatResolutions functorialCupMultiplication functorialCupSource

private abbrev selectedLaxQ (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    letI := P.functorialCupDerivedMonoidal pro X
    (DerivedCategory.Q (C := P.functorialCupSheaves pro X)).LaxMonoidal := inferInstance

/-- Flat supported coefficients make the canonical degree-zero tensor comparison
invertible. Source: def-pur-supported-cup and lem-pur-etale-closed-constant-tensor
(blueprint: lem-pur-supported-cup-functoriality).
Proof: on the etale site geometric stalks are A or zero and multiplication is the
identity on the common support. On the pro-etale site use the quotient/idempotent
calculation in def-pur-supported-cup. In both cases the flat degree-zero sheaves
are their own K-flat models, so the canonical localization comparison is invertible. -/
theorem functorialCupCoefficient_isIso (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    IsIso (ProEtale.cupDerivedCoefficientMap (hD := P.functorialCupHasDerived pro X)
      (hDM := P.functorialCupDerivedMonoidal pro X) (P.functorialCupMultiplication pro i j)) := by
  cases pro with
  | false =>
    have h := Etale.closedConstantTensor P.Coefficient X i j j (𝟙 X)
    have hμ : IsIso (P.functorialCupMultiplication false i j) :=
      h.2.2.2.2.2.2.2.2.2.1
    have hcoeff := functorialDerivedPair_isIso
      (C := P.functorialCupSheaves false X)
      (hCat := P.functorialCupCategory false X) (hAb := P.functorialCupAbelian false X)
      (hMP := P.functorialCupMonoidalPreadditive false X)
      (hClosed := P.functorialCupClosed false X)
      (hFlat := P.functorialCupFlatResolutions false X)
      (hD := P.functorialCupHasDerived false X)
      (hM := P.functorialCupMonoidal false X)
      (hB := (P.functorialCupSymmetric false X).toBraidedCategory)
      (L := P.functorialCupSource false i) (M := P.functorialCupSource false j)
      (N := P.functorialCupSource false (ProEtale.cupIntersection i j))
      (hμ := hμ) ⟨P.functorialCupDerivedMonoidal false X, selectedLaxQ P false X⟩ rfl
      (P.functorialCupMultiplication false i j) (Etale.closedConstantModule_flat _ i)
    exact hcoeff
  | true =>
    have hμ : IsIso (P.functorialCupMultiplication true i j) :=
      ProEtale.cupCoefficientMap_isIso P i j
    have hcoeff := functorialDerivedPair_isIso
      (C := P.functorialCupSheaves true X)
      (hCat := P.functorialCupCategory true X) (hAb := P.functorialCupAbelian true X)
      (hMP := P.functorialCupMonoidalPreadditive true X)
      (hClosed := P.functorialCupClosed true X)
      (hFlat := P.functorialCupFlatResolutions true X)
      (hD := P.functorialCupHasDerived true X)
      (hM := P.functorialCupMonoidal true X)
      (hB := (P.functorialCupSymmetric true X).toBraidedCategory)
      (L := P.functorialCupSource true i) (M := P.functorialCupSource true j)
      (N := P.functorialCupSource true (ProEtale.cupIntersection i j))
      (hμ := hμ) ⟨P.functorialCupDerivedMonoidal true X, selectedLaxQ P true X⟩ rfl
      (P.functorialCupMultiplication true i j) (ProEtale.cupCoefficient_flat P i)
    exact hcoeff

end CoefficientProof

/-- The prescribed tensor-morphism supported product followed by multiplication
of the twist lines. For pro=true its first composite is the published supportedCup;
for pro=false it is its etale analogue, with exactly the same shift sign.
Source: def-pur-supported-cup, tensor-morphism formula
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCup (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
    (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
    (a b r s : ℤ) (α : P.FunctorialCupH pro i a r) (β : P.FunctorialCupH pro j b s) :
    P.FunctorialCupH pro (ProEtale.cupIntersection i j) (a + b) (r + s) :=
  ProEtale.cupComposite (hM := P.functorialCupDerivedMonoidal pro X)
    (ProEtale.cupDerivedCoefficientMap (hD := P.functorialCupHasDerived pro X)
      (hDM := P.functorialCupDerivedMonoidal pro X) (P.functorialCupMultiplication pro i j))
    (P.functorialCupCoefficient_isIso pro i j) a b α β ≫
      (ProEtale.cupSingleTensorMap (hD := P.functorialCupHasDerived pro X)
        (hDM := P.functorialCupDerivedMonoidal pro X)
          (P.functorialCupTwist pro X r) (P.functorialCupTwist pro X s) ≫
        (P.functorialCupSingle pro X).map (P.functorialCupTwistProduct pro X aX r s).hom)⟦a+b⟧'


/-- Canonical inverse image of the coefficient unit. Source: constant-sheaf adjunction
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupConstantPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) :
    (P.functorialCupInverseImage pro v).obj (P.functorialCupConstant pro X) ≅
      P.functorialCupConstant pro Y :=
  match pro with
  | false => (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) v).app
      (ModuleCat.of P.Coefficient P.Coefficient)
  | true => P.frameConstantPullback v

/-- The etale part of normalized signed-twist inverse image.
Source: Stacks 03Q1, 07A4 (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupEtaleTwistPullback (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (v : Y ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (r : ℤ) :
    (P.functorialCupInverseImage false v).obj (P.functorialCupTwist false X r) ≅
      P.functorialCupTwist false Y r :=
  Etale.p1DecompositionSheafPullback P.Coefficient P.diagonalExponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
    P.diagonalExponent_annihilates v (P.diagonalExponent_isUnit aX) r

/-- The same root-normalized inverse image on either site. Pro-etale inverse image
uses the canonical comparison mate. Source: Stacks 03Q1, 07A4
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupTwistPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (r : ℤ) :
    (P.functorialCupInverseImage pro v).obj (P.functorialCupTwist pro X r) ≅
      P.functorialCupTwist pro Y r :=
  match pro with
  | false => P.functorialCupEtaleTwistPullback v aX r
  | true => (ProEtale.comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) v).app (P.functorialCupTwist false X r) ≪≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).mapIso
        (P.functorialCupEtaleTwistPullback v aX r)

section ClosedSupportProof

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupCategory functorialCupAbelian
  functorialCupMonoidal functorialCupSymmetric functorialCupClosed
  constant constantEtale functorialCupConstant functorialCupComparisonFunctor
  functorialCupSource functorialCupRestriction functorialCupInverseImage
  functorialCupConstantPullback

section ClosedSourceNormalization

open ProEtale
universe c1 c2 c3 c4 v1 v2 v3 v4
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false in
private theorem cupRestriction_eq_laxUnit (P : WeilConjectures.PurityFiniteSetting.{u})
    {D X : Scheme.{u}} (c : D ⟶ X) :
    cupCoefficientRestriction P c = (cupConstantIso P X).hom ≫
      Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} P.Coefficient) c) ≫
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) c).map (cupConstantIso P D).inv := by
  unfold cupCoefficientRestriction
  congr 1
  congr 1
  apply ((constantSheafAdj (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)
    (Scheme.ProEt.isTerminalMkId X)).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  exact (Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ c)
    (ModuleCat.{u + 1} P.Coefficient) (Scheme.ProEt.topology X)
    (Scheme.ProEt.topology D) (op (Scheme.ProEt.mk (𝟙 X)))).symm

set_option backward.defeqAttrib.useBackward true in
private theorem monoidal_mate
    {C : Type c1} {D : Type c2} {E : Type c3} {F : Type c4}
    [Category.{v1} C] [Category.{v2} D] [Category.{v3} E] [Category.{v4} F]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    [G.LaxMonoidal] [H.LaxMonoidal] [L₁.Monoidal] [L₂.Monoidal]
    [R₁.LaxMonoidal] [R₂.LaxMonoidal]
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [adj₁.IsMonoidal] [adj₂.IsMonoidal]
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) [NatTrans.IsMonoidal β] :
    NatTrans.IsMonoidal (TwoSquare.natTrans ((mateEquiv adj₁ adj₂).symm β)) := by
  change NatTrans.IsMonoidal (_ ≫ _ ≫ _ ≫ _ ≫ _ ≫ _ ≫ _ ≫ _ ≫ _)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem constant_iso_eta (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) :
    (cupConstantIso P X).hom = Functor.OplaxMonoidal.η
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X) := by
  unfold cupConstantIso comparisonUpperStarConstantSheafIso
  apply (((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
    (Scheme.Etale.isTerminalMkId X)).comp
      (comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) X)).ofNatIsoRight
    ((Scheme.toProEt X).sheafPushforwardContinuousCompSheafSectionsObjIso
      (ModuleCat.{u + 1} P.Coefficient) X.smallEtaleTopology
      (Scheme.ProEt.topology X) (op (Scheme.Etale.mk (𝟙 X))))).homEquiv _ _ |>.injective
  simp only [Iso.app_hom]
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  change (constantSheafAdj (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient) (Scheme.ProEt.isTerminalMkId X)).unit.app
      (𝟙_ (ModuleCat.{u + 1} P.Coefficient)) =
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
      (Scheme.Etale.isTerminalMkId X)).unit.app _ ≫
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)).obj
      (op (Scheme.Etale.mk (𝟙 X)))).map
      ((comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) X).unit.app _ ≫
        (comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) X).map
          (Functor.OplaxMonoidal.η
            (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X))) ≫
    ((Scheme.toProEt X).sheafPushforwardContinuousCompSheafSectionsObjIso
      (ModuleCat.{u + 1} P.Coefficient) X.smallEtaleTopology
      (Scheme.ProEt.topology X) (op (Scheme.Etale.mk (𝟙 X)))).hom.app _
  erw [Adjunction.unit_app_unit_comp_map_η]
  have hp : (constantSheafAdj (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient) (Scheme.ProEt.isTerminalMkId X)).unit.app
      (𝟙_ (ModuleCat.{u + 1} P.Coefficient)) =
      (Functor.LaxMonoidal.ε (sheafToPresheaf _ _)).app
        (op (Scheme.ProEt.mk (𝟙 X))) := by
    simp only [constantSheafAdj, Adjunction.rightAdjointLaxMonoidal_ε]
    rw [Adjunction.homEquiv_unit]
    have : Functor.OplaxMonoidal.η
      (presheafToSheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} P.Coefficient)) = 𝟙 _ := rfl
    simp [this]
    rfl
  have he : (constantSheafAdj X.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient) (Scheme.Etale.isTerminalMkId X)).unit.app
      (𝟙_ (ModuleCat.{u + 1} P.Coefficient)) =
      (Functor.LaxMonoidal.ε (sheafToPresheaf _ _)).app
        (op (Scheme.Etale.mk (𝟙 X))) := by
    simp only [constantSheafAdj, Adjunction.rightAdjointLaxMonoidal_ε]
    rw [Adjunction.homEquiv_unit]
    have : Functor.OplaxMonoidal.η
      (presheafToSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)) = 𝟙 _ := rfl
    simp [this]
    rfl
  rw [hp, he]
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc]
  rfl
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem comparison_monoidal (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    NatTrans.IsMonoidal
      (lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} P.Coefficient)) := by
  exact monoidal_mate
    (comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) Z)
    (comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) X)
    (lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} P.Coefficient)).inv


set_option backward.isDefEq.respectTransparency false in
private theorem comparison_restriction (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    cupCoefficientRestriction P i =
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
        (Functor.LaxMonoidal.ε (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i)) ≫
      (lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} P.Coefficient)).app
        (𝟙_ (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) := by
  have := comparison_monoidal P i
  have h := NatTrans.IsMonoidal.unit
    (τ := lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} P.Coefficient))
  simp only [Functor.LaxMonoidal.comp_ε, Category.assoc] at h
  have hi : (cupConstantIso P Z).inv =
      Functor.LaxMonoidal.ε (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Z) := by
    apply (cancel_mono (cupConstantIso P Z).hom).mp
    rw [Iso.inv_hom_id, constant_iso_eta, Functor.Monoidal.ε_η]
    rfl
  rw [cupRestriction_eq_laxUnit, constant_iso_eta, hi]
  apply (cancel_epi (Functor.LaxMonoidal.ε
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X))).mp
  simp only [Functor.Monoidal.ε_η_assoc]
  exact h.symm

end ClosedSourceNormalization

section EtaleSourceNormalization

open Etale

private theorem transition_unit (A : Type (u + 1)) [CommRing A]
    {V D X : Scheme.{u}} (p : V ⟶ D) (g : D ⟶ X) (h : V ⟶ X)
    (hp : p ≫ g = h) :
    Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} A) g) ≫
      constantModulePushforwardMap A (ModuleCat.of A A) g h p hp =
    Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} A) h) := by
  unfold constantModulePushforwardMap
  erw [upperStarConstantSheafIso_hom_app_tensorUnit (ModuleCat.{u + 1} A) p]
  erw [Adjunction.unit_app_unit_comp_map_η]
  exact (ε_lowerStar_comp p g h hp.symm).symm

private theorem section_unit (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    closedConstantSectionMap A i =
      Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} A) i) := by
  unfold closedConstantSectionMap
  erw [← ε_lowerStar_id]
  exact transition_unit A i (𝟙 X) i (by simp)

private theorem section_epi (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    Epi (closedConstantSectionMap A i) := by
  erw [section_unit A i]
  erw [← (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit_app_unit_comp_map_η]
  have : Epi ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app
      (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))) :=
    (shortExact_openClosedShortComplex (ModuleCat.{u + 1} A)
      i.openComplement.ι i
      (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      i.range_eq_compl_range_openComplement_ι).epi_g
  exact epi_comp _ _

end EtaleSourceNormalization

private theorem comparisonSource_normalized (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    ∃! b : (P.functorialCupComparisonFunctor X).obj
        (P.functorialCupSource false i) ≅ P.functorialCupSource true i,
      (P.functorialCupComparisonFunctor X).map
          (P.functorialCupRestriction false i) ≫ b.hom = P.functorialCupRestriction true i := by
  let F := P.functorialCupComparisonFunctor X
  have := section_epi P.Coefficient i
  have : Epi (F.map (P.functorialCupRestriction false i)) := F.map_epi _
  have := ProEtale.isIso_lowerStarComparisonUpperStarBaseChange i
    (ModuleCat.{u + 1} P.Coefficient)
  let e := asIso ((ProEtale.lowerStarComparisonUpperStarBaseChange i
    (ModuleCat.{u + 1} P.Coefficient)).app (P.constantEtale C))
  have he : F.map (P.functorialCupRestriction false i) ≫ e.hom =
      P.functorialCupRestriction true i := by
    change (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
      (Etale.closedConstantSectionMap P.Coefficient i) ≫ _ = _
    rw [section_unit]
    exact (comparison_restriction P i).symm
  refine ⟨e, he, ?_⟩
  intro b hb
  apply Iso.ext
  exact (cancel_epi (F.map (P.functorialCupRestriction false i))).1 (hb.trans he.symm)


section EtaleExchangeNormalization

open Etale
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem mate_symm_monoidal
    {V W V' W' : Type*} [Category V] [Category W] [Category V'] [Category W']
    [MonoidalCategory V] [MonoidalCategory W]
    [MonoidalCategory V'] [MonoidalCategory W']
    {L : V ⥤ W} {R : W ⥤ V} {L' : V' ⥤ W'} {R' : W' ⥤ V'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (F : V ⥤ V') (G : W ⥤ W')
    [L.Monoidal] [R.LaxMonoidal] [L'.Monoidal] [R'.LaxMonoidal]
    [F.LaxMonoidal] [G.LaxMonoidal] [adj.IsMonoidal] [adj'.IsMonoidal]
    (β : TwoSquare R G F R') [β.natTrans.IsMonoidal] :
    NatTrans.IsMonoidal ((mateEquiv adj adj').symm β).natTrans := by
  change NatTrans.IsMonoidal
    ((Functor.leftUnitor _).inv ≫
      Functor.whiskerRight adj.unit (F ⋙ L') ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Functor.associator _ _ _).hom _ ≫
      Functor.whiskerRight (Functor.whiskerLeft L β.natTrans) L' ≫
      Functor.whiskerRight (Functor.associator _ _ _).inv _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (L ⋙ G) adj'.counit ≫
      (Functor.rightUnitor _).hom)
  infer_instance

private theorem basechange_monoidal
    (A : Type (u + 1)) [CommRing A]
    {C' C X' X : Scheme.{u}} {q : C' ⟶ C} {r : C' ⟶ X'}
    {i : C ⟶ X} {v : X' ⟶ X} (sq : CommSq q r i v) :
    NatTrans.IsMonoidal (baseChangeMap (ModuleCat.{u + 1} A) sq) := by
  change NatTrans.IsMonoidal (baseChangeSquare (ModuleCat.{u + 1} A) sq).natTrans
  rw [baseChangeSquare_eq_mateEquiv_symm]
  have : NatTrans.IsMonoidal (squareLowerStarIso (ModuleCat.{u + 1} A) sq).hom := by
    dsimp only [squareLowerStarIso, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  exact mate_symm_monoidal _ _ _ _ _

private theorem etaleExchange_normalized (P : PurityFiniteSetting.{u})
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (sq : ChosenCartesianSquare g j i v) :
    ∃! b : (P.functorialCupInverseImage false v).obj (P.functorialCupSource false i) ≅
        P.functorialCupSource false j,
      (P.functorialCupInverseImage false v).map (P.functorialCupRestriction false i) ≫
          b.hom =
        (P.functorialCupConstantPullback false v).hom ≫
          P.functorialCupRestriction false j := by
  let B := ModuleCat.{u + 1} P.Coefficient
  have hs : IsPullback g j i v :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  let b := (baseChangeMap B sq.toCommSq).app (𝟙_ _) ≫
    (lowerStar B j).map (Functor.OplaxMonoidal.η (upperStar B g))
  have hBC := basechange_monoidal P.Coefficient sq.toCommSq
  have hb : (upperStar B v).map (Etale.closedConstantSectionMap P.Coefficient i) ≫ b =
      Functor.OplaxMonoidal.η (upperStar B v) ≫
        Etale.closedConstantSectionMap P.Coefficient j := by
    erw [section_unit, section_unit]
    apply (cancel_epi (Functor.LaxMonoidal.ε (upperStar B v))).1
    dsimp only [b]
    have hu := NatTrans.IsMonoidal.unit (τ := baseChangeMap B sq.toCommSq)
    dsimp only [Functor.LaxMonoidal.comp_ε] at hu
    simp only [Category.assoc] at hu ⊢
    rw [reassoc_of% hu]
    simp only [← Functor.map_comp, Functor.Monoidal.ε_η,
      Functor.Monoidal.ε_η_assoc]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have := isIso_baseChangeMap_of_isFinite B hs
  have : IsIso b := by dsimp only [b]; infer_instance
  have := section_epi P.Coefficient i
  have : Epi ((upperStar B v).map (Etale.closedConstantSectionMap P.Coefficient i)) :=
    (upperStar B v).map_epi _
  have he : (P.functorialCupInverseImage false v).map
        (P.functorialCupRestriction false i) ≫ (asIso b).hom =
      (P.functorialCupConstantPullback false v).hom ≫
        P.functorialCupRestriction false j := by
    change (upperStar B v).map (Etale.closedConstantSectionMap P.Coefficient i) ≫ b =
      (Scheme.upperStarConstantSheafIso B v).hom.app (𝟙_ B) ≫
        Etale.closedConstantSectionMap P.Coefficient j
    rw [upperStarConstantSheafIso_hom_app_tensorUnit]
    exact hb
  refine ⟨asIso b, he, ?_⟩
  intro e he'
  apply Iso.ext
  exact (cancel_epi ((upperStar B v).map
    (Etale.closedConstantSectionMap P.Coefficient i))).1 (he'.trans he.symm)

end EtaleExchangeNormalization

/-- Closed constant exchange is uniquely fixed by restriction of the unit.
Source: Stacks 03Q1 and 099V; supported functoriality, proof Steps 2 and 6
(blueprint: lem-pur-supported-cup-functoriality).
Proof: etale geometric stalks give A on the inverse-image closed subset and zero
elsewhere, so the section-normalized adjoint is invertible. For pro-etale objects
Y over X identify comparison inverse-image sections with etale sections on Y.
The same etale calculation and degree-zero comparison identify the closed source,
with identical local constants and restriction. This yields the asserted map on
both sites. Restriction from the constant unit is epic, so its displayed equation
makes the map unique. Nonreduced and empty closed supports require no modification. -/
theorem functorialCupExchange_existsUnique (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (_sq : ChosenCartesianSquare g j i v) :
    ∃! b : (P.functorialCupInverseImage pro v).obj (P.functorialCupSource pro i) ≅
        P.functorialCupSource pro j,
      (P.functorialCupInverseImage pro v).map (P.functorialCupRestriction pro i) ≫ b.hom =
        (P.functorialCupConstantPullback pro v).hom ≫ P.functorialCupRestriction pro j := by
  cases pro with
  | false => exact etaleExchange_normalized P i j v g _sq
  | true =>
    let FX := P.functorialCupComparisonFunctor X
    let FY := P.functorialCupComparisonFunctor Y
    let V := P.functorialCupInverseImage true v
    let U := P.functorialCupInverseImage false v
    let ei := (comparisonSource_normalized P i).choose
    let ej := (comparisonSource_normalized P j).choose
    have hi := (comparisonSource_normalized P i).choose_spec.1
    have hj := (comparisonSource_normalized P j).choose_spec.1
    change FX.map (P.functorialCupRestriction false i) ≫ ei.hom = _ at hi
    change FY.map (P.functorialCupRestriction false j) ≫ ej.hom = _ at hj
    let e := (etaleExchange_normalized P i j v g _sq).choose
    have he := (etaleExchange_normalized P i j v g _sq).choose_spec.1
    change U.map (P.functorialCupRestriction false i) ≫ e.hom = _ at he
    let τ := ProEtale.comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) v
    let b := V.mapIso ei.symm ≪≫ τ.app (P.functorialCupSource false i) ≪≫
      FY.mapIso e ≪≫ ej
    have hb : V.map (P.functorialCupRestriction true i) ≫ b.hom =
        (P.functorialCupConstantPullback true v).hom ≫
          P.functorialCupRestriction true j := by
      rw [← hi]
      change V.map (FX.map (P.functorialCupRestriction false i) ≫ ei.hom) ≫
        V.map ei.inv ≫ τ.hom.app _ ≫ FY.map e.hom ≫ ej.hom = _
      rw [V.map_comp]
      simp only [Category.assoc, ← V.map_comp_assoc, Iso.hom_inv_id,
        V.map_id, Category.id_comp]
      have hn := τ.hom.naturality (P.functorialCupRestriction false i)
      change V.map (FX.map (P.functorialCupRestriction false i)) ≫ τ.hom.app _ =
        τ.hom.app _ ≫ FY.map (U.map (P.functorialCupRestriction false i)) at hn
      rw [reassoc_of% hn]
      rw [← FY.map_comp_assoc, he, FY.map_comp]
      rw [Category.assoc, hj]
      simp only [functorialCupConstantPullback, frameConstantPullback, Iso.trans_hom,
        Functor.mapIso_hom, Iso.app_hom, Category.assoc]
      rfl
    have := section_epi P.Coefficient i
    have : Epi (FX.map (P.functorialCupRestriction false i)) := FX.map_epi _
    have hpi : Epi (P.functorialCupRestriction true i) := by
      rw [← hi]
      exact epi_comp _ _
    have : V.Additive := inferInstanceAs (P.functorialCupInverseImage true v).Additive
    have : PreservesFiniteColimits V :=
      inferInstanceAs (PreservesFiniteColimits (P.functorialCupInverseImage true v))
    have : V.PreservesEpimorphisms :=
      NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels V
    have : Epi (V.map (P.functorialCupRestriction true i)) := V.map_epi _
    refine ⟨b, hb, ?_⟩
    intro b' hb'
    apply Iso.ext
    exact (cancel_epi (V.map (P.functorialCupRestriction true i))).1 (hb'.trans hb.symm)

end ClosedSupportProof

/-- The uniquely normalized ordinary coefficient exchange; no purity exchange is used.
Source: Stacks 03Q1, supported functoriality formula
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupExchange (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (sq : ChosenCartesianSquare g j i v) :=
  (P.functorialCupExchange_existsUnique pro i j v g sq).choose

/-- Exact inverse image on derived Hom, precomposed by closed coefficient exchange
and followed by the normalized twist identification and canonical shift comparison.
This is the formula tau[a] v inverse(alpha) b inverse of proof Step 4.
Source: Stacks 0G78 and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
    (a r : ℤ) (α : P.FunctorialCupH pro i a r) : P.FunctorialCupH pro j a r :=
  (P.functorialCupSingle pro Y).map (P.functorialCupExchange pro i j v g sq).inv ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).inv.app
      (P.functorialCupSource pro i) ≫
    (P.functorialCupInverseImage pro v).mapDerivedCategory.map α ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategory.commShiftIso a).hom.app
      ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r)) ≫
    (((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).hom.app
        (P.functorialCupTwist pro X r) ≫
      (P.functorialCupSingle pro Y).map (P.functorialCupTwistPullback pro v aX r).hom)⟦a⟧'

section SupportMapProof

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupCategory functorialCupAbelian
  functorialCupMonoidal functorialCupSymmetric functorialCupClosed
  constant constantEtale functorialCupConstant functorialCupComparisonFunctor
  functorialCupSource functorialCupRestriction functorialCupInverseImage
  functorialCupConstantPullback

/-- Change of closed support over a fixed scheme, uniquely determined on local constants.
Source: supported functoriality, Steps 2 and 5
(blueprint: lem-pur-supported-cup-functoriality).
Proof: the map D to C over X restricts each locally constant section on C to D.
The sheaf map is A-linear and carries the restricted unit to the restricted unit.
The constant restriction onto the closed direct image is epic, proving uniqueness. -/
theorem functorialCupSupportMap_existsUnique (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (g : D ⟶ C) (_h : g ≫ i = j) :
    ∃! b : P.functorialCupSource pro i ⟶ P.functorialCupSource pro j,
      P.functorialCupRestriction pro i ≫ b = P.functorialCupRestriction pro j := by
  let t := Etale.constantModulePushforwardMap P.Coefficient
    (ModuleCat.of P.Coefficient P.Coefficient) i j g _h
  have ht : Etale.closedConstantSectionMap P.Coefficient i ≫ t =
      Etale.closedConstantSectionMap P.Coefficient j := by
    rw [section_unit, section_unit]
    exact transition_unit _ g i j _h
  have := section_epi P.Coefficient i
  cases pro with
  | false =>
    refine ⟨t, ht, ?_⟩
    intro b hb
    exact (cancel_epi (Etale.closedConstantSectionMap P.Coefficient i)).1 (hb.trans ht.symm)
  | true =>
    let F := P.functorialCupComparisonFunctor X
    let ei := (comparisonSource_normalized P i).choose
    let ej := (comparisonSource_normalized P j).choose
    have hi := (comparisonSource_normalized P i).choose_spec.1
    have hj := (comparisonSource_normalized P j).choose_spec.1
    change F.map (P.functorialCupRestriction false i) ≫ ei.hom = _ at hi
    change F.map (P.functorialCupRestriction false j) ≫ ej.hom = _ at hj
    have : Epi (F.map (Etale.closedConstantSectionMap P.Coefficient i)) := F.map_epi _
    have hpi : Epi (P.functorialCupRestriction true i) := by
      rw [← hi]
      exact epi_comp _ _
    let b := ei.inv ≫ F.map t ≫ ej.hom
    have hb : P.functorialCupRestriction true i ≫ b =
        P.functorialCupRestriction true j := by
      rw [← hi]
      dsimp only [b]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← F.map_comp_assoc, ht]
      exact hj
    refine ⟨b, hb, ?_⟩
    intro b' hb'
    exact (cancel_epi (P.functorialCupRestriction true i)).1 (hb'.trans hb.symm)

end SupportMapProof

/-- The actual restriction on closed constant sheaves, fixed by its epic unit map.
Source: supported functoriality, Steps 2 and 5
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupSupportMap (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (g : D ⟶ C) (h : g ≫ i = j) :=
  (P.functorialCupSupportMap_existsUnique pro i j g h).choose

/-- Precomposition with the canonical closed support map. Source: supported
functoriality, symmetry and associativity clauses
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupChangeSupport (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (g : D ⟶ C) (h : g ≫ i = j)
    (a r : ℤ) (α : P.FunctorialCupH pro j a r) : P.FunctorialCupH pro i a r :=
  (P.functorialCupSingle pro X).map (P.functorialCupSupportMap pro i j g h) ≫ α

/-- Only the integral indices are transported; the coefficient and support maps are
spelled out separately. Source: supported functoriality, graded laws
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupReindex (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) {a b r s : ℤ} (ha : a = b) (hr : r = s)
    (α : P.FunctorialCupH pro i a r) : P.FunctorialCupH pro i b s :=
  ha ▸ hr ▸ α

/-- The canonical Ext-to-derived-Hom map, with its localization explicitly shared.
Source: Mathlib Ext.hom (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupExtHom {B : Type c} [Category.{v} B] [Abelian B]
    [HasExt.{w} B] [hD : HasDerivedCategory.{w} B] {F G : B} (x : Abelian.Ext F G 1) :
    (DerivedCategory.singleFunctor B 0).obj F ⟶
      ((DerivedCategory.singleFunctor B 0).obj G)⟦(1 : ℤ)⟧ := x.hom

/-- Transport an Ext class along equality of its target before specializing coefficients.
Source: def-pur-frame-class, identical signed Kummer targets
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupExtTarget {B : Type c} [Category.{v} B] [Abelian B] [HasExt.{w} B]
    {F G H : B} (h : G = H) (x : Abelian.Ext F G 1) : Abelian.Ext F H 1 :=
  h ▸ x

/-- The frame twist is the identical signed etale coefficient line.
Source: def-pur-frame-class, degree-one Kummer target
(blueprint: lem-pur-supported-cup-functoriality).
Proof: unfold frameTwistEtale and functorialCupTwist at the etale site; both
are the same finiteEtaleTateSheaf with the same annihilation proof. -/
theorem functorialCupFrameTwistEtale_eq (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    P.frameTwistEtale X 1 = P.functorialCupTwist false X 1 := by
  rfl

/-- The frame twist is the identical signed pro-etale coefficient line.
Source: def-pur-frame-class, comparison of the Kummer target
(blueprint: lem-pur-supported-cup-functoriality).
Proof: both frameTwist and functorialCupTwist on the pro-etale site are the
same exact comparison inverse image of the etale signed finite coefficient line. -/
theorem functorialCupFrameTwist_eq (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    P.frameTwist X 1 = P.functorialCupTwist true X 1 := by
  rfl

/-- The published Kummer Ext class, selected before passing to derived Hom.
Source: the arbitrary-index Kummer prescription
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupKummerExt (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (v : Γ(X, ⊤)ˣ) :
    Abelian.Ext (P.functorialCupConstant pro X) (P.functorialCupTwist pro X 1) 1 :=
  match pro with
  | false => functorialCupExtTarget (P.functorialCupFrameTwistEtale_eq X)
      (P.frameKummerEtale X aX v)
  | true => functorialCupExtTarget (P.functorialCupFrameTwist_eq X) (P.frameKummer X aX v)

/-- The identity direct-image unitor of the actual supported coefficient source.
Source: the full-support normalization
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupFullSupportIso (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) :
    P.functorialCupSource pro (𝟙 X) ≅ P.functorialCupConstant pro X :=
  match pro with
  | false => (Etale.lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).app
      (P.constantEtale X)
  | true => (ProEtale.lowerStarId (ModuleCat.{u + 1} P.Coefficient) X).app (P.constant X)

/-- The concrete published Kummer class in the full-support Hom model. The direct
image along the identity is identified by its canonical unitor.
Source: def-pur-frame-class, arbitrary-index Kummer prescription
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupKummer (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (v : Γ(X, ⊤)ˣ) :
    P.FunctorialCupH pro (𝟙 X) 1 1 :=
  (P.functorialCupSingle pro X).map (P.functorialCupFullSupportIso pro X).hom ≫
    functorialCupExtHom (hD := P.functorialCupHasDerived pro X)
      (P.functorialCupKummerExt pro X aX v)


/-- Scalar linearity of fixed-ring module sheaves, with the existing action.
Source: purity conventions (blueprint: lem-pur-supported-cup-functoriality). -/
instance functorialCupLinear (P : PurityFiniteSetting.{u}) (pro : Bool) (X : Scheme.{u}) :
    Linear P.Coefficient (P.functorialCupSheaves pro X) := by cases pro <;> infer_instance

/-- The `identity` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraIdentity (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
      (sq : ChosenCartesianSquare (𝟙 C) i i (𝟙 X))
      (aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ) (α : P.FunctorialCupH pro i a r),
    P.functorialCupPullback pro i i (𝟙 X) (𝟙 C) sq aX a r α = α

/-- The `composition` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraComposition (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C X D Y E Z : Scheme.{u}}
      (i : C ⟶ X) (j : D ⟶ Y) (k : E ⟶ Z)
      [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion k]
      (v : Y ⟶ X) (w : Z ⟶ Y) (g : D ⟶ C) (h : E ⟶ D)
      (sq : ChosenCartesianSquare g j i v) (sq' : ChosenCartesianSquare h k j w)
      (sq'' : ChosenCartesianSquare (h ≫ g) k i (w ≫ v))
      (aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ) (α : P.FunctorialCupH pro i a r),
    P.functorialCupPullback pro i k (w ≫ v) (h ≫ g) sq'' aX a r α =
      P.functorialCupPullback pro j k w h sq' (v ≫ aX) a r
        (P.functorialCupPullback pro i j v g sq aX a r α)

/-- The `kummer_add` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraKummerAdd (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ (X : Scheme.{u}) (aX : X ⟶ Spec (.of P.field.k)) (u w : Γ(X, ⊤)ˣ),
    P.functorialCupKummer pro X aX (u * w) =
      P.functorialCupKummer pro X aX u + P.functorialCupKummer pro X aX w

/-- The `kummer_pullback` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraKummerPullback (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {X Y : Scheme.{u}} (v : Y ⟶ X)
      (sq : ChosenCartesianSquare v (𝟙 Y) (𝟙 X) v)
      (aX : X ⟶ Spec (.of P.field.k)) (u : Γ(X, ⊤)ˣ),
    P.functorialCupPullback pro (𝟙 X) (𝟙 Y) v v sq aX 1 1
        (P.functorialCupKummer pro X aX u) =
      P.functorialCupKummer pro Y (v ≫ aX) (Units.map v.appTop.hom.toMonoidHom u)

/-- The `add_left` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraAddLeft (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C D X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
      (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
      (a b r s : ℤ) (α α' : P.FunctorialCupH pro i a r) (β : P.FunctorialCupH pro j b s),
    P.functorialCup pro aX i j a b r s (α + α') β =
      P.functorialCup pro aX i j a b r s α β + P.functorialCup pro aX i j a b r s α' β

/-- The `add_right` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraAddRight (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C D X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
      (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
      (a b r s : ℤ) (α : P.FunctorialCupH pro i a r) (β β' : P.FunctorialCupH pro j b s),
    P.functorialCup pro aX i j a b r s α (β + β') =
      P.functorialCup pro aX i j a b r s α β + P.functorialCup pro aX i j a b r s α β'

/-- The `smul_left` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraSmulLeft (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C D X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
      (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
      (a b r s : ℤ) (c : P.Coefficient)
      (α : P.FunctorialCupH pro i a r) (β : P.FunctorialCupH pro j b s),
    P.functorialCup pro aX i j a b r s (c • α) β = c • P.functorialCup pro aX i j a b r s α β

/-- The `smul_right` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraSmulRight (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C D X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
      (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
      (a b r s : ℤ) (c : P.Coefficient)
      (α : P.FunctorialCupH pro i a r) (β : P.FunctorialCupH pro j b s),
    P.functorialCup pro aX i j a b r s α (c • β) = c • P.functorialCup pro aX i j a b r s α β

/-- The `associativity` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraAssociativity (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C D E X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
      (i : C ⟶ X) (j : D ⟶ X) (k : E ⟶ X)
      [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion k]
      (g : pullback i (ProEtale.cupIntersection j k) ⟶
        pullback (ProEtale.cupIntersection i j) k)
      (hg : g ≫ ProEtale.cupIntersection (ProEtale.cupIntersection i j) k =
        ProEtale.cupIntersection i (ProEtale.cupIntersection j k))
      (a b c r s t : ℤ) (α : P.FunctorialCupH pro i a r)
      (β : P.FunctorialCupH pro j b s) (γ : P.FunctorialCupH pro k c t),
    P.functorialCup pro aX (ProEtale.cupIntersection i j) k (a+b) c (r+s) t
        (P.functorialCup pro aX i j a b r s α β) γ =
      P.functorialCupReindex pro _ (add_assoc a b c).symm (add_assoc r s t).symm
        (P.functorialCupChangeSupport pro _ _ g hg (a+(b+c)) (r+(s+t))
          (P.functorialCup pro aX i (ProEtale.cupIntersection j k) a (b+c) r (s+t)
            α (P.functorialCup pro aX j k b c s t β γ)))

/-- The `symmetry` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraSymmetry (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C D X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
      (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
      (g : pullback j i ⟶ pullback i j)
      (hg : g ≫ ProEtale.cupIntersection i j = ProEtale.cupIntersection j i)
      (a b r s : ℤ) (α : P.FunctorialCupH pro i a r) (β : P.FunctorialCupH pro j b s),
    P.functorialCup pro aX i j a b r s α β = ((-1 : ℤ) ^ (a*b).natAbs) •
      P.functorialCupReindex pro _ (add_comm b a) (add_comm s r)
        (P.functorialCupChangeSupport pro _ _ g hg (b+a) (s+r)
          (P.functorialCup pro aX j i b a s r β α))

/-- The `pullback` clause of `FunctorialCupAlgebraLaws`.
Named to share its kernel type.
Source: Stacks 0FPL, 0FPM, 03PL and 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupAlgebraPullback (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop :=
  ∀ {C D X C' D' Y : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
      (i : C ⟶ X) (j : D ⟶ X) (i' : C' ⟶ Y) (j' : D' ⟶ Y)
      [IsClosedImmersion i] [IsClosedImmersion j]
      [IsClosedImmersion i'] [IsClosedImmersion j']
      (v : Y ⟶ X) (g : C' ⟶ C) (h : D' ⟶ D)
      (sq : ChosenCartesianSquare g i' i v) (sq' : ChosenCartesianSquare h j' j v)
      (q : pullback i' j' ⟶ pullback i j)
      (sqp : ChosenCartesianSquare q (ProEtale.cupIntersection i' j')
        (ProEtale.cupIntersection i j) v)
      (a b r s : ℤ) (α : P.FunctorialCupH pro i a r) (β : P.FunctorialCupH pro j b s),
    P.functorialCupPullback pro _ _ v q sqp aX (a+b) (r+s)
        (P.functorialCup pro aX i j a b r s α β) =
      P.functorialCup pro (v ≫ aX) i' j' a b r s
        (P.functorialCupPullback pro i i' v g sq aX a r α)
        (P.functorialCupPullback pro j j' v h sq' aX b s β)

/-- All algebraic laws in the statement, on the actual supported Hom groups.
A morphism between the indicated closed supports over X is necessarily the canonical
support identification, since their immersions are monic. Thus the symmetry and
associativity fields include their support identifications, not an equality of
differently supported groups. Source: Stacks 0FPL and 0FPM, proof Steps 2--5 and 8
(blueprint: lem-pur-supported-cup-functoriality). -/
structure FunctorialCupAlgebraLaws (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop where
  identity : P.FunctorialCupAlgebraIdentity pro
  composition : P.FunctorialCupAlgebraComposition pro
  kummer_add : P.FunctorialCupAlgebraKummerAdd pro
  kummer_pullback : P.FunctorialCupAlgebraKummerPullback pro
  add_left : P.FunctorialCupAlgebraAddLeft pro
  add_right : P.FunctorialCupAlgebraAddRight pro
  smul_left : P.FunctorialCupAlgebraSmulLeft pro
  smul_right : P.FunctorialCupAlgebraSmulRight pro
  associativity : P.FunctorialCupAlgebraAssociativity pro
  symmetry : P.FunctorialCupAlgebraSymmetry pro
  pullback : P.FunctorialCupAlgebraPullback pro


/-- Ordinary cohomology in the same derived-Hom model. Source: Hom_A(A,-)=sections
(blueprint: lem-pur-supported-cup-functoriality). -/
abbrev FunctorialCupOrdinaryH (P : PurityFiniteSetting.{u}) (pro : Bool)
    (X : Scheme.{u}) (a r : ℤ) :=
  (P.functorialCupSingle pro X).obj (P.functorialCupConstant pro X) ⟶
    ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r))⟦a⟧

/-- Forget supports by the actual restriction of constants to the support.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupForget (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
    (α : P.FunctorialCupH pro i a r) : P.FunctorialCupOrdinaryH pro X a r :=
  (P.functorialCupSingle pro X).map (P.functorialCupRestriction pro i) ≫ α

/-- Ordinary pullback, using exact inverse image and the same twist normalization.
Source: Stacks 0G78 (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOrdinaryPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {X Y : Scheme.{u}} (v : Y ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ)
    (α : P.FunctorialCupOrdinaryH pro X a r) : P.FunctorialCupOrdinaryH pro Y a r :=
  (P.functorialCupSingle pro Y).map (P.functorialCupConstantPullback pro v).inv ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).inv.app
      (P.functorialCupConstant pro X) ≫
    (P.functorialCupInverseImage pro v).mapDerivedCategory.map α ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategory.commShiftIso a).hom.app
      ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r)) ≫
    (((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).hom.app
        (P.functorialCupTwist pro X r) ≫
      (P.functorialCupSingle pro Y).map (P.functorialCupTwistPullback pro v aX r).hom)⟦a⟧'

/-- The published exact extension by zero for the complementary open.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenExtension (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    P.functorialCupSheaves pro i.openComplement.toScheme ⥤ P.functorialCupSheaves pro X :=
  match pro with
  | false => Etale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient)
      i.openComplement.ι
  | true => ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient)
      i.openComplement.ι

/-- Extension by zero of the actual unit on the open complement.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenSource (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :=
  (P.functorialCupOpenExtension pro i).obj
    (P.functorialCupConstant pro i.openComplement.toScheme)

/-- The adjunction counit, with its canonical constant-sheaf restriction.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenInclusion (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    P.functorialCupOpenSource pro i ⟶ P.functorialCupConstant pro X :=
  match pro with
  | false => (P.functorialCupOpenExtension false i).map
      (P.functorialCupConstantPullback false i.openComplement.ι).inv ≫
      (Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) i.openComplement.ι).counit.app (P.constantEtale X)
  | true => (P.functorialCupOpenExtension true i).map
      (P.functorialCupConstantPullback true i.openComplement.ι).inv ≫
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) i.openComplement.ι).counit.app (P.constant X)

/-- The source coefficient arrows form a complex for every closed support.
Source: Stacks 09XP, proof Steps 4 and 7
(blueprint: lem-pur-supported-cup-functoriality).
Proof: restriction of an extension-by-zero section to the complementary closed
subscheme is zero, on every object of either small site. Sheafification preserves
this identity. -/
theorem functorialCupSequence_zero (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    P.functorialCupOpenInclusion pro i ≫ P.functorialCupRestriction pro i = 0 := by
  have hd : Disjoint (Set.range i.openComplement.ι.base) (Set.range i.base) :=
    disjoint_range_of_range_eq_compl i.openComplement.ι i
      i.range_eq_compl_range_openComplement_ι
  cases pro with
  | false =>
    have hz := Etale.isZero_upperStar_lowerStar_of_disjoint_range
      (ModuleCat.{u + 1} P.Coefficient) i.openComplement.ι i hd (P.constantEtale C)
    have : Subsingleton (P.functorialCupConstant false i.openComplement.toScheme ⟶
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) i.openComplement.ι).obj
          (P.functorialCupSource false i)) := ⟨fun _ _ ↦ hz.eq_of_tgt _ _⟩
    have : Subsingleton (P.functorialCupOpenSource false i ⟶
        P.functorialCupSource false i) := Equiv.subsingleton
      ((Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) i.openComplement.ι).homEquiv _ _)
    exact Subsingleton.elim _ _
  | true =>
    have hz := ProEtale.isZero_upperStar_lowerStar_of_disjoint
      (ModuleCat.{u + 1} P.Coefficient) i i.openComplement.ι hd.symm (P.constant C)
    have : Subsingleton (P.functorialCupConstant true i.openComplement.toScheme ⟶
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) i.openComplement.ι).obj
          (P.functorialCupSource true i)) := ⟨fun _ _ ↦ hz.eq_of_tgt _ _⟩
    have : Subsingleton (P.functorialCupOpenSource true i ⟶
        P.functorialCupSource true i) := Equiv.subsingleton
      ((ProEtale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) i.openComplement.ι).homEquiv _ _)
    exact Subsingleton.elim _ _

/-- The actual open-closed coefficient sequence, before deriving.
Source: Stacks 095L, 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupSequence (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :=
  ShortComplex.mk (P.functorialCupOpenInclusion pro i) (P.functorialCupRestriction pro i)
    (P.functorialCupSequence_zero pro i)

section SequenceProof

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupCategory functorialCupAbelian
  constant constantEtale functorialCupConstant functorialCupSource
  functorialCupRestriction functorialCupInverseImage functorialCupConstantPullback
  functorialCupComparisonFunctor functorialCupOpenExtension functorialCupOpenSource
  functorialCupOpenInclusion

private theorem adjunctionCounitSquare
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (F : D ⥤ D') (G : C ⥤ C')
    (e : L ⋙ F ≅ G ⋙ L') (t : R ⋙ G ⟶ F ⋙ R')
    (hu : ∀ K : C, G.map (a.unit.app K) ≫ t.app (L.obj K) ≫
      R'.map (e.hom.app K) = b.unit.app (G.obj K)) (M : D) :
    e.hom.app (R.obj M) ≫ L'.map (t.app M) ≫ b.counit.app (F.obj M) =
      F.map (a.counit.app M) := by
  apply (cancel_epi (e.inv.app (R.obj M))).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply (b.homEquiv _ _).injective
  have hl : (b.homEquiv _ _).symm (t.app M) =
      L'.map (t.app M) ≫ b.counit.app (F.obj M) := b.homEquiv_counit _ _ _
  change (b.homEquiv (G.obj (R.obj M)) (F.obj M))
      (L'.map (t.app M) ≫ b.counit.app (F.obj M)) =
    (b.homEquiv (G.obj (R.obj M)) (F.obj M))
      (e.inv.app (R.obj M) ≫ F.map (a.counit.app M))
  rw [← hl]
  apply Eq.trans ((b.homEquiv _ _).apply_symm_apply (t.app M))
  rw [Adjunction.homEquiv_unit, R'.map_comp, ← hu]
  simp only [Category.assoc, ← R'.map_comp_assoc, Iso.hom_inv_id_app]
  erw [R'.map_id, Category.id_comp]
  have hn := t.naturality (a.counit.app M)
  change G.map (R.map (a.counit.app M)) ≫ t.app M =
    t.app (L.obj (R.obj M)) ≫ R'.map (F.map (a.counit.app M)) at hn
  rw [← hn, ← G.map_comp_assoc, a.right_triangle_components]
  erw [G.map_id, Category.id_comp]

private theorem openComparison_normalized (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    ∃ e : (P.functorialCupComparisonFunctor X).obj
        (P.functorialCupOpenSource false i) ≅ P.functorialCupOpenSource true i,
      (P.functorialCupComparisonFunctor X).map (P.functorialCupOpenInclusion false i) =
        e.hom ≫ P.functorialCupOpenInclusion true i := by
  let A := ModuleCat.{u + 1} P.Coefficient
  let j := i.openComplement.ι
  let F := ProEtale.comparisonUpperStar A X
  let G := ProEtale.comparisonUpperStar A i.openComplement.toScheme
  let E := Etale.openImmersionLowerShriek A j
  let L := ProEtale.openImmersionLowerShriek A j
  let U := Etale.upperStar A j
  let V := ProEtale.upperStar A j
  let a := Etale.openImmersionLowerShriekUpperStarAdjunction A j
  let b := ProEtale.openImmersionLowerShriekUpperStarAdjunction A j
  let ar := Etale.openImmersionLowerShriekAdjunction A j
  let br := ProEtale.openImmersionLowerShriekAdjunction A j
  let er := Etale.upperStarIsoOpenImmersionRestriction A j
  let pr := ProEtale.upperStarIsoOpenImmersionRestriction A j
  let τ := ProEtale.comparisonUpperStarCompUpperStarIso A j
  let θ := ProEtale.openImmersionLowerShriekComparisonUpperStarIso A j
  have hu (K : Sheaf i.openComplement.toScheme.smallEtaleTopology A) :
      G.map (a.unit.app K) ≫ τ.inv.app (E.obj K) ≫ V.map (θ.hom.app K) =
        b.unit.app (G.obj K) := by
    have hr := (ProEtale.openComparison_unit_normalization P.Coefficient j).2 K
    change G.map (ar.unit.app K) ≫
      (ProEtale.openComparisonRestrictionIso P.Coefficient j).hom.app (E.obj K) ≫
      (ProEtale.openImmersionRestriction A j).map (θ.hom.app K) =
        br.unit.app (G.obj K) at hr
    change G.map (ar.unit.app K ≫ er.inv.app (E.obj K)) ≫
      τ.inv.app (E.obj K) ≫ V.map (θ.hom.app K) =
        br.unit.app (G.obj K) ≫ pr.inv.app (L.obj (G.obj K))
    rw [G.map_comp]
    apply ((pr.app (L.obj (G.obj K))).homToEquiv).injective
    change (G.map (ar.unit.app K) ≫ G.map (er.inv.app (E.obj K)) ≫
      τ.inv.app (E.obj K) ≫ V.map (θ.hom.app K)) ≫ pr.hom.app _ =
        (br.unit.app (G.obj K) ≫ pr.inv.app _) ≫ pr.hom.app _
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [pr.hom.naturality]
    erw [Category.comp_id]
    change G.map (ar.unit.app K) ≫
      ((G.map (er.inv.app (E.obj K)) ≫ τ.inv.app (E.obj K)) ≫
        pr.hom.app (F.obj (E.obj K))) ≫
      (ProEtale.openImmersionRestriction A j).map (θ.hom.app K) = _ at hr
    simpa only [Category.assoc] using hr
  have hc := adjunctionCounitSquare a b F G θ τ.inv hu (P.constantEtale X)
  let e := θ.app (P.constantEtale i.openComplement.toScheme)
  refine ⟨e, ?_⟩
  change F.map (E.map (P.functorialCupConstantPullback false j).inv ≫
      a.counit.app (P.constantEtale X)) = e.hom ≫
    L.map (P.functorialCupConstantPullback true j).inv ≫
      b.counit.app (P.constant X)
  rw [F.map_comp]
  change _ = e.hom ≫ L.map (G.map
    (P.functorialCupConstantPullback false j).inv ≫ τ.inv.app _) ≫ _
  rw [L.map_comp]
  simp only [Category.assoc]
  have hn := θ.hom.naturality (P.functorialCupConstantPullback false j).inv
  change F.map (E.map (P.functorialCupConstantPullback false j).inv) ≫ θ.hom.app _ =
    e.hom ≫ L.map (G.map (P.functorialCupConstantPullback false j).inv) at hn
  rw [← reassoc_of% hn, hc]

private theorem etaleSequence_shortExact (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    (P.functorialCupSequence false i).ShortExact := by
  let A := ModuleCat.{u + 1} P.Coefficient
  let j := i.openComplement.ι
  let eU := P.functorialCupConstantPullback false j
  let eC := P.functorialCupConstantPullback false i
  let S := Etale.openClosedShortComplex A j i
    (disjoint_range_of_range_eq_compl j i i.range_eq_compl_range_openComplement_ι)
    (P.constantEtale X)
  let e₁ := (Etale.openImmersionLowerShriek A j).mapIso eU
  let e₃ := (Etale.lowerStar A i).mapIso eC
  let e : S ≅ P.functorialCupSequence false i := ShortComplex.isoMk
    e₁ (Iso.refl _) e₃ (by
      change (Etale.openImmersionLowerShriek A j).map eU.hom ≫
        ((Etale.openImmersionLowerShriek A j).map eU.inv ≫
          (Etale.openImmersionLowerShriekUpperStarAdjunction A j).counit.app
            (P.constantEtale X)) =
        (Etale.openImmersionLowerShriekUpperStarAdjunction A j).counit.app
          (P.constantEtale X) ≫ 𝟙 _
      rw [← Functor.map_comp_assoc, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]) (by
      change 𝟙 _ ≫ Etale.closedConstantSectionMap P.Coefficient i =
        (Etale.upperStarLowerStarAdjunction A i).unit.app (P.constantEtale X) ≫
          (Etale.lowerStar A i).map eC.hom
      simp only [Category.id_comp]
      rw [section_unit]
      change _ = (Etale.upperStarLowerStarAdjunction A i).unit.app _ ≫
        (Etale.lowerStar A i).map
          ((Scheme.upperStarConstantSheafIso A i).hom.app (𝟙_ A))
      rw [Etale.upperStarConstantSheafIso_hom_app_tensorUnit]
      exact (Adjunction.unit_app_unit_comp_map_η
        (Etale.upperStarLowerStarAdjunction A i)).symm)
  exact ShortComplex.shortExact_of_iso e
    (Etale.shortExact_openClosedShortComplex A j i (P.constantEtale X)
      i.range_eq_compl_range_openComplement_ι)

/-- Exactness of this normalized coefficient sequence on either small site.
Source: Stacks 095L, 09XP, proof Steps 4 and 7
(blueprint: lem-pur-supported-cup-functoriality).
Proof: apply the recorded open-closed sequence on the etale site. On the pro-etale
site compare the exact sequence by exact inverse image, identifying the closed
source by restriction of local constants and the open source by the counit-normalized
extension-by-zero comparison. This argument does not require a quasi-compact complement. -/
theorem functorialCupSequence_shortExact (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    (P.functorialCupSequence pro i).ShortExact := by
  cases pro with
  | false => exact etaleSequence_shortExact P i
  | true =>
    let F := P.functorialCupComparisonFunctor X
    obtain ⟨e₁, h₁⟩ := openComparison_normalized P i
    let e₃ := (comparisonSource_normalized P i).choose
    have h₃ := (comparisonSource_normalized P i).choose_spec.1
    let e : (P.functorialCupSequence false i).map F ≅
        P.functorialCupSequence true i := ShortComplex.isoMk e₁ (Iso.refl _) e₃
      (by
        change e₁.hom ≫ P.functorialCupOpenInclusion true i =
          F.map (P.functorialCupOpenInclusion false i) ≫ 𝟙 _
        exact h₁.symm.trans (Category.comp_id _).symm)
      (by
        change 𝟙 _ ≫ P.functorialCupRestriction true i =
          F.map (P.functorialCupRestriction false i) ≫ e₃.hom
        exact (Category.id_comp _).trans h₃.symm)
    exact ShortComplex.shortExact_of_iso e ((etaleSequence_shortExact P i).map_of_exact F)

end SequenceProof

/-- Cohomology of the open complement in its exact extension-by-zero adjunction
model Hom_X(j!A_U,F[a])=Hom_U(A_U,j*F[a]). This retains the usual cohomology
on U with the restriction of A(r). Source: Stacks 09XP
(blueprint: lem-pur-supported-cup-functoriality). -/
abbrev FunctorialCupOpenH (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ) :=
  (P.functorialCupSingle pro X).obj (P.functorialCupOpenSource pro i) ⟶
    ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r))⟦a⟧

/-- Ordinary restriction is precomposition with the open adjunction counit.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenRestriction (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
    (α : P.FunctorialCupOrdinaryH pro X a r) : P.FunctorialCupOpenH pro i a r :=
  (P.functorialCupSingle pro X).map (P.functorialCupOpenInclusion pro i) ≫ α

/-- The localization boundary with the source sequence's actual connecting arrow.
Its normalization is the same Ext composition as the individual frame boundary.
Source: thm-pur-with-support-exactness and Stacks 09XP, proof Steps 4 and 7
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupBoundary (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
    (α : P.FunctorialCupOpenH pro i a r) : P.FunctorialCupH pro i (a + 1) r :=
  ShiftedHom.comp (P.functorialCupSequence_shortExact pro i).singleδ α rfl

private theorem normalizedKernelIso {E : Type c} [Category.{v} E] [Abelian E]
    {S T : ShortComplex E} (hS : S.ShortExact) (hT : T.ShortExact)
    (e₂ : S.X₂ ≅ T.X₂) (e₃ : S.X₃ ≅ T.X₃)
    (h : e₂.hom ≫ T.g = S.g ≫ e₃.hom) :
    ∃! e₁ : S.X₁ ≅ T.X₁, S.f ≫ e₂.hom = e₁.hom ≫ T.f := by
  let φ : Arrow.mk S.g ≅ Arrow.mk T.g := Arrow.isoMk e₂ e₃ h
  let e := KernelFork.mapIsoOfIsLimit hS.fIsKernel hT.fIsKernel φ
  have he : S.f ≫ e₂.hom = e.hom ≫ T.f := by
    exact (KernelFork.mapOfIsLimit_ι (KernelFork.ofι S.f S.zero) hT.fIsKernel φ.hom).symm
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  have := hT.mono_f
  apply (cancel_mono T.f).1
  exact he'.symm.trans he

/-- Open coefficient exchange is uniquely normalized by its inclusion in the unit.
Source: Stacks 09XP, supported functoriality, Steps 4 and 7
(blueprint: lem-pur-supported-cup-functoriality).
Proof: exact inverse image and extension by zero commute for the base-changed open.
Their canonical comparison respects counits by adjunction. Its tensor-unit
normalization gives the displayed equation; the monic open inclusion proves uniqueness. -/
theorem functorialCupOpenExchange_existsUnique (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (_sq : ChosenCartesianSquare g j i v) :
    ∃! b : (P.functorialCupInverseImage pro v).obj (P.functorialCupOpenSource pro i) ≅
        P.functorialCupOpenSource pro j,
      (P.functorialCupInverseImage pro v).map (P.functorialCupOpenInclusion pro i) ≫
          (P.functorialCupConstantPullback pro v).hom =
        b.hom ≫ P.functorialCupOpenInclusion pro j := by
  let F := P.functorialCupInverseImage pro v
  let e := (P.functorialCupExchange_existsUnique pro i j v g _sq).choose
  have he := (P.functorialCupExchange_existsUnique pro i j v g _sq).choose_spec.1
  exact normalizedKernelIso
    ((P.functorialCupSequence_shortExact pro i).map_of_exact F)
    (P.functorialCupSequence_shortExact pro j)
    (P.functorialCupConstantPullback pro v) e he.symm

/-- Canonical open pullback, expressed by exact inverse image on the adjunction Hom model.
Source: Stacks 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenPullback (P : PurityFiniteSetting.{u}) (pro : Bool)
    {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
    (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
    (a r : ℤ) (α : P.FunctorialCupOpenH pro i a r) : P.FunctorialCupOpenH pro j a r :=
  (P.functorialCupSingle pro Y).map
      (P.functorialCupOpenExchange_existsUnique pro i j v g sq).choose.inv ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).inv.app
      (P.functorialCupOpenSource pro i) ≫
    (P.functorialCupInverseImage pro v).mapDerivedCategory.map α ≫
    ((P.functorialCupInverseImage pro v).mapDerivedCategory.commShiftIso a).hom.app
      ((P.functorialCupSingle pro X).obj (P.functorialCupTwist pro X r)) ≫
    (((P.functorialCupInverseImage pro v).mapDerivedCategorySingleFunctor 0).hom.app
        (P.functorialCupTwist pro X r) ≫
      (P.functorialCupSingle pro Y).map (P.functorialCupTwistPullback pro v aX r).hom)⟦a⟧'

/-- The localization compatibility clauses, including the full-support normalization.
Source: Stacks 09XP and 0G78, proof Step 4
(blueprint: lem-pur-supported-cup-functoriality). -/
structure FunctorialCupLocalizationLaws (P : PurityFiniteSetting.{u}) (pro : Bool) : Prop where
  full_support : ∀ (X : Scheme.{u}) (_aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ),
    Function.Bijective (P.functorialCupForget pro (𝟙 X) a r)
  forget_support : ∀ {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
      [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
      (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
      (a r : ℤ) (α : P.FunctorialCupH pro i a r),
    P.functorialCupForget pro j a r (P.functorialCupPullback pro i j v g sq aX a r α) =
      P.functorialCupOrdinaryPullback pro v aX a r (P.functorialCupForget pro i a r α)
  open_restriction : ∀ {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
      [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
      (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
      (a r : ℤ) (α : P.FunctorialCupOrdinaryH pro X a r),
    P.functorialCupOpenPullback pro i j v g sq aX a r
        (P.functorialCupOpenRestriction pro i a r α) =
      P.functorialCupOpenRestriction pro j a r
        (P.functorialCupOrdinaryPullback pro v aX a r α)
  boundary : ∀ {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
      [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
      (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
      (a r : ℤ) (α : P.FunctorialCupOpenH pro i a r),
    P.functorialCupPullback pro i j v g sq aX (a+1) r
        (P.functorialCupBoundary pro i a r α) =
      P.functorialCupBoundary pro j a r (P.functorialCupOpenPullback pro i j v g sq aX a r α)


/-- Map a degree-zero shifted Hom by an exact functor, using its canonical
single and shift comparisons before specializing the site categories.
Source: finite site comparison, Stacks 099W
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupExactHom {B D : Type c} [Category.{v} B] [Category.{v} D]
    [Abelian B] [Abelian D] [hB : HasDerivedCategory.{w} B]
    [hD : HasDerivedCategory.{w} D] (F : B ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S T : B} (a : ℤ)
    (α : (DerivedCategory.singleFunctor B 0).obj S ⟶
      ((DerivedCategory.singleFunctor B 0).obj T)⟦a⟧) :
    (DerivedCategory.singleFunctor D 0).obj (F.obj S) ⟶
      ((DerivedCategory.singleFunctor D 0).obj (F.obj T))⟦a⟧ :=
  (F.mapDerivedCategorySingleFunctor 0).inv.app S ≫
    F.mapDerivedCategory.map α ≫
    (F.mapDerivedCategory.commShiftIso a).hom.app
      ((DerivedCategory.singleFunctor B 0).obj T) ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app T)⟦a⟧'

/-- Closed sources are canonically identified by the site comparison, normalized
on local constants. Source: Stacks 099V, 099W; proof Step 6
(blueprint: lem-pur-supported-cup-functoriality).
Proof: on a weakly etale Y over X the inverse-image section formula computes
etale sections on Y of the closed direct image. Etale base change identifies these
with constants on Y times_X C. Degree-zero comparison identifies them with the
same pro-etale constants. These identifications commute with restriction and
scalar multiplication and carry 1 to 1. They glue to the specified isomorphism.
The epic constant restriction makes it unique. -/
theorem functorialCupComparisonSource_existsUnique (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    ∃! b : (P.functorialCupComparisonFunctor X).obj
        (P.functorialCupSource false i) ≅ P.functorialCupSource true i,
      (P.functorialCupComparisonFunctor X).map
          (P.functorialCupRestriction false i) ≫ b.hom = P.functorialCupRestriction true i := by
  exact comparisonSource_normalized P i

/-- The comparison target of the signed twist is its defining pro-etale sheaf.
Source: finite coefficient twist comparison, Stacks 099W
(blueprint: lem-pur-supported-cup-functoriality).
Proof: unfold the two selected twists and the comparison functor. Both sides
are exact comparison inverse image of the same signed finite etale Tate sheaf. -/
theorem functorialCupComparisonTwist_eq (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (r : ℤ) :
    (P.functorialCupComparisonFunctor X).obj (P.functorialCupTwist false X r) =
      P.functorialCupTwist true X r := by
  rfl

/-- The comparison target of the coefficient unit is its defining pro-etale constant.
Source: finite coefficient comparison, Stacks 099W
(blueprint: lem-pur-supported-cup-functoriality).
Proof: unfold the constant sheaves and comparison functor; the pro-etale
coefficient unit was defined as comparison inverse image of the etale unit. -/
theorem functorialCupComparisonConstant_eq (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) :
    (P.functorialCupComparisonFunctor X).obj (P.functorialCupConstant false X) =
      P.functorialCupConstant true X := by
  rfl

/-- Canonical comparison on the supported Hom groups. The finite twist on the
pro-etale site is the exact inverse image of the identical etale twist.
Source: Stacks 09B1, supported functoriality Step 7
(blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupCompare (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
    (α : P.FunctorialCupH false i a r) : P.FunctorialCupH true i a r :=
  (P.functorialCupSingle true X).map (P.functorialCupComparisonSource_existsUnique i).choose.inv ≫
    functorialCupExactHom (hB := P.functorialCupHasDerived false X)
      (hD := P.functorialCupHasDerived true X) (P.functorialCupComparisonFunctor X) a α ≫
    ((P.functorialCupSingle true X).map
      (eqToHom (P.functorialCupComparisonTwist_eq X r)))⟦a⟧'

/-- Ordinary site comparison in the identical degree-zero and shift conventions.
Source: Stacks 099W (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOrdinaryCompare (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (a r : ℤ)
    (α : P.FunctorialCupOrdinaryH false X a r) : P.FunctorialCupOrdinaryH true X a r :=
  (P.functorialCupSingle true X).map
      (eqToHom (P.functorialCupComparisonConstant_eq X).symm) ≫
  functorialCupExactHom (hB := P.functorialCupHasDerived false X)
    (hD := P.functorialCupHasDerived true X) (P.functorialCupComparisonFunctor X) a α ≫
    ((P.functorialCupSingle true X).map
      (eqToHom (P.functorialCupComparisonTwist_eq X r)))⟦a⟧'

/-- Open comparison preserves the actual extension-by-zero counit.
Source: Stacks 099V, proof Step 7; lem-cbc-proetale-extension-zero-comparison
(blueprint: lem-pur-supported-cup-functoriality).
Proof: the canonical comparison restricts to the identity on the open. Under the
two extension-by-zero adjunctions the counits correspond to that same identity.
The open inclusion is monic, so its equation specifies the comparison uniquely. -/
theorem functorialCupComparisonOpen_existsUnique (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    ∃! b : (P.functorialCupComparisonFunctor X).obj
        (P.functorialCupOpenSource false i) ≅ P.functorialCupOpenSource true i,
      (P.functorialCupComparisonFunctor X).map
          (P.functorialCupOpenInclusion false i) =
        b.hom ≫ P.functorialCupOpenInclusion true i := by
  let F := P.functorialCupComparisonFunctor X
  let e := (P.functorialCupComparisonSource_existsUnique i).choose
  have he := (P.functorialCupComparisonSource_existsUnique i).choose_spec.1
  exact normalizedKernelIso
    ((P.functorialCupSequence_shortExact false i).map_of_exact F)
    (P.functorialCupSequence_shortExact true i)
    (eqToIso (P.functorialCupComparisonConstant_eq X)) e (by
      change 𝟙 _ ≫ P.functorialCupRestriction true i =
        F.map (P.functorialCupRestriction false i) ≫ e.hom
      exact (Category.id_comp _).trans he.symm)

/-- Site comparison on open cohomology in the extension-by-zero adjunction model.
Source: Stacks 099V, 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def functorialCupOpenCompare (P : PurityFiniteSetting.{u})
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
    (α : P.FunctorialCupOpenH false i a r) : P.FunctorialCupOpenH true i a r :=
  (P.functorialCupSingle true X).map (P.functorialCupComparisonOpen_existsUnique i).choose.inv ≫
    functorialCupExactHom (hB := P.functorialCupHasDerived false X)
      (hD := P.functorialCupHasDerived true X) (P.functorialCupComparisonFunctor X) a α ≫
    ((P.functorialCupSingle true X).map
      (eqToHom (P.functorialCupComparisonTwist_eq X r)))⟦a⟧'

/-- The `supported_bijective` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonSupportedBijective (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
      (_aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ),
    Function.Bijective (P.functorialCupCompare i a r)

/-- The `ordinary_bijective` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonOrdinaryBijective (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ (X : Scheme.{u}) (_aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ),
    Function.Bijective (P.functorialCupOrdinaryCompare X a r)

/-- The `open_bijective` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonOpenBijective (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
      (_aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ),
    Function.Bijective (P.functorialCupOpenCompare i a r)

/-- The `pullback` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonPullback (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
      [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
      (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
      (a r : ℤ) (α : P.FunctorialCupH false i a r),
    P.functorialCupCompare j a r (P.functorialCupPullback false i j v g sq aX a r α) =
      P.functorialCupPullback true i j v g sq aX a r (P.functorialCupCompare i a r α)

/-- The `ordinary_pullback` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonOrdinaryPullback (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y : Scheme.{u}} (v : Y ⟶ X)
      (aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ)
      (α : P.FunctorialCupOrdinaryH false X a r),
    P.functorialCupOrdinaryCompare Y a r (P.functorialCupOrdinaryPullback false v aX a r α) =
      P.functorialCupOrdinaryPullback true v aX a r (P.functorialCupOrdinaryCompare X a r α)

/-- The `open_pullback` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonOpenPullback (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {C X D Y : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ Y)
      [IsClosedImmersion i] [IsClosedImmersion j] (v : Y ⟶ X) (g : D ⟶ C)
      (sq : ChosenCartesianSquare g j i v) (aX : X ⟶ Spec (.of P.field.k))
      (a r : ℤ) (α : P.FunctorialCupOpenH false i a r),
    P.functorialCupOpenCompare j a r (P.functorialCupOpenPullback false i j v g sq aX a r α) =
      P.functorialCupOpenPullback true i j v g sq aX a r (P.functorialCupOpenCompare i a r α)

/-- The `cup` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonCup (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {C D X : Scheme.{u}} (aX : X ⟶ Spec (.of P.field.k))
      (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j]
      (a b r s : ℤ) (α : P.FunctorialCupH false i a r) (β : P.FunctorialCupH false j b s),
    P.functorialCupCompare _ (a+b) (r+s) (P.functorialCup false aX i j a b r s α β) =
      P.functorialCup true aX i j a b r s
        (P.functorialCupCompare i a r α) (P.functorialCupCompare j b s β)

/-- The `kummer` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonKummer (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ (X : Scheme.{u}) (aX : X ⟶ Spec (.of P.field.k)) (u : Γ(X, ⊤)ˣ),
    P.functorialCupCompare (𝟙 X) 1 1 (P.functorialCupKummer false X aX u) =
      P.functorialCupKummer true X aX u

/-- The `forget_support` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonForgetSupport (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
      (α : P.FunctorialCupH false i a r),
    P.functorialCupOrdinaryCompare X a r (P.functorialCupForget false i a r α) =
      P.functorialCupForget true i a r (P.functorialCupCompare i a r α)

/-- The `open_restriction` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonOpenRestriction (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
      (α : P.FunctorialCupOrdinaryH false X a r),
    P.functorialCupOpenCompare i a r (P.functorialCupOpenRestriction false i a r α) =
      P.functorialCupOpenRestriction true i a r (P.functorialCupOrdinaryCompare X a r α)

/-- The `boundary` clause of `FunctorialCupComparisonLaws`.
Named to share its kernel type.
Source: Stacks 09B1, 099V, 099W and 09XP (blueprint: lem-pur-supported-cup-functoriality). -/
def FunctorialCupComparisonBoundary (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] (a r : ℤ)
      (α : P.FunctorialCupOpenH false i a r),
    P.functorialCupCompare i (a+1) r (P.functorialCupBoundary false i a r α) =
      P.functorialCupBoundary true i a r (P.functorialCupOpenCompare i a r α)

/-- All operation-identification clauses for the canonical etale-to-pro-etale
comparison, including both arrows and the boundary of localization.
Source: Stacks 09B1, 099V and 099W, proof Steps 6--8
(blueprint: lem-pur-supported-cup-functoriality). -/
structure FunctorialCupComparisonLaws (P : PurityFiniteSetting.{u}) : Prop where
  supported_bijective : P.FunctorialCupComparisonSupportedBijective
  ordinary_bijective : P.FunctorialCupComparisonOrdinaryBijective
  open_bijective : P.FunctorialCupComparisonOpenBijective
  pullback : P.FunctorialCupComparisonPullback
  ordinary_pullback : P.FunctorialCupComparisonOrdinaryPullback
  open_pullback : P.FunctorialCupComparisonOpenPullback
  cup : P.FunctorialCupComparisonCup
  kummer : P.FunctorialCupComparisonKummer
  forget_support : P.FunctorialCupComparisonForgetSupport
  open_restriction : P.FunctorialCupComparisonOpenRestriction
  boundary : P.FunctorialCupComparisonBoundary

/-- Pullback, localization, concrete Kummer identities and graded cup laws on both
small sites, identified by their canonical site comparison.
Source: Stacks Tags 0FPL, 0FPM, 09XP, 03PL and 0G78; blueprint
lem-pur-frame-independence, unit multiples, permutations and shears
(blueprint: lem-pur-supported-cup-functoriality).

Proof:
1. Put m=ell^n. It annihilates A at every positive coefficient level. Apply
lem-asd-etale-finite-twist-pullback to its roots line, powers and duals. The local
primitive-root descriptions and lem-pur-twist-sheaf-locally-free identify the
projection-induced pro-etale twist and root coefficient map with this finite line.
Compare the identical root sections by lem-cbc-abelian-etale-proetale-cohomology-comparison
and lem-sf-comparison-pullback-exact. Every twist is a flat rank-one line.
2. Use lem-pur-etale-closed-constant-tensor: closed coefficients are flat, and the
normalized exchange and tensor multiplication are invertible and coherent. This
constructs the etale analogue of def-pur-supported-cup without exceptional base change.
3. Total tensor has its usual associator and Koszul symmetry. On homogeneous
cochains of degrees p,q the symmetry is (-1)^(pq). The two differential signs agree.
Descend these constraints through flat-term K-flat representatives using
lem-weil-pbc-site-derived-tensor-descent and lem-pc-kflat-closure. The canonical
ringed-topos tensor pullback comparison respects them termwise.
4. Use lem-amb-closed-support-hom and prop-weil-pbc-inverse-image-modules-exact
to pull back a representative as tau[a] v inverse(alpha) b inverse. Evaluation at 1
on injective representatives identifies this with the usual support-kernel pullback:
lem-weil-pbc-ext-exact-functor-cocycle and lem-weil-pbc-site-cohomology-pullback give
the normalization. Negative degrees vanish. Naturality of the actual source
short exact sequence gives restriction and boundary compatibility, with the
boundary convention of thm-pur-with-support-exactness. Unit-normalized exchanges
compose and are identities. For full support this is ordinary pullback.
5. Apply lem-pur-shifted-tensor-morphism-calculus to the flat support sources and
rank-one targets. Its sign is (-1)^(bp), exactly cupTensorShiftIso. Biadditivity
and scalar linearity give bilinearity. Its associativity and signed symmetry,
the source multiplications from Step 2 and the twist multiplications from Step 1
give associativity and (-1)^(ab) symmetry. Its pullback equation cancels the
normalized source exchanges and gives the cup pullback equality.
6. Evaluate comparison of a closed source on every weakly etale Y over X.
lem-cbc-comparison-pullback-sections and etale base change identify it with
etale constants on Y times_X C; degree-zero comparison identifies these with
pro-etale constants. Restriction and multiplication of the same local constants
identify the two coefficient multiplication maps and their flat derived maps.
No conservativity of pro-etale geometric stalks is asserted.
7. Full faithfulness in thm-weil-pbc-site-comparison and the supported Hom models
give the comparison bijections. lem-weil-pbc-comparison-pullback gives their
pullback square. lem-cbc-proetale-extension-zero-comparison preserves the open
counit by adjunction; together with Step 6 this identifies both arrows of the
source short exact sequence. The exact-functor single-delta formula
lem-weil-pbc-exact-functor-ses-triangle-image identifies the actual boundary,
including its sign. Step 5 then identifies the cups, and every pro-etale class
comes from an etale class, transporting all laws.
8. The Kummer sequence is short exact by lem-amb-kummer-any-base. Its connecting
map is additive by lem-weil-pbc-right-derived-universal-delta-functor. Pullback of
units commutes with powers and roots, giving naturality of its connecting map
by lem-weil-pbc-site-cohomology-pullback. The scalar extension sends a root to
that root tensor 1 and commutes with pullback. Def-pur-frame-class specifies
the concrete pro-etale class by comparison and this very root coefficient map,
so both Kummer identities and their site comparison follow. -/
theorem supportedCupFunctoriality (P : PurityFiniteSetting.{u}) :
    (∀ pro : Bool, P.FunctorialCupAlgebraLaws pro ∧ P.FunctorialCupLocalizationLaws pro) ∧
      P.FunctorialCupComparisonLaws := by
  sorry

end WeilConjectures.PurityFiniteSetting

