/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralDualizing
public import WeilConjectures.SixFunctors.Integral.IntegralHomReduction
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.AlgebraicGeometry.SixFunctors.DeltaRestriction
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.Sites.PullbackFlat
public import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
public import WeilConjectures.Mathlib.CategoryTheory.EssentialImage
public import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedFiniteExceptionalAt

/-! # Integral Verdier duality models

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general, order 2146
(blueprint: def-sf-integral-verdier-models).

The dual is the ambient K-injective internal Hom over the completed ring sheaf.
Positive level n+1 is indexed by n : ℕ. The dualizing input is the object with
its specified reductions from prop-coef-integral-dualizing.

## Main definitions and statement

* `IntegralVerdier.dual`: ambient internal Hom into the integral dualizing object.
* `IntegralVerdier.comparison`: the evaluation-defined reduction map.
* `IntegralVerdier.delta`: specialization of the recorded evaluation transpose.
* `IntegralVerdier.Conclusion`: all integral duality and compatibility clauses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace WeilConjectures.IntegralVerdier

/-- The signed symmetry on a normalized tensor presentation, fixed on all homogeneous
local tensor generators. Naturality extends the representative normalization to all
objects and arrows of the derived category.
Source: blueprint order 2146, proof step 5; Stacks 06YL and 08J9
(blueprint: def-sf-integral-verdier-models). -/
structure SignedSymmetry (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : IntegralHom.TensorPresentation.{u, u} X R) where
  swap : ∀ K L : IntegralHom.Derived.{u, u} X R,
    a.tensor.obj (K, L) ≅ a.tensor.obj (L, K)
  naturality : ∀ (K L K' L' : IntegralHom.Derived.{u, u} X R)
    (f : K ⟶ K') (g : L ⟶ L'),
    a.tensor.map (Prod.mkHom f g) ≫ (swap K' L').hom =
      (swap K L).hom ≫ a.tensor.map (Prod.mkHom g f)
  representative : ∀ (P Q : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
    (hP : IntegralHom.flat.{u, u} X R P) (hQ : IntegralHom.flat.{u, u} X R Q),
    ∃ s : ((IntegralHom.totalTensor.{u, u} X R).obj P).obj Q ⟶
        ((IntegralHom.totalTensor.{u, u} X R).obj Q).obj P,
      (∀ (i j : ℤ) (U : X.ProEtᵒᵖ)
        (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
        (s.f (i + j)).val.app U (IntegralHom.totalPair.{u, u} X R P Q i j U x y) =
          (i * j).negOnePow •
            (eqToHom (congrArg
              (fun k : ℤ ↦ (((IntegralHom.totalTensor.{u, u} X R).obj Q).obj P).X k)
                (add_comm j i))).val.app U
                  (IntegralHom.totalPair.{u, u} X R Q P j i U y x)) ∧
      a.representative.inv.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫ DerivedCategory.Q.map s ≫
        a.representative.hom.app (⟨Q, hQ⟩, ⟨P, hP⟩) =
          (swap (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The unchanged completed-coefficient derived category.
Source: blueprint order 2146 (blueprint: def-sf-integral-verdier-models). -/
abbrev Ambient := DerivedCategory (scalarReductionSource.{u, u} l E X)

/-- Ambient Verdier duality is RHom into the supplied integral dualizing object.
Source: blueprint order 2146, first display (blueprint: def-sf-integral-verdier-models). -/
def dual (ω : Ambient l E X) : (Ambient l E X)ᵒᵖ ⥤ Ambient l E X :=
  (Functor.curry.obj (IntegralHom.hom.{u, u} X
    (completedIntegralCommRingSheafUnrestricted l E X))).flip.obj ω

/-- The actual finite dual with the specified finite dualizing object.
Source: blueprint order 2146, finite dual (blueprint: def-sf-integral-verdier-models). -/
def finiteDual (n : ℕ) (ω : DerivedCategory (scalarReductionTarget l E X n)) :
    (DerivedCategory (scalarReductionTarget l E X n))ᵒᵖ ⥤
      DerivedCategory (scalarReductionTarget l E X n) :=
  (Functor.curry.obj (IntegralHom.hom.{u, u} X
    (integralCoefficientCommRingSheaf l E X n))).flip.obj ω

/-- The double-dual map is the transpose of evaluation with its factors interchanged.
The symmetry is the signed representative symmetry above.
Source: blueprint order 2146, proof step 5; Stacks 08J9
(blueprint: def-sf-integral-verdier-models). -/
def delta {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : IntegralHom.TensorPresentation.{u, u} X R) (s : SignedSymmetry X R a)
    (ω K : IntegralHom.Derived.{u, u} X R) :
    K ⟶ (IntegralHom.hom.{u, u} X R).obj
      (op ((IntegralHom.hom.{u, u} X R).obj (op K, ω)), ω) :=
  restrictionDualDelta (Functor.curry.obj a.tensor)
    (Functor.curry.obj (IntegralHom.hom.{u, u} X R)) a.adjunction s.swap ω K

/-- Restriction of the actual dual functor, using the preservation clause as a proof.
Source: blueprint order 2146, anti-equivalence (blueprint: def-sf-integral-verdier-models). -/
def restrictedDual (ω : Ambient l E X)
    (h : ∀ K : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E X ((dual l E X ω).obj (op K.obj))) :
    (sfIntegralConstructibleCategory l E X)ᵒᵖ ⥤ sfIntegralConstructibleCategory l E X :=
  ObjectProperty.lift (sfIntegralConstructible l E X)
    ((sfIntegralConstructible l E X).ι.op ⋙ dual l E X ω) (fun K ↦ h K.unop)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The evaluation-defined comparison, followed by the specified dualizing reduction.
Source: blueprint order 2146, first comparison; lem-coef-integral-hom-reduction
(blueprint: def-sf-integral-verdier-models). -/
def comparison
    {a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl)}
    {n : ℕ} (m : IntegralHom.ReductionPresentation l E X D hl a n)
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n) (K : Ambient l E X) :
    (scalarReductionDerivedExtension l E X n).obj ((dual l E X ω.obj).obj (op K)) ⟶
      (finiteDual l E X n (integralDualizingFiniteTerm l E D X n)).obj
        (op ((scalarReductionDerivedExtension l E X n).obj K)) :=
  (m.target.adjunction ((scalarReductionDerivedExtension l E X n).obj K)).homEquiv
    ((scalarReductionDerivedExtension l E X n).obj ((dual l E X ω.obj).obj (op K)))
    ((scalarReductionDerivedExtension l E X n).obj ω.obj)
    (m.mu.inv.app (K, (dual l E X ω.obj).obj (op K)) ≫
      (scalarReductionDerivedExtension l E X n).map ((a.adjunction K).counit.app ω.obj)) ≫
    (IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
      (Prod.mkHom (𝟙 (op ((scalarReductionDerivedExtension l E X n).obj K)))
        (r n).hom)

/-- The finite dual terms in one ambient category, using actual restriction of scalars.
Source: blueprint order 2146, second display (blueprint: def-sf-integral-verdier-models). -/
def finiteTerms (K : Ambient l E X) (n : ℕ) : Ambient l E X :=
  (scalarReductionDerivedRestriction l E X n).obj
    ((finiteDual l E X n (integralDualizingFiniteTerm l E D X n)).obj
      (op ((scalarReductionDerivedExtension l E X n).obj K)))

/-- Restrict the evaluation-defined comparison, using its asserted invertibility.
Source: blueprint order 2146, reconstruction (blueprint: def-sf-integral-verdier-models). -/
def restrictedComparison
    {a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl)}
    (m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n)
    (K : Ambient l E X)
    (h : ∀ n : ℕ, IsIso (comparison l E X D hl (m n) ω r K)) (n : ℕ) :
    (sfDerivedReductionRestricted l E X n).obj ((dual l E X ω.obj).obj (op K)) ≅
      finiteTerms l E X D K n :=
  (scalarReductionDerivedRestriction l E X n).mapIso
    (@asIso _ _ _ _ (comparison l E X D hl (m n) ω r K) (h n))

/-- The finite-dual transition in the completed-coefficient category. This is the
comparison transport of the actual quotient transition, not a chosen tower on the
same objects. The evaluation and transpose equations of the theorem identify it
with the transition induced by finite evaluation and dualizing reduction.
Source: blueprint order 2146, proof step 4 (blueprint: def-sf-integral-verdier-models). -/
def finiteTransition
    {a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl)}
    (m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n)
    (K : Ambient l E X)
    (h : ∀ n : ℕ, IsIso (comparison l E X D hl (m n) ω r K)) (n : ℕ) :
    finiteTerms l E X D K (n + 1) ⟶ finiteTerms l E X D K n :=
  (restrictedComparison l E X D hl m ω r K h (n + 1)).inv ≫
    (sfDerivedReductionTransition l E X n).app ((dual l E X ω.obj).obj (op K)) ≫
      (restrictedComparison l E X D hl m ω r K h n).hom

/-- The specified reduction leg to the finite dual.
Source: blueprint order 2146, proof step 4 (blueprint: def-sf-integral-verdier-models). -/
def finiteLeg
    {a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl)}
    (m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n)
    (K : Ambient l E X)
    (h : ∀ n : ℕ, IsIso (comparison l E X D hl (m n) ω r K)) (n : ℕ) :
    (dual l E X ω.obj).obj (op K) ⟶ finiteTerms l E X D K n :=
  (sfDerivedReductionUnit l E X n).app ((dual l E X ω.obj).obj (op K)) ≫
    (restrictedComparison l E X D hl m ω r K h n).hom

/-- Finite evaluation, adjointed back to completed coefficients. This explicitly
uses reduction of K and the reduction/restriction counit, so it is finite evaluation
with its input reduced, rather than an evaluation on an unrelated ambient object.
Source: blueprint order 2146, proof step 4 (blueprint: def-sf-integral-verdier-models). -/
def finiteEvaluation
    {a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl)}
    (m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (K : Ambient l E X) (n : ℕ) :
    a.tensor.obj (K, finiteTerms l E X D K n) ⟶
      (scalarReductionDerivedRestriction l E X n).obj
        (integralDualizingFiniteTerm l E D X n) :=
  (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose.homEquiv _ _
    ((m n).mu.hom.app (K, finiteTerms l E X D K n) ≫
      (m n).target.tensor.map
        (Prod.mkHom (𝟙 ((scalarReductionDerivedExtension l E X n).obj K))
          ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose.counit.app
            ((finiteDual l E X n (integralDualizingFiniteTerm l E D X n)).obj
              (op ((scalarReductionDerivedExtension l E X n).obj K))))) ≫
      ((m n).target.adjunction ((scalarReductionDerivedExtension l E X n).obj K)).counit.app
        (integralDualizingFiniteTerm l E D X n))

/-- The specified finite dualizing transition transported through its reductions.
Source: blueprint order 2146, proof step 4 (blueprint: def-sf-integral-verdier-models). -/
def dualizingTransition (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n) (n : ℕ) :
    (scalarReductionDerivedRestriction l E X (n + 1)).obj
        (integralDualizingFiniteTerm l E D X (n + 1)) ⟶
      (scalarReductionDerivedRestriction l E X n).obj (integralDualizingFiniteTerm l E D X n) :=
  ((scalarReductionDerivedRestriction l E X (n + 1)).mapIso (r (n + 1))).inv ≫
    (sfDerivedReductionTransition l E X n).app ω.obj ≫
      ((scalarReductionDerivedRestriction l E X n).mapIso (r n)).hom

/-- Every clause of integral Verdier duality for the ambient internal Hom.
Tensor presentations and signed symmetries are supplied as part of the conclusion;
their representative normalizations fix evaluation and its transposes.
Source: blueprint order 2146 (blueprint: def-sf-integral-verdier-conclusion-predicate). -/
def Conclusion (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n) : Prop :=
  ∃ (tensor : IntegralHom.TensorPresentation.{u, u} X
    (completedIntegralCommRingSheaf l E X D hl)),
  ∃ (symmetry : SignedSymmetry X (completedIntegralCommRingSheaf l E X D hl) tensor),
  ∃ (reduction : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl tensor n),
  ∃ (finiteSymmetry : ∀ n : ℕ,
    SignedSymmetry X (integralCoefficientCommRingSheaf l E X n) (reduction n).target),
  ∃ (_categories_equal : sfIntegralConstructible l E X = finiteTorConstructibleIntegral l E X),
  ∃ (preservation : ∀ K : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E X ((dual l E X ω.obj).obj (op K.obj))),
  ∃ (_anti_equivalence : (restrictedDual l E X ω.obj preservation).IsEquivalence),
  ∃ (_exact : ∃ s : (dual l E X ω.obj).CommShift ℤ,
    ∀ T : CategoryTheory.Pretriangulated.Triangle (Ambient l E X)ᵒᵖ,
      sfIntegralConstructible l E X T.obj₁.unop →
      sfIntegralConstructible l E X T.obj₂.unop →
      sfIntegralConstructible l E X T.obj₃.unop →
      T ∈ distTriang (Ambient l E X)ᵒᵖ →
      CategoryTheory.Pretriangulated.Triangle.mk
        ((dual l E X ω.obj).map T.mor₁) ((dual l E X ω.obj).map T.mor₂)
        ((dual l E X ω.obj).map T.mor₃ ≫
          (s.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈
        distTriang (Ambient l E X)),
  ∃ (comparisons : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    IsIso (comparison l E X D hl (reduction n) ω r K.obj)),
  ∃ (_evaluation : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    (reduction n).target.tensor.map
        (Prod.mkHom (𝟙 ((scalarReductionDerivedExtension l E X n).obj K.obj))
          (comparison l E X D hl (reduction n) ω r K.obj)) ≫
      ((reduction n).target.adjunction
        ((scalarReductionDerivedExtension l E X n).obj K.obj)).counit.app
          (integralDualizingFiniteTerm l E D X n) =
    (reduction n).mu.inv.app (K.obj, (dual l E X ω.obj).obj (op K.obj)) ≫
      (scalarReductionDerivedExtension l E X n).map
        ((tensor.adjunction K.obj).counit.app ω.obj) ≫
          (r n).hom),
  ∃ (_transposes : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ)
    (V : Ambient l E X) (f : V ⟶ (dual l E X ω.obj).obj (op K.obj)),
    ((reduction n).target.adjunction
      ((scalarReductionDerivedExtension l E X n).obj K.obj)).homEquiv
        ((scalarReductionDerivedExtension l E X n).obj V)
        (integralDualizingFiniteTerm l E D X n)
        ((reduction n).mu.inv.app (K.obj, V) ≫
          (scalarReductionDerivedExtension l E X n).map
            (((tensor.adjunction K.obj).homEquiv V ω.obj).symm f) ≫
              (r n).hom) =
      (scalarReductionDerivedExtension l E X n).map f ≫
        comparison l E X D hl (reduction n) ω r K.obj),
  ∃ (_transition_evaluation : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    tensor.tensor.map (Prod.mkHom (𝟙 K.obj)
        (finiteTransition l E X D hl reduction ω r K.obj (comparisons K) n)) ≫
      finiteEvaluation l E X D hl reduction K.obj n =
    finiteEvaluation l E X D hl reduction K.obj (n + 1) ≫
      dualizingTransition l E X D ω r n),
  ∃ (_reconstruction : ∀ K : sfIntegralConstructibleCategory l E X,
    ∃ hprod : HasProduct (fun n : ℕ ↦ finiteTerms l E X D K.obj n),
      (fun [_productInst : HasProduct (fun n : ℕ ↦ finiteTerms l E X D K.obj n)] ↦
        ∃ δ : (∏ᶜ fun n : ℕ ↦ finiteTerms l E X D K.obj n) ⟶
            ((dual l E X ω.obj).obj (op K.obj))⟦(1 : ℤ)⟧,
          IsDerivedLimitTriangle
            (finiteTransition l E X D hl reduction ω r K.obj (comparisons K))
            ((dual l E X ω.obj).obj (op K.obj))
            (Pi.lift (finiteLeg l E X D hl reduction ω r K.obj (comparisons K))) δ)
        (_productInst := hprod)),
  ∃ (_tor_bound : ∀ (K : sfIntegralConstructibleCategory l E X) (d : ℕ),
    topologicalKrullDim X ≤ (d : WithBot ℕ∞) → ∀ a b : ℤ, a ≤ b →
    (∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension l E X n).obj K.obj) a b) →
    ∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((scalarReductionDerivedExtension l E X n).obj ((dual l E X ω.obj).obj (op K.obj)))
        (-b - 2 * (d : ℤ)) (-a)),
  ∃ (_reduction_delta : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    (scalarReductionDerivedExtension l E X n).map
        (delta X tensor symmetry ω.obj K.obj) ≫
      comparison l E X D hl (reduction n) ω r
        ((dual l E X ω.obj).obj (op K.obj)) ≫
      (IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
        (Prod.mkHom
          ((@asIso _ _ _ _
            (comparison l E X D hl (reduction n) ω r K.obj) (comparisons K n)).inv.op)
          (𝟙 (integralDualizingFiniteTerm l E D X n))) =
      delta X (reduction n).target (finiteSymmetry n) (integralDualizingFiniteTerm l E D X n)
        ((scalarReductionDerivedExtension l E X n).obj K.obj)),
  ∃ (_biduality : ∀ K : sfIntegralConstructibleCategory l E X,
    IsIso (delta X tensor symmetry ω.obj K.obj)),
  ∀ (K L : sfIntegralConstructibleCategory l E X) (f : K ⟶ L),
    f.hom ≫ delta X tensor symmetry ω.obj L.obj =
      delta X tensor symmetry ω.obj K.obj ≫
        (dual l E X ω.obj).map ((dual l E X ω.obj).map f.hom.op).op

end WeilConjectures.IntegralVerdier
