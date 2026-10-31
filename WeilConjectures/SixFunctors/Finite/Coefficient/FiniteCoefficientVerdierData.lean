/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
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
public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDualitySiteComparison
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.Finite.FiniteDualizing
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final

/-! # Finite coefficient change for Verdier duality

Source: Weil conjectures blueprint, `sec-six-functors/sk-prop-sf-biduality-general`,
node `cor-coef-finite-verdier` (blueprint: cor-coef-finite-verdier).

## Main definitions

* `FiniteVerdierCoherentComparison`: the evaluation, biduality, identity and cocycle diagrams.
* `FiniteVerdierSiteComparison`: those diagrams with the normalized scalar tensorator.
* `FiniteCoefficientVerdierComparison`: specialization to both finite coefficient sites.

The theorem is supplied by `WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientVerdier`, which
publicly re-exports this definition module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry

namespace WeilConjectures

open AlgebraicGeometry.ProEtale

/-- Ordinary scalar extension on either of the two finite-coefficient sites.
Source: blueprint cor-coef-finite-verdier, proof step 6, ordinary balanced tensor.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierOrdinaryExtension
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) :=
  Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)

/-- The ordinary scalar adjunction, with its actual sectionwise unit.
Source: blueprint cor-coef-finite-verdier, proof step 6.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierOrdinaryAdjunction
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) : finiteVerdierOrdinaryExtension J φ ⊣ Sheaf.restrictScalars J φ :=
  Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

/-- Additivity inherited from the ordinary scalar adjunction.
Source: blueprint cor-coef-finite-verdier, proof step 6.
(blueprint: cor-coef-finite-verdier). -/
instance finiteVerdierOrdinaryExtension_additive
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) : (finiteVerdierOrdinaryExtension J φ).Additive :=
  (finiteVerdierOrdinaryAdjunction J φ).left_adjoint_additive

/-- The oplax structure is ordinary scalar balancing, rather than a free tensorator.
Source: blueprint cor-coef-finite-verdier, proof step 6.
(blueprint: cor-coef-finite-verdier). -/
instance finiteVerdierOrdinaryExtension_oplax
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) : (finiteVerdierOrdinaryExtension J φ).OplaxMonoidal :=
  composeAndSheafifyOplaxMonoidal J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

/-- The adjunct of the localized ordinary scalar unit, with the abelian structures
shared before specializing to sheaves. This is a construction, not an assumed map.
Source: blueprint cor-coef-finite-verdier, proof steps 1 and 6.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierScalarRepresentativeAux
    {C : Type v} [Category.{u + 1} C] [Abelian C] [HasDerivedCategory.{u + 1} C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [HasDerivedCategory.{u + 1} D]
    (L : C ⥤ D) [L.Additive] (R : D ⥤ C) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (ordinary : L ⊣ R) {S : DerivedCategory C ⥤ DerivedCategory D}
    (derived : S ⊣ R.mapDerivedCategory) (P : CochainComplex C ℤ) :
    S.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj P) :=
  (derived.homEquiv _ _).symm
    (DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso C (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex ordinary.unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ R)) (.up ℤ)).inv.app P) ≫
      R.mapDerivedCategoryFactors.inv.app ((L.mapHomologicalComplex (.up ℤ)).obj P))

/-- The derived scalar counit on a cochain representative. This is the adjunct of
localizing the ordinary unit, so it fixes the scalar tensor normalization without
assuming flatness of the quotient.
Source: blueprint cor-coef-finite-verdier, proof steps 1 and 6.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierScalarRepresentative
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ) :
    (pbcFixedScalarExtension J φ).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((finiteVerdierOrdinaryExtension J φ).mapHomologicalComplex (.up ℤ)).obj P) :=
  finiteVerdierScalarRepresentativeAux
    (finiteVerdierOrdinaryExtension J φ) (Sheaf.restrictScalars J φ)
    (finiteVerdierOrdinaryAdjunction J φ)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J φ)) P

/-- The coefficient compatibility diagrams with all ambient structures shared explicitly.
This helper is specialized below to the two prescribed derived module categories.
Source: blueprint cor-coef-finite-verdier, proof steps 2--6.
(blueprint: cor-coef-finite-verdier). -/
def FiniteVerdierCoherentComparison
    (V : ℕ → Type v) [∀ n, Category.{w} (V n)]
    (T : ∀ n, V n ⥤ V n ⥤ V n) (H : ∀ n, (V n)ᵒᵖ ⥤ V n ⥤ V n)
    (W : ∀ n, V n) (P : ∀ n, ObjectProperty (V n))
    (Tor : ∀ n, ℤ → ℤ → ObjectProperty (V n))
    (S : ∀ {n m : ℕ}, m ≤ n → V n ⥤ V m)
    (unit : ∀ n, S (le_refl n) ≅ 𝟭 (V n))
    (comp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m), S h ⋙ S g ≅ S (g.trans h))
    (μ : ∀ {n m : ℕ} (h : m ≤ n),
      Functor.uncurry.obj (T n) ⋙ S h ≅
        (S h).prod (S h) ⋙ Functor.uncurry.obj (T m))
    (ev : ∀ n (K : V n), ((T n).obj (((H n).obj (op K)).obj (W n))).obj K ⟶ W n)
    (δ : ∀ n (K : V n),
      K ⟶ (dualityDoubleFunctor (H n) (W n)).obj K)
    (uMap : ∀ {n m : ℕ} (h : m ≤ n), (S h).obj (W n) ⟶ W m) (d : ℕ) : Prop :=
  ∃ comparison : ∀ {n m : ℕ} (h : m ≤ n),
      (H n).flip.obj (W n) ⋙ S h ⟶
        (S h).op ⋙ (H m).flip.obj (W m),
    (∀ {n m : ℕ} (h : m ≤ n) (K : V n), P n K →
      P m ((S h).obj K) ∧ IsIso ((comparison h).app (op K)) ∧
      ((T m).map ((comparison h).app (op K))).app ((S h).obj K) ≫ ev m ((S h).obj K) =
        (μ h).inv.app ((((H n).obj (op K)).obj (W n)), K) ≫
          (S h).map (ev n K) ≫ uMap h ∧
      (S h).map (δ n K) ≫
          (comparison h).app (op (((H n).obj (op K)).obj (W n))) =
        δ m ((S h).obj K) ≫
          ((H m).flip.obj (W m)).map (((comparison h).app (op K)).op) ∧
      (∀ a b : ℤ, a ≤ b → Tor n a b K →
        Tor m (-b - 2 * (d : ℤ)) (-a)
          ((S h).obj (((H n).obj (op K)).obj (W n))) ∧
        Tor m (-b - 2 * (d : ℤ)) (-a)
          (((H m).obj (op ((S h).obj K))).obj (W m)))) ∧
    (∀ (n : ℕ) (K : V n), P n K → (comparison (le_refl n)).app (op K) =
      (unit n).hom.app (((H n).obj (op K)).obj (W n)) ≫
        ((H n).flip.obj (W n)).map (((unit n).hom.app K).op)) ∧
    (∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m) (K : V n), P n K →
      (S g).map ((comparison h).app (op K)) ≫
          (comparison g).app (op ((S h).obj K)) ≫
          ((H r).flip.obj (W r)).map (((comp h g).inv.app K).op) =
        (comp h g).hom.app (((H n).obj (op K)).obj (W n)) ≫
          (comparison (g.trans h)).app (op K))

/-- The complete coefficient comparison on one fixed site. The dualizing maps `uMap`,
evaluations `ev`, and transposes `δ` are fixed before the comparisons are quantified.
The tensorator is normalized on ordinary cochain representatives, using the published
normalization predicate. Invertibility is asserted only on `P`, never on the whole
unbounded category. The two final equations are the identity and quotient cocycle,
with the canonical scalar associators displayed.
Source: blueprint cor-coef-finite-verdier, all clauses and proof steps 2--6.
(blueprint: cor-coef-finite-verdier). -/
def FiniteVerdierSiteComparison
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    (R : ℕ → Type (u + 1)) [∀ n, CommRing (R n)]
    (φ : ∀ {n m : ℕ}, m ≤ n → R n →+* R m)
    (φId : ∀ n, φ (le_refl n) = RingHom.id (R n))
    (φComp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m),
      φ (g.trans h) = (φ g).comp (φ h))
    (W : ∀ n : ℕ, DerivedCategory (Sheaf J (ModuleCat.{u + 1}
      (R n))))
    (P : ∀ n : ℕ, ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1}
      (R n)))))
    (Tor : ∀ n : ℕ, ℤ → ℤ → ObjectProperty (DerivedCategory
      (Sheaf J (ModuleCat.{u + 1} (R n)))))
    (T : ∀ n : ℕ,
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R n))) ⥤
        DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R n))) ⥤
          DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R n))))
    (H : ∀ n : ℕ,
      (DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R n))))ᵒᵖ ⥤
        DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R n))) ⥤
          DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R n))))
    (ev : ∀ (n : ℕ) (K : DerivedCategory
      (Sheaf J (ModuleCat.{u + 1} (R n)))),
      ((T n).obj (((H n).obj (op K)).obj (W n))).obj K ⟶ W n)
    (δ : ∀ (n : ℕ) (K : DerivedCategory
      (Sheaf J (ModuleCat.{u + 1} (R n)))),
      K ⟶ (dualityDoubleFunctor (H n) (W n)).obj K)
    (uMap : ∀ {n m : ℕ} (h : m ≤ n),
      (pbcFixedScalarExtension J (φ h)).obj (W n) ⟶ W m)
    (d : ℕ) : Prop :=
  letI {n m : ℕ} (h : m ≤ n) : (finiteVerdierOrdinaryExtension J (φ h)).IsLeftAdjoint :=
    (finiteVerdierOrdinaryAdjunction J (φ h)).isLeftAdjoint
  ∃ μ : ∀ {n m : ℕ} (h : m ≤ n),
      Functor.uncurry.obj (T n) ⋙ pbcFixedScalarExtension J (φ h) ≅
        (pbcFixedScalarExtension J (φ h)).prod (pbcFixedScalarExtension J (φ h)) ⋙
          Functor.uncurry.obj (T m),
    (∀ {n m : ℕ} (h : m ≤ n), ∃ e,
      Etale.ExceptionalCoefficients.TensorNormalizationAux
        (finiteVerdierOrdinaryExtension J (φ h)) (pbcFixedScalarExtension J (φ h))
        (finiteVerdierScalarRepresentative J (φ h)) e ∧ HEq (μ h) e) ∧
    @FiniteVerdierCoherentComparison
      (fun n ↦ DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R n))))
      (fun _n ↦ inferInstance) T H W P Tor
      (fun {_ _} h ↦ pbcFixedScalarExtension J (φ h))
      (fun n ↦ normalizedOriginScalarUnit J (φ (le_refl n)) (φId n))
      (fun {_ _ _} h g ↦ pbcFixedScalarExtensionComp J (φ h) (φ g) (φ (g.trans h))
        (φComp h g)) μ ev δ (fun {_ _} h ↦ uMap h) d

/-- Evaluation projected from the recorded, normalized etale pairing.
The coefficient category is shared before specializing to modules.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierEtaleEvaluation
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) {W : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (h : Etale.AmbientDualityPairing A X W)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((Etale.derivedTensor A X).obj (((Etale.derivedHom A X).obj (op K)).obj W)).obj K ⟶ W :=
  h.choose_spec.2.choose K

/-- Evaluation projected from the recorded, normalized pro-etale pairing.
The coefficient category is shared before specializing to modules.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4 and 7.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierProEtaleEvaluation
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) {W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (h : ProEtale.AmbientDualityPairing A X W)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((ProEtale.derivedTensor A X).obj
      (((ProEtale.derivedHom A X).obj (op K)).obj W)).obj K ⟶ W :=
  h.choose_spec.2.choose K

/-- The recorded pro-etale double-dual arrow with the published Hom wrapper.
Source: blueprint cor-coef-finite-verdier, proof step 4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierProEtaleBiduality
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) {W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (h : ProEtale.AmbientDualityPairing A X W)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    K ⟶ (dualityDoubleFunctor (ProEtale.derivedHom A X) W).obj K :=
  ProEtale.AmbientDualityPairing.bidualityMap A X h K

/-- The published Etale derived tensor, with the module coefficient structures shared.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierEtaleTensorAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  Etale.derivedTensor (ModuleCat.{u + 1} R) X

/-- The published Etale derived hom, with the module coefficient structures shared.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierEtaleHomAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :
    (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))ᵒᵖ ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  Etale.derivedHom (ModuleCat.{u + 1} R) X

/-- The recorded normalized Etale pairing, specialized to module coefficients.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierEtalePairingAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    (W : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) : Prop :=
  Etale.AmbientDualityPairing (ModuleCat.{u + 1} R) X W

/-- The specified Etale evaluation at module coefficients.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierEtaleEvaluationAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    {W : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))}
    (h : finiteVerdierEtalePairingAt R X W)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    ((finiteVerdierEtaleTensorAt R X).obj
      (((finiteVerdierEtaleHomAt R X).obj (op K)).obj W)).obj K ⟶
      W :=
  finiteVerdierEtaleEvaluation (ModuleCat.{u + 1} R) X h K

/-- The specified Etale transpose of evaluation at module coefficients.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierEtaleBidualityAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    {W : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))}
    (h : finiteVerdierEtalePairingAt R X W)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    K ⟶ (dualityDoubleFunctor (finiteVerdierEtaleHomAt R X) W).obj K :=
  Etale.AmbientDualityPairing.bidualityMap (ModuleCat.{u + 1} R) X h K

/-- The published ProEtale derived tensor, with the module coefficient structures shared.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierProEtaleTensorAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) :=
  ProEtale.derivedTensor (ModuleCat.{u + 1} R) X

/-- The published ProEtale derived hom, with the module coefficient structures shared.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierProEtaleHomAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :
    (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)))ᵒᵖ ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)) :=
  ProEtale.derivedHom (ModuleCat.{u + 1} R) X

/-- The recorded normalized ProEtale pairing, specialized to module coefficients.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierProEtalePairingAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    (W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))) : Prop :=
  ProEtale.AmbientDualityPairing (ModuleCat.{u + 1} R) X W

/-- The specified ProEtale evaluation at module coefficients.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierProEtaleEvaluationAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    {W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))}
    (h : finiteVerdierProEtalePairingAt R X W)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))) :
    ((finiteVerdierProEtaleTensorAt R X).obj
      (((finiteVerdierProEtaleHomAt R X).obj (op K)).obj W)).obj K ⟶
      W :=
  finiteVerdierProEtaleEvaluation (ModuleCat.{u + 1} R) X h K

/-- The specified ProEtale transpose of evaluation at module coefficients.
Source: blueprint cor-coef-finite-verdier, proof steps 3--4.
(blueprint: cor-coef-finite-verdier). -/
def finiteVerdierProEtaleBidualityAt (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    {W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))}
    (h : finiteVerdierProEtalePairingAt R X W)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))) :
    K ⟶ (dualityDoubleFunctor (finiteVerdierProEtaleHomAt R X) W).obj K :=
  finiteVerdierProEtaleBiduality (ModuleCat.{u + 1} R) X h K

/-- The etale specialization of the full coefficient diagrams.
Source: blueprint cor-coef-finite-verdier, proof steps 2--7.
(blueprint: cor-coef-finite-verdier). -/
def FiniteVerdierEtaleComparison
    (X : Scheme.{u}) (R : ℕ → Type (u + 1)) [∀ n, CommRing (R n)]
    (φ : ∀ {n m : ℕ}, m ≤ n → R n →+* R m)
    (φId : ∀ n, φ (le_refl n) = RingHom.id (R n))
    (φComp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m),
      φ (g.trans h) = (φ g).comp (φ h))
    (W : ∀ n, Etale.DerivedCategoryModule (R n) X)
    (Pet : ∀ n, ObjectProperty (Etale.DerivedCategoryModule (R n) X))
    (_Ppro : ∀ n, ObjectProperty
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (R n)))))
    (TorEt : ∀ n, ℤ → ℤ → ObjectProperty (Etale.DerivedCategoryModule (R n) X))
    (_TorPro : ∀ n, ℤ → ℤ → ObjectProperty
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (R n)))))
    (uEt : ∀ {n m : ℕ} (h : m ≤ n), (Etale.scalarExtension (φ h) X).obj (W n) ⟶ W m)
    (d : ℕ) : Prop :=
  (∃ hEt : ∀ n : ℕ, finiteVerdierEtalePairingAt
      (R n) X (W n),
    @FiniteVerdierSiteComparison _ _ _ X.smallEtaleTopology R
      (fun _n ↦ inferInstance) (fun {_ _} h ↦ φ h)
      φId (fun {_ _ _} h g ↦ φComp h g)
      W
      Pet
      TorEt
      (fun n ↦ finiteVerdierEtaleTensorAt (R n) X)
      (fun n ↦ finiteVerdierEtaleHomAt (R n) X)
      (fun n ↦ finiteVerdierEtaleEvaluationAt (R n) X (hEt n))
      (fun n ↦ finiteVerdierEtaleBidualityAt (R n) X (hEt n))
      (fun {_ _} h ↦ uEt h) d)

/-- The pro-etale specialization, with transported dualizing object and coefficient map.
Source: blueprint cor-coef-finite-verdier, proof steps 2--7.
(blueprint: cor-coef-finite-verdier). -/
def FiniteVerdierProEtaleComparison
    (X : Scheme.{u}) (R : ℕ → Type (u + 1)) [∀ n, CommRing (R n)]
    (φ : ∀ {n m : ℕ}, m ≤ n → R n →+* R m)
    (φId : ∀ n, φ (le_refl n) = RingHom.id (R n))
    (φComp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m),
      φ (g.trans h) = (φ g).comp (φ h))
    (W : ∀ n, Etale.DerivedCategoryModule (R n) X)
    (_Pet : ∀ n, ObjectProperty (Etale.DerivedCategoryModule (R n) X))
    (Ppro : ∀ n, ObjectProperty
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (R n)))))
    (_TorEt : ∀ n, ℤ → ℤ → ObjectProperty (Etale.DerivedCategoryModule (R n) X))
    (TorPro : ∀ n, ℤ → ℤ → ObjectProperty
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (R n)))))
    (uEt : ∀ {n m : ℕ} (h : m ≤ n), (Etale.scalarExtension (φ h) X).obj (W n) ⟶ W m)
    (d : ℕ) : Prop :=
  let F := fun n ↦ (comparisonUpperStar (ModuleCat.{u + 1}
    (R n)) X).mapDerivedCategory
  (∃ hPro : ∀ n : ℕ, finiteVerdierProEtalePairingAt
      (R n) X ((F n).obj (W n)),
    @FiniteVerdierSiteComparison _ _ _ (Scheme.ProEt.topology X) R
      (fun _n ↦ inferInstance) (fun {_ _} h ↦ φ h)
      φId (fun {_ _ _} h g ↦ φComp h g)
      (fun n ↦ (F n).obj (W n))
      Ppro
      TorPro
      (fun n ↦ finiteVerdierProEtaleTensorAt (R n) X)
      (fun n ↦ finiteVerdierProEtaleHomAt (R n) X)
      (fun n ↦ finiteVerdierProEtaleEvaluationAt (R n) X (hPro n))
      (fun n ↦ finiteVerdierProEtaleBidualityAt (R n) X (hPro n))
      (fun {n m} h ↦ (pbcComparisonReduction X (φ h)).hom.app
        (W n) ≫ (F m).map (uEt h)) d)

/-- Both sites with the same coefficient tower and dimension bound.
Source: blueprint cor-coef-finite-verdier, proof steps 2--7.
(blueprint: cor-coef-finite-verdier). -/
def FiniteVerdierTwoSitesComparison
    (X : Scheme.{u}) (R : ℕ → Type (u + 1)) [∀ n, CommRing (R n)]
    (φ : ∀ {n m : ℕ}, m ≤ n → R n →+* R m)
    (φId : ∀ n, φ (le_refl n) = RingHom.id (R n))
    (φComp : ∀ {n m r : ℕ} (h : m ≤ n) (g : r ≤ m),
      φ (g.trans h) = (φ g).comp (φ h))
    (W : ∀ n, Etale.DerivedCategoryModule (R n) X)
    (Pet : ∀ n, ObjectProperty (Etale.DerivedCategoryModule (R n) X))
    (Ppro : ∀ n, ObjectProperty
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (R n)))))
    (TorEt : ∀ n, ℤ → ℤ → ObjectProperty (Etale.DerivedCategoryModule (R n) X))
    (TorPro : ∀ n, ℤ → ℤ → ObjectProperty
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (R n)))))
    (uEt : ∀ {n m : ℕ} (h : m ≤ n), (Etale.scalarExtension (φ h) X).obj (W n) ⟶ W m)
    (d : ℕ) : Prop :=
  FiniteVerdierEtaleComparison X R (fun {_ _} h ↦ φ h) φId
    (fun {_ _ _} h g ↦ φComp h g) W Pet Ppro TorEt TorPro (fun {_ _} h ↦ uEt h) d ∧
  FiniteVerdierProEtaleComparison X R (fun {_ _} h ↦ φ h) φId
    (fun {_ _ _} h g ↦ φComp h g) W Pet Ppro TorEt TorPro (fun {_ _} h ↦ uEt h) d

end WeilConjectures
