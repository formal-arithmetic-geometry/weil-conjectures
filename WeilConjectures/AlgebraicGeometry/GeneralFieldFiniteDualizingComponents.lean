/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.FiniteCompactCoefficients.FiniteCoefficientCompactSupportCompatibility
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.FiniteCompactificationTranspose.FiniteRingCompactificationTransposeComparison
public import WeilConjectures.SixFunctors.Etale.Derived.PointUnit
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientOrdinary.FiniteCoefficientOrdinaryDirectImage
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
public import WeilConjectures.AlgebraicGeometry.Support.SupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedOriginScalarComparisons
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.AlgebraicGeometry.OpenScalarOperations.OpenScalarOperations

/-! # Components of the finite dualizing coefficient argument
(blueprint: def-sf-general-field-finite-dualizing-components). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- A proper part of the finite dualizing comparison package.
Source: lem-coef-finite-dualizing.proof.md, the local calculation and site transport
(blueprint: def-sf-general-field-finite-dualizing-components). -/
structure GeneralFieldFiniteDualizingGeometry
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (l : ℕ) (φ : A →+* B) {X S : Scheme.{u}} (a : X ⟶ S)
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] [HasCompactification a]
    [CompactSpace S] : Prop where
  etale_isIso : IsIso (generalFieldFiniteDualizingMap φ a)
  natural_under_isomorphism :
    ∀ {X' S' : Scheme.{u}} (eX : X ≅ X') (eS : S ≅ S')
      (a' : X' ⟶ S') [IsSeparated a'] [LocallyOfFiniteType a'] [QuasiCompact a']
      [HasCompactification a']
      (sq : IsPullback eX.inv a' a eS.inv),
      eX.hom ≫ a' = a ≫ eS.hom →
      ((scalarExtension φ X').map (dualizingComplexBaseChangeMap A sq) ≫
          generalFieldFiniteDualizingMap φ a' =
        (scalarPullbackIso φ eX.inv).inv.app (dualizingComplex A a) ≫
          (upperStar (ModuleCat.{u + 1} B) eX.inv).leftDerivedFunctor.map
            (generalFieldFiniteDualizingMap φ a) ≫
          dualizingComplexBaseChangeMap B sq) ∧
      (letI : EssentiallySmall.{u + 1} X'.ProEt := essentiallySmallSelf.{0, u, u + 1} _
       let C_A :=
         (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
       let C_A' :=
         (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X').mapDerivedCategory
       let C_B' :=
         (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X').mapDerivedCategory
       let κA := ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso
         (ModuleCat.{u + 1} A) eX.inv
       let κB := ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso
         (ModuleCat.{u + 1} B) eX.inv
       let eA := leftDerivedUpperStarIsoMapDerivedCategory
         (ModuleCat.{u + 1} A) eX.inv
       let eB := leftDerivedUpperStarIsoMapDerivedCategory
         (ModuleCat.{u + 1} B) eX.inv
       let T_X' := @Sheaf.fixedCoefficientDerivedScalarExtension.{u} X'.ProEt
         inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
         (Scheme.ProEt.topology X') A B inferInstance inferInstance φ
       let s := generalFieldFiniteProScalarPullbackReverse φ eX.inv
       T_X'.map (κA.hom.app (dualizingComplex A a)) ≫
           T_X'.map (C_A'.map
             (eA.inv.app (dualizingComplex A a) ≫
               dualizingComplexBaseChangeMap A sq)) ≫
         generalFieldFiniteProDualizingMap φ a' =
       s.app (C_A.obj (dualizingComplex A a)) ≫
           (ProEtale.upperStar (ModuleCat.{u + 1} B) eX.inv).mapDerivedCategory.map
             (generalFieldFiniteProDualizingMap φ a) ≫
         κB.hom.app (dualizingComplex B a) ≫
           C_B'.map
             (eB.inv.app (dualizingComplex B a) ≫
               dualizingComplexBaseChangeMap B sq))
  compactification_independent :
    ∀ (c d : Compactification a),
      generalFieldFiniteEtaleDualizingMapAt φ a c =
          generalFieldFiniteEtaleDualizingMapAt φ a d ∧
        generalFieldFiniteEtaleDualizingMapAt φ a c = generalFieldFiniteDualizingMap φ a

/-- A proper part of the finite dualizing comparison package.
Source: lem-coef-finite-dualizing.proof.md, the local calculation and site transport
(blueprint: def-sf-general-field-finite-dualizing-components). -/
structure GeneralFieldFiniteDualizingScalarSite
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (l : ℕ) (φ : A →+* B) {X S : Scheme.{u}} (a : X ⟶ S)
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] [HasCompactification a]
    [CompactSpace S] : Prop where
  pro_identity :
    (letI : EssentiallySmall.{u + 1} X.ProEt :=
        essentiallySmallSelf.{0, u, u + 1} _
     generalFieldFiniteProDualizingMap (RingHom.id A) a =
      (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology X)
        (RingHom.id A) rfl).hom.app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
          (dualizingComplex A a)))
  pro_mixed_square :
    letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    letI : EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    ∀ (c : Compactification a) (K : DerivedCategoryModule A X)
      (_hK : ProEtale.FiniteCompactCoefficients.Input A X K),
      let cP := (generalFieldFiniteProCompactMap φ c).app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)
      IsIso cP ∧
      (Sheaf.fixedCoefficientDerivedScalarExtension (Scheme.ProEt.topology S) φ).map
          ((generalFieldFiniteSiteComparison A c).app K) ≫
        cP ≫
        (ProEtale.FiniteCompactCoefficients.pro B
          c).map
          ((ProEtale.OrdinaryScalarSite.delta φ X).hom.app K) =
      (ProEtale.OrdinaryScalarSite.delta φ S).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c).obj K) ≫
        (ProEtale.FiniteCompactCoefficients.nu B S).map
          ((generalFieldFiniteEtaleCompactMap φ c).app K) ≫
        (generalFieldFiniteSiteComparison B c).app
          ((scalarExtension φ X).obj K)
  pro_counit_equation :
    letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    letI : EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    let c := HasCompactification.compactification a
    let cP := (generalFieldFiniteProCompactMap φ c).app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
        (dualizingComplex A a))
    let F_B := ProEtale.FiniteCompactCoefficients.pro B c
    cP ≫ F_B.map ((ProEtale.OrdinaryScalarSite.delta φ X).hom.app
      (dualizingComplex A a)) ≫
      F_B.map
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
          (generalFieldFiniteDualizingMap φ a)) ≫
      generalFieldFiniteProEpsilon (A := B) a =
    (ProEtale.OrdinaryScalarSite.scalar (Scheme.ProEt.topology S) φ).map
      (generalFieldFiniteProEpsilon a) ≫
      (ProEtale.OrdinaryScalarSite.delta φ S).hom.app
        (𝟙_ (DerivedCategoryModule A S)) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) S).mapDerivedCategory.map
        (ExceptionalCoefficients.unitIso φ S).hom
  pro_site_composition :
    letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
    ∀ {C : Type (u + 1)} [CommRing C] [Finite C]
      (_hAell : ∃ n : ℕ, ∀ x : A, (l ^ n : A) * x = 0)
      (_hBell : ∃ n : ℕ, ∀ x : B, (l ^ n : B) * x = 0)
      (_hCell : ∃ n : ℕ, ∀ x : C, (l ^ n : C) * x = 0)
      (ψ : B →+* C),
      (FiniteCoefficientOrdinary.scalarComposition (Scheme.ProEt.topology X) φ ψ).hom.app
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
            (dualizingComplex A a)) ≫
        generalFieldFiniteProDualizingMap (ψ.comp φ) a =
      (@Sheaf.fixedCoefficientDerivedScalarExtension.{u} X.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) B C
        inferInstance inferInstance ψ).map
          (generalFieldFiniteProDualizingMap φ a) ≫
        generalFieldFiniteProDualizingMap ψ a

end AlgebraicGeometry.Etale
