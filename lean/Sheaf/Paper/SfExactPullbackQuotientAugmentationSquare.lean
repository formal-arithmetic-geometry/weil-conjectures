/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.CategoryTheory.DerivedCategory.ConstantTowerNormalization
public import Sheaf.CategoryTheory.UnboundedExactAdjunctionSquare
public import Sheaf.Paper.StrictQuotientPullbackComputation
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Sheaf.Algebra.Homology.DiagramKFlatReplacements

/-! # The normalized strict quotient-augmentation square

Source: blueprint localization, returned Step 6, retained normalization Steps 4--5;
Stacks Tag 06XN, dual part
(blueprint: lem-sf-exact-pullback-quotient-augmentation-square).

The universal pairs below are arbitrary specified pairs. The exact comparison is
constructed by localization of the identity commuting constant towers with the functor.
The augmentation uses the published quotient transitions and section map, and all
comparison equations are in the derived category of strict towers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.SfExactPullbackQuotient

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- Levelwise application of the specified exact functor.
Source: localization normalization Step 4
(blueprint: lem-sf-exact-pullback-quotient-augmentation-square). -/
abbrev exactTowerFunctor
    (F : pbcModules X (pbcAdicCompletion X d) ⥤ pbcModules Y (pbcAdicCompletion Y d)) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj F

variable (F : pbcModules X (pbcAdicCompletion X d) ⥤ pbcModules Y (pbcAdicCompletion Y d))
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Finite limits of the levelwise exact functor use the shape-wise Mathlib instance.
Source: localization normalization Step 4; Stacks 02MZ
(blueprint: lem-sf-exact-pullback-quotient-augmentation-square). -/
instance exactTowerFiniteLimits : PreservesFiniteLimits (exactTowerFunctor d F) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- Finite colimits of the levelwise exact functor use the shape-wise Mathlib instance.
Source: localization normalization Step 4; Stacks 02MZ
(blueprint: lem-sf-exact-pullback-quotient-augmentation-square). -/
instance exactTowerFiniteColimits : PreservesFiniteColimits (exactTowerFunctor d F) where
  preservesFiniteColimits _ _ _ := inferInstance

/-- The localized strict quotient augmentation with a specified representative of K.
Source: localization normalization Step 5; its chain map is x ↦ x tensor 1
(blueprint: lem-sf-exact-pullback-quotient-augmentation-square). -/
def quotientAugmentation (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
    (P : CbcStrictKFlatRepresentative d X) (i : DerivedCategory.Q.obj P.complex ≅ K) :
    (completedDerivedConstant d X).obj K ⟶
      DerivedCategory.Q.obj ((cbcStrictReduction d X).obj P.complex) :=
  (completedDerivedConstant d X).map i.inv ≫
    (completedTowerConstant d X).mapDerivedCategoryFactors.hom.app P.complex ≫
    DerivedCategory.Q.map (cbcStrictAugmentation d X P.complex)

variable (L : DerivedCategory (pbcModules X (pbcAdicCompletion X d)) ⥤
    DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
  (Lt : DerivedCategory (pbcTowers X (pbcAdicCompletion X d)) ⥤
    DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)))
  (b : Functor.ConstantTowerDerivedComparison L Lt)

/-- The strict pulled-back augmentation beta_K with the specified constant comparison b.
Source: localization normalization Step 5
(blueprint: lem-sf-exact-pullback-quotient-augmentation-square). -/
def pulledAugmentation (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
    (P : CbcStrictKFlatRepresentative d X) (i : DerivedCategory.Q.obj P.complex ≅ K) :=
  b.hom.app K ≫ Lt.map (quotientAugmentation d K P i)

/-- The exact augmentation beta^F_K, without resolving the quotient levels.
Source: localization normalization Step 5; Stacks 015F
(blueprint: lem-sf-exact-pullback-quotient-augmentation-square). -/
def exactAugmentation (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
    (P : CbcStrictKFlatRepresentative d X) (i : DerivedCategory.Q.obj P.complex ≅ K) :=
  (CategoryTheory.UnboundedExactTower.constantInterchange F).inv.app K ≫
    (exactTowerFunctor d F).mapDerivedCategory.map (quotientAugmentation d K P i)

/-- The resolved comparison chi_r, using the supplied complex-level counit tau.
Source: localization normalization Step 5; Stacks 06XN
(blueprint: lem-sf-exact-pullback-quotient-augmentation-square). -/
def resolutionComparison
    (τ : DerivedCategory.Q ⋙ Lt ⟶
      (completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (P : CbcStrictKFlatRepresentative d X) (r : CbcStrictQuotientResolution d P) :=
  letI := r.quasiIso
  inv (Lt.map (DerivedCategory.Q.map r.arrow)) ≫ τ.app r.complex

/-- Constant-tower normalization, computation of the actual quotient augmentation,
and its exact comparison square, independent of representatives and strict resolutions.

Source: localization returned Step 6, retained normalization Steps 4--5;
Stacks Tag 06XN, dual part
(blueprint: lem-sf-exact-pullback-quotient-augmentation-square).

Proof:
1. Put b' = Delta(e) followed by c followed by E inverse. The identity on complexes
   defining c lifts through exact localization (lem-weil-pbc-localization-universal-property).
   Compose its representative equation with the two assumed counit normalizations.
   Cancel Q(m) and obtain the same constant-tower counit equation as for b.
   Uniqueness in lem-cbc-derived-constant-tower-normalization gives b' = b.
2. By lem-cbc-strict-quotient-pullback-computation the actual resolved augmentation
   is w_P = tau_(Delta P) inverse followed by Lt(Q a_P). Its source identification
   is the constant ordinary counit. The normalization of b identifies that composite
   with b followed by Lt(a_K). Exact termwise descent gives c followed by F_Tow(a_K)
   (lem-weil-pbc-exact-functor-derived-factorization).
3. Naturality of E at a_K and Step 1 give the displayed strict-tower square.
4. The strict quotient-pullback computation gives chi_r = Lt(Qr) inverse followed by
   tau_H, and its naturality identifies w_P in every strict resolution, with the
   canonical chi_r inverse followed by chi_s comparison. For representatives use
   R(f) a_P = a_P' Delta(f) and homotopicality of coefficient augmentation
   (lem-cbc-strict-coefficient-augmentation-homotopicality). Quasi-isomorphisms have
   common denominators by lem-pur-quasi-isos-saturated-triangulated; replace a common
   source by a K-flat flat-term complex using lem-weil-pbc-diagram-kflat-replacements.
   Thus the augmented arrows agree through the canonical reduction-tower counits.
   No quotient complex is required to be K-flat, and K need not be complete. -/
theorem quotient_augmentation_square
    (m : completedModulePullback g d ≅ F)
    (ε : DerivedCategory.Q ⋙ L ⟶
      (completedModulePullback g d).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (_hL : L.IsLeftDerivedFunctor ε
      (HomologicalComplex.quasiIso (pbcModules X (pbcAdicCompletion X d)) (.up ℤ)))
    (τ : DerivedCategory.Q ⋙ Lt ⟶
      (completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (_hLt : Lt.IsLeftDerivedFunctor τ
      (HomologicalComplex.quasiIso (pbcTowers X (pbcAdicCompletion X d)) (.up ℤ)))
    (_hε : ∀ P : CbcStrictKFlatRepresentative d X, IsIso (ε.app P.complex))
    (_hτ : ∀ H : CochainComplex (pbcTowers X (pbcAdicCompletion X d)) ℤ,
      (∀ n : ℕ, @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        X.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} X.ProEt)
        (ProEt.topology X) (pbcAdicCompletion X d) (H.asFunctor.obj (op n))) →
      (∀ (n : ℕ) (q : ℤ), SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (C := X.ProEt) (J := ProEt.topology X) (R := pbcAdicCompletion X d)
        ((H.X q).obj (op n))) → IsIso (τ.app H))
    (e : L ≅ F.mapDerivedCategory) (E : Lt ≅ (exactTowerFunctor d F).mapDerivedCategory)
    (_he : ∀ P : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ,
      e.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P =
        ε.app P ≫ DerivedCategory.Q.map ((NatIso.mapHomologicalComplex m (.up ℤ)).hom.app P))
    (_hE : ∀ H : CochainComplex (pbcTowers X (pbcAdicCompletion X d)) ℤ,
      E.hom.app (DerivedCategory.Q.obj H) ≫
          (exactTowerFunctor d F).mapDerivedCategoryFactors.hom.app H =
        τ.app H ≫ DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso m) (.up ℤ)).hom.app H))
    (_hb : ∀ P : CbcStrictKFlatRepresentative d X,
      Functor.IsConstantTowerRepresentativeNormalized (completedModulePullback g d)
        L ε Lt τ b P.complex) :
    (∀ K : DerivedCategory (pbcModules X (pbcAdicCompletion X d)),
      b.hom.app K ≫ E.hom.app ((completedDerivedConstant d X).obj K) =
        (completedDerivedConstant d Y).map (e.hom.app K) ≫
          (CategoryTheory.UnboundedExactTower.constantInterchange F).inv.app K) ∧
    (∀ (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
        (P : CbcStrictKFlatRepresentative d X) (i : DerivedCategory.Q.obj P.complex ≅ K),
      pulledAugmentation d L Lt b K P i ≫
          E.hom.app (DerivedCategory.Q.obj ((cbcStrictReduction d X).obj P.complex)) =
        (completedDerivedConstant d Y).map (e.hom.app K) ≫ exactAugmentation d F K P i) ∧
    ∃ (δ : ∀ P : CbcStrictKFlatRepresentative d X,
        Lt.obj (DerivedCategory.Q.obj ((cbcStrictDelta d X).obj P.complex)) ≅
          DerivedCategory.Q.obj
            ((cbcStrictPull d g).obj ((cbcStrictDelta d X).obj P.complex)))
      (χ : ∀ (P : CbcStrictKFlatRepresentative d X) (r : CbcStrictQuotientResolution d P),
        Lt.obj (DerivedCategory.Q.obj ((cbcStrictReduction d X).obj P.complex)) ≅
          DerivedCategory.Q.obj ((cbcStrictPull d g).obj r.complex))
      (ρ : ∀ P : CbcStrictKFlatRepresentative d X,
        (completedReductionTower X d).obj (DerivedCategory.Q.obj P.complex) ≅
          DerivedCategory.Q.obj ((cbcStrictReduction d X).obj P.complex)),
      (∀ P : CbcStrictKFlatRepresentative d X,
        (δ P).hom = τ.app ((cbcStrictDelta d X).obj P.complex)) ∧
      (∀ (P : CbcStrictKFlatRepresentative d X) (r : CbcStrictQuotientResolution d P),
        (χ P r).hom = resolutionComparison d g Lt τ P r) ∧
      (∀ P : CbcStrictKFlatRepresentative d X,
        (ρ P).hom = completedReductionTowerComplexCounit X d P.complex) ∧
      (∀ (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
          (P : CbcStrictKFlatRepresentative d X) (i : DerivedCategory.Q.obj P.complex ≅ K),
        (completedDerivedConstant d Y).map (L.map i.inv) ≫
            (Functor.constantTowerDerivedSourceCounit
              (completedModulePullback g d) L ε).app P.complex ≫
            cbcStrictPulledAugmentation d g Lt P (δ P) =
          pulledAugmentation d L Lt b K P i) ∧
      (∀ (P : CbcStrictKFlatRepresentative d X) (r : CbcStrictQuotientResolution d P),
        cbcStrictPulledAugmentation d g Lt P (δ P) ≫ (χ P r).hom ≫
            DerivedCategory.Q.map ((cbcStrictPull d g).map r.arrow) =
          DerivedCategory.Q.map ((cbcStrictPull d g).map (cbcStrictAugmentation d X P.complex))) ∧
      (∀ (P : CbcStrictKFlatRepresentative d X) (r s : CbcStrictQuotientResolution d P),
        (cbcStrictPulledAugmentation d g Lt P (δ P) ≫ (χ P r).hom) ≫
            ((χ P r).symm ≪≫ χ P s).hom =
          cbcStrictPulledAugmentation d g Lt P (δ P) ≫ (χ P s).hom) ∧
      (∀ (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
          (P P' : CbcStrictKFlatRepresentative d X)
          (i : DerivedCategory.Q.obj P.complex ≅ K) (i' : DerivedCategory.Q.obj P'.complex ≅ K),
        pulledAugmentation d L Lt b K P i ≫ Lt.map
            (((ρ P).symm ≪≫ (completedReductionTower X d).mapIso (i ≪≫ i'.symm) ≪≫
              ρ P').hom) = pulledAugmentation d L Lt b K P' i' ∧
        exactAugmentation d F K P i ≫ (exactTowerFunctor d F).mapDerivedCategory.map
            (((ρ P).symm ≪≫ (completedReductionTower X d).mapIso (i ≪≫ i'.symm) ≪≫
              ρ P').hom) = exactAugmentation d F K P' i') := by
  sorry

end AlgebraicGeometry.Scheme.SfExactPullbackQuotient
