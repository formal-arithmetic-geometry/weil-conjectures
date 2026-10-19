/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.Paper.IntegralTwistDerivedScalarCanonical
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.IntegralTwistBaseChange
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.PbcCoefficientTwists
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import Sheaf.Paper.PurTwistSheafLocallyFree
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.Algebra.Homology.KFlat
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-! # Coherence of integral twisting and scalar extension

Source: blueprint `prop-weil-twist-preserves`, final integral/common-stage paragraph,
and `lem-weil-scalar-extension-composition`, integral associativity paragraph
(blueprint: lem-weil-integral-twist-scalar-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (S : Scheme.{u}) [∀ x : S, Invertible (l : S.residueField x)]

/-- Bundle the actual twist of C in the full integral category, using the membership
clause of the published twist comparison for the identity coefficient extension.
Source: blueprint `prop-weil-twist-preserves`, integral/common-stage paragraph
(blueprint: lem-weil-integral-twist-scalar-coherence). -/
def integralTwistCoherenceObject (m : ℤ) (C : sfIntegralConstructibleCategory l E S) :
    sfIntegralConstructibleCategory l E S :=
  ⟨(integralSheafTwist l E S m).mapDerivedCategory.obj C.obj,
    ((integral_twist_derived_scalar l E E (AlgHom.id (Padic l) E)
      S m).choose_spec.choose_spec.2.2 C).1⟩

variable (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
  (G : Type u) [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
  (ι : E →ₐ[Padic l] F) (κ : F →ₐ[Padic l] G)

/-- The specified ordinary K-flat model maps to the specified completed extension by
its quotient-completion chain map and the inverse universal resolving comparison.
Source: blueprint `prop-weil-twist-preserves`, integral/common-stage paragraph
(blueprint: lem-weil-integral-twist-scalar-coherence). -/
def integralTwistCoherenceModelMap
    (P : (integralOperationsGoodComplex l E S).FullSubcategory) :
    DerivedCategory.Q.obj ((completedOrdinaryScalarComplex l E F ι S).obj P.obj) ⟶
      (integralScalarExtensionOfUniverses l E F ι S).obj (DerivedCategory.Q.obj P.obj) :=
  DerivedCategory.Q.map ((completedScalarChainComparison l E F ι S).app P.obj) ≫
    (integralScalarExtensionComparisonOfUniverses l E F ι S).inv.app P

/-- The canonical twist/scalar square, its unit normalization and rationalized associator.
Source: blueprint `prop-weil-twist-preserves`, final integral/common-stage paragraph,
and `lem-weil-scalar-extension-composition`, both proof paragraphs
(blueprint: lem-weil-integral-twist-scalar-coherence).

Proof:
1. The signed twist-line maps satisfy the tower equation by integral_twist_base_change.
   The specified completion maps chi are natural and invertible on complete objects.
   The identity twist comparison puts C(m) in the full integral category; scalar
   constructibility puts every successive extension there too.
2. Trivialize the rank-one line. Its tensor powers and duals are inverse tensor
   equivalences, hence exact, flat, and preserve acyclic complexes.
3. Resolve C by a flat-term K-flat P. Twisting P and changing coefficients preserve
   these conditions. Tensor closedness permits rebracketing the total sums; the line
   has degree zero, so there is no new sign.
4. Ordinary associativity sends ((x tensor b) tensor c) to x tensor kappa(b)c,
   with inverse x tensor c to ((x tensor 1) tensor c). Balancing proves the inverse
   equations. Bilinear sheafification extends the formulas to chain isomorphisms.
   They commute with chain maps and descend naturally through K-flat localization.
5. On (((x tensor y) tensor b) tensor c), the two twist paths both give
   (x tensor kappa(b)c) tensor theta(y). The signed line tower equation identifies
   theta_GF(theta_FE(y)) with theta_GE(y). Local tensor generation proves equality
   of chain maps, rather than assuming global pure tensors generate global sections.
6. Write d = chi_GF at B_FE(C) composed with T_GF(chi_FE at C). The prescribed
   completed associator is chi_GE composed with mu composed with inverse d;
   beta is W(chi) composed with alpha composed with inverse chi at W(C).
7. Expand both paths. Naturality moves the intervening chi past beta and alpha;
   adjacent inverse comparisons cancel. The remaining equality is step 5.
   Faithfulness of the full integral inclusion gives the asserted square.
8. For an identity extension, ordinary multiplication sends b tensor x to b*x.
   Both twist-unit paths send (x tensor y) tensor b to bx tensor y = x tensor by.
   The finite-free comparison's identity normalization transports this to completed
   units. The source and target identity associators are the whiskered unit maps.
9. Rationalization tensors Hom groups with the coefficient field and preserves all
   these equations. Naturality extends from integral arrows to pure rational tensors
   and their finite sums. The integral associator has exactly the normalization used
   in sfRationalScalarComp, proving equality with that specified rational map.
-/
theorem integral_twist_scalar_coherence (m : ℤ) :
    (∃ μ : completedDerivedScalarExtension l E F ι S ⋙
        completedDerivedScalarExtension l F G κ S ≅
          completedDerivedScalarExtension l E G (κ.comp ι) S,
      (∀ P : (integralOperationsGoodComplex l E S).FullSubcategory,
        ∃ a : (completedOrdinaryScalarComplex l F G κ S).obj
            ((completedOrdinaryScalarComplex l E F ι S).obj P.obj) ≅
          (completedOrdinaryScalarComplex l E G (κ.comp ι) S).obj P.obj,
          (∀ (i : ℤ) (U : S.ProEtᵒᵖ)
            (b : (completedIntegralCommRingSheafUnrestricted l F S).obj.obj U)
            (c : (completedIntegralCommRingSheafUnrestricted l G S).obj.obj U)
            (x : (P.obj.X i).val.obj U),
            (a.hom.f i).val.app U
                (completedScalarTensorSection l F G κ S _ U c
                  (completedScalarTensorSection l E F ι S _ U b x)) =
              completedScalarTensorSection l E G (κ.comp ι) S _ U
                (c * (completedCoefficientMap l F G κ S).hom.app U b) x) ∧
          (completedDerivedScalarExtension l F G κ S).map
              (completedScalarCounit l E F ι S P.obj) ≫
            completedScalarCounit l F G κ S
              ((completedOrdinaryScalarComplex l E F ι S).obj P.obj) ≫
            DerivedCategory.Q.map a.hom =
          μ.hom.app (DerivedCategory.Q.obj P.obj) ≫
            completedScalarCounit l E G (κ.comp ι) S P.obj) ∧
      ∀ C : sfIntegralConstructibleCategory l E S,
        (completedDerivedScalarExtension l F G κ S).map
            ((completedScalarComparison l E F ι S).app C.obj) ≫
          (completedScalarComparison l F G κ S).app
            ((integralScalarExtensionOfUniverses l E F ι S).obj C.obj) ≫
          ((sfIntegralScalarComp l E F ι S
            (l + 1) (ne_of_lt (Nat.lt_succ_self l)) G κ).hom.app C).hom =
        μ.hom.app C.obj ≫ (completedScalarComparison l E G (κ.comp ι) S).app C.obj) ∧
    (∀ C : sfIntegralConstructibleCategory l E S,
      (integralScalarExtensionOfUniverses l F G κ S).map
          ((integralTwistCompletedBeta l E F ι S m).hom.app C) ≫
        (integralTwistCompletedBeta l F G κ S m).hom.app
          ((sfConstructibleIntegralScalarExtension (l + 1) l (ne_of_lt (Nat.lt_succ_self l))
            E F ι S).obj C) ≫
        (integralSheafTwist l G S m).mapDerivedCategory.map
          ((sfIntegralScalarComp l E F ι S
            (l + 1) (ne_of_lt (Nat.lt_succ_self l)) G κ).hom.app C).hom =
      ((sfIntegralScalarComp l E F ι S (l + 1) (ne_of_lt (Nat.lt_succ_self l)) G κ).hom.app
          (integralTwistCoherenceObject l E S m C)).hom ≫
        (integralTwistCompletedBeta l E G (κ.comp ι) S m).hom.app C) ∧
    (∀ (C : sfIntegralConstructibleCategory l E S)
      (P : (integralOperationsGoodComplex l E S).FullSubcategory)
      (e : DerivedCategory.Q.obj P.obj ≅ C.obj),
      ∃ a : (completedOrdinaryScalarComplex l F G κ S).obj
          ((completedOrdinaryScalarComplex l E F ι S).obj
            (((integralSheafTwist l E S m).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≅
        ((integralSheafTwist l G S m).mapHomologicalComplex (.up ℤ)).obj
          ((completedOrdinaryScalarComplex l E G (κ.comp ι) S).obj P.obj),
        (∀ (i : ℤ) (U : S.ProEtᵒᵖ)
          (b : (completedIntegralCommRingSheafUnrestricted l F S).obj.obj U)
          (c : (completedIntegralCommRingSheafUnrestricted l G S).obj.obj U)
          (x : (P.obj.X i).val.obj U) (y : (integralTwistLine l E S m).val.obj U),
          (a.hom.f i).val.app U
              (completedScalarTensorSection l F G κ S _ U c
                (completedScalarTensorSection l E F ι S _ U b
                  (SheafOfModules.siteSheafTensorTmul
                    (A := completedIntegralCommRingSheafUnrestricted l E S) _ _ U x y))) =
            SheafOfModules.siteSheafTensorTmul
              (A := completedIntegralCommRingSheafUnrestricted l G S) _ _ U
              (completedScalarTensorSection l E G (κ.comp ι) S _ U
                (c * (completedCoefficientMap l F G κ S).hom.app U b) x)
              ((twistScalarMaps l E S G (κ.comp ι) m).val.app U y)) ∧
        (completedDerivedScalarExtension l F G κ S).map
            ((completedDerivedScalarExtension l E F ι S).map
              ((integralSheafTwist l E S m).mapDerivedCategory.map e.inv)) ≫
          (completedDerivedScalarExtension l F G κ S).map
            ((completedDerivedScalarExtension l E F ι S).map
              ((integralSheafTwist l E S m).mapDerivedCategoryFactors.hom.app P.obj)) ≫
          (completedDerivedScalarExtension l F G κ S).map
            (completedScalarCounit l E F ι S
              (((integralSheafTwist l E S m).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≫
          completedScalarCounit l F G κ S
            ((completedOrdinaryScalarComplex l E F ι S).obj
              (((integralSheafTwist l E S m).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≫
          DerivedCategory.Q.map a.hom ≫
          (integralSheafTwist l G S m).mapDerivedCategoryFactors.inv.app
            ((completedOrdinaryScalarComplex l E G (κ.comp ι) S).obj P.obj) ≫
          (integralSheafTwist l G S m).mapDerivedCategory.map
            (integralTwistCoherenceModelMap l E S G (κ.comp ι) P ≫
              (integralScalarExtensionOfUniverses l E G (κ.comp ι) S).map e.hom) =
        (completedDerivedScalarExtension l F G κ S).map
            ((completedScalarComparison l E F ι S).app
              ((integralSheafTwist l E S m).mapDerivedCategory.obj C.obj)) ≫
          (completedScalarComparison l F G κ S).app
            ((integralScalarExtensionOfUniverses l E F ι S).obj
              ((integralSheafTwist l E S m).mapDerivedCategory.obj C.obj)) ≫
          ((sfIntegralScalarComp l E F ι S
            (l + 1) (ne_of_lt (Nat.lt_succ_self l)) G κ).hom.app
              (integralTwistCoherenceObject l E S m C)).hom ≫
          (integralTwistCompletedBeta l E G (κ.comp ι) S m).hom.app C) ∧
    (∀ (P : (integralOperationsGoodComplex l E S).FullSubcategory)
      (hP : sfIntegralConstructible l E S (DerivedCategory.Q.obj P.obj)),
      (completedScalarComparison l E E (AlgHom.id (Padic l) E) S).app
          (DerivedCategory.Q.obj P.obj) ≫
        ((sfIntegralScalarUnit l E S (l + 1) (ne_of_lt (Nat.lt_succ_self l))).hom.app
          ⟨DerivedCategory.Q.obj P.obj, hP⟩).hom =
      completedScalarCounit l E E (AlgHom.id (Padic l) E) S P.obj ≫
        DerivedCategory.Q.map
          ((completedScalarIdentityMultiplication l E S).hom.app P.obj)) ∧
    (∀ C : sfIntegralConstructibleCategory l E S,
      (integralTwistCompletedBeta l E E (AlgHom.id (Padic l) E) S m).hom.app C ≫
          (integralSheafTwist l E S m).mapDerivedCategory.map
            ((sfIntegralScalarUnit l E S (l + 1) (ne_of_lt (Nat.lt_succ_self l))).hom.app C).hom =
        ((sfIntegralScalarUnit l E S (l + 1) (ne_of_lt (Nat.lt_succ_self l))).hom.app
          (integralTwistCoherenceObject l E S m C)).hom) ∧
    (∀ C : sfIntegralConstructibleCategory l E S,
      (sfIntegralScalarComp l E E (AlgHom.id (Padic l) E) S
          (l + 1) (ne_of_lt (Nat.lt_succ_self l)) F ι).hom.app C =
        (sfConstructibleIntegralScalarExtension
          (l + 1) l (ne_of_lt (Nat.lt_succ_self l)) E F ι S).map
          ((sfIntegralScalarUnit l E S (l + 1) (ne_of_lt (Nat.lt_succ_self l))).hom.app C)) ∧
    (∀ C : sfIntegralConstructibleCategory l E S,
      (sfIntegralScalarComp l E F ι S
          (l + 1) (ne_of_lt (Nat.lt_succ_self l)) F (AlgHom.id (Padic l) F)).hom.app C =
        (sfIntegralScalarUnit l F S (l + 1) (ne_of_lt (Nat.lt_succ_self l))).hom.app
          ((sfConstructibleIntegralScalarExtension (l + 1) l (ne_of_lt (Nat.lt_succ_self l))
            E F ι S).obj C)) ∧
    ∀ C : sfRationalConstructibleCategory l E S,
      HEq ((sfRationalScalarComp l E F ι S (l + 1) (ne_of_lt (Nat.lt_succ_self l)) G κ).hom.app C)
        ((sfRationalConstructibleLocalization l G S).map
          ((sfIntegralScalarComp l E F ι S
            (l + 1) (ne_of_lt (Nat.lt_succ_self l)) G κ).hom.app C.obj)) := by
  sorry

end WeilConjectures
