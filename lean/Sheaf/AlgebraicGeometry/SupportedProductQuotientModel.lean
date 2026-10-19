/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

import Sheaf.SixFunctors.IntrinsicDerivedTensor
import Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-!
# The quotient model of supported constant coefficients

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
`lem-pur-kunneth-supported.proof.md`, paragraph 4
(blueprint: lem-pur-supported-product-quotient-model).

The quotient is an actual cokernel. The comparison with closed pushforward is
normalized by its quotient map. The unbounded tensor comparison is the localization
of the signed total-complex comparison.

## Main definitions and statement

* `Etale.supportQuotient` and `ProEtale.supportQuotient`: the cokernel objects.
* `supportQuotientOrdinaryIso`: the uniquely generator-normalized comparison.
* `supportQuotientComparison`: its canonical unbounded derived extension.
* `SupportQuotientModel`: adjunction, generator and counit normalizations.
* `supported_product_quotient_model`: both topologies for the three closed pairs.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- Cache the existing constant-coefficient sheafification interface at this site.
Source: blueprint small-site convention
(blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable instance supportQuotientWeakSheafify
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (GrothendieckTopology.hasSheafify_smallEtaleTopology (ModuleCat.{u + 1} A) X).isRightAdjoint

variable (A : Type (u + 1)) [CommRing A]
  {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The inclusion of the constant module on the open complement into the constant
module on the ambient site, adjoint to the constant inverse-image identification.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientOpenArrow :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) i.openComplement.ι).obj
      ((constantSheaf i.openComplement.toScheme.smallEtaleTopology
        (ModuleCat.{u + 1} A)).obj (𝟙_ (ModuleCat.{u + 1} A))) ⟶
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (𝟙_ (ModuleCat.{u + 1} A)) :=
  ((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) i.openComplement.ι).homEquiv _ _).symm
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A)
        i.openComplement.ι).inv.app (𝟙_ (ModuleCat.{u + 1} A)))

/-- The rank-one support quotient, with real cokernel data.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotient :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) := cokernel (supportQuotientOpenArrow A i)

/-- The ordinary tensor functor Q tensor constant coefficients.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientCoefficients :
    ModuleCat.{u + 1} A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    (supportedSheafTensor A X).obj (supportQuotient A i)

/-- Its quotient-generator map, using the unit and the canonical constant tensor map.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientGenerator (M : ModuleCat.{u + 1} A) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ⟶
      (supportQuotientCoefficients A i).obj M :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).map (λ_ M).inv ≫
    supportedConstantTensor A X (𝟙_ (ModuleCat.{u + 1} A)) M ≫
      ((supportedSheafTensor A X).map (cokernel.π (supportQuotientOpenArrow A i))).app
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)


/-- The ordinary comparison is uniquely determined by the quotient generators.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model).
Proof: the open-closed exact sequence identifies the rank-one cokernel with
closed pushforward of A, under the specified quotient. Both tensor with Q and
closed pushforward of constant coefficients preserve coproducts and cokernels.
Extend the rank-one comparison to free modules; it commutes with every matrix
column because each column is a finite linear combination. The functorial
presentation on symbols [m], with additive and scalar relations, then gives the
comparison for every module. Tensor is right exact, so the generator map is epic;
this proves uniqueness. No flatness of the coefficient module is assumed. -/
theorem supportQuotientOrdinary_existsUnique :
    ∃! b : supportQuotientCoefficients A i ≅ supportedCoefficients A i,
      ∀ M : ModuleCat.{u + 1} A,
        supportQuotientGenerator A i M ≫ b.hom.app M = supportedCoefficientQuotient A i M := by
  sorry

/-- The uniquely quotient-normalized ordinary comparison.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientOrdinaryIso :
    supportQuotientCoefficients A i ≅ supportedCoefficients A i :=
  (supportQuotientOrdinary_existsUnique A i).choose

/-- Additivity uses the existing constant-sheaf and tensor functors.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable instance supportQuotientCoefficients_additive :
    (supportQuotientCoefficients A i).Additive :=
  inferInstanceAs ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    (supportedSheafTensor A X).obj (supportQuotient A i)).Additive)

/-- Exactness transported along the uniquely normalized ordinary comparison.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable instance supportQuotientCoefficients_preservesFiniteLimits :
    PreservesFiniteLimits (supportQuotientCoefficients A i) :=
  preservesFiniteLimits_of_natIso (supportQuotientOrdinaryIso A i).symm

/-- Exactness transported along the uniquely normalized ordinary comparison.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable instance supportQuotientCoefficients_preservesFiniteColimits :
    PreservesFiniteColimits (supportQuotientCoefficients A i) :=
  preservesFiniteColimits_of_natIso (supportQuotientOrdinaryIso A i).symm

/-- The unbounded functor E(V) = Q[0] tensor-derived constant V.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientDerived :
    DerivedCategory (ModuleCat.{u + 1} A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory ⋙
    (derivedTensor (ModuleCat.{u + 1} A) X).obj
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (supportQuotient A i)))

/-- The canonical comparison on an arbitrary complex: constant localization,
lax-monoidal localization of the signed tensor, and collapse of the degree-zero
first factor. Source: blueprint paragraph 4
(blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientLocalizationComponent
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    (supportQuotientDerived A i).obj (DerivedCategory.Q.obj P) ⟶
      (supportQuotientCoefficients A i).mapDerivedCategory.obj (DerivedCategory.Q.obj P) :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (supportQuotient A i)))).map
      ((constantSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)).mapDerivedCategoryFactors.hom.app P) ≫
    supportedDerivedTensorLocalizationGeneric (ModuleCat.{u + 1} A) X
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (supportQuotient A i))
      (((constantSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Q.map
      (CochainComplex.mapBifunctorSingle₁Iso (supportedSheafTensor A X)
        (supportQuotient A i)
        (((constantSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)).obj P)).hom ≫
    (supportQuotientCoefficients A i).mapDerivedCategoryFactors.inv.app P

/-- Naturality of the explicit localization components.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model).
Proof: naturality of the constant localization isomorphism, of the lax-monoidal
localization map, and of the single-factor total-complex collapse gives the three
successive commuting squares. Compose them and the inverse exact-localization
square. The tensor differential has the usual sign; the first factor is in degree
zero, so the collapse introduces no sign or exchange of factors. -/
theorem supportQuotientLocalization_naturality
    {P P' : CochainComplex (ModuleCat.{u + 1} A) ℤ} (f : P ⟶ P') :
    (supportQuotientDerived A i).map (DerivedCategory.Q.map f) ≫
        supportQuotientLocalizationComponent A i P' =
      supportQuotientLocalizationComponent A i P ≫
        (supportQuotientCoefficients A i).mapDerivedCategory.map (DerivedCategory.Q.map f) := by
  sorry

/-- The canonical comparison on complexes, before descent through localization.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientLocalizationComplex :
    DerivedCategory.Q ⋙ supportQuotientDerived A i ⟶
      DerivedCategory.Q ⋙ (supportQuotientCoefficients A i).mapDerivedCategory where
  app := supportQuotientLocalizationComponent A i
  naturality _ _ f := supportQuotientLocalization_naturality A i f

/-- Descend the specified complex comparison; localization gives a unique map.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientLocalization :
    supportQuotientDerived A i ⟶ (supportQuotientCoefficients A i).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} A) (.up ℤ))
    _ _ _ _ (supportQuotientLocalizationComplex A i)

/-- The tensor localization comparison is invertible without boundedness assumptions.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model).
Proof: choose a flat-term K-flat module resolution P of V. Constant inverse image
is exact and preserves K-flatness and flat terms. The lax tensor localization map
is thus invertible using its second factor. The single-factor collapse and both
exact-localization comparisons are invertible. Every derived object has such a
representative and naturality transports invertibility along its quasi-isomorphism.
This also proves independence of the chosen resolution. -/
theorem supportQuotientLocalization_isIso : IsIso (supportQuotientLocalization A i) := by
  sorry

/-- The natural comparison, explicitly derived from the ordinary quotient comparison.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientComparison :
    supportQuotientDerived A i ≅ (supportedCoefficients A i).mapDerivedCategory :=
  @asIso _ _ _ _ (supportQuotientLocalization A i)
    (supportQuotientLocalization_isIso A i) ≪≫
      Functor.mapDerivedCategoryNatIso (supportQuotientOrdinaryIso A i)

/-- The quotient-support adjunction, with identity on the existing right adjoint.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientDerivedAdjunction :
    supportQuotientDerived A i ⊣ supportedSectionsDerived A i :=
  (((supportedCoefficientAdjunction A i).ofNatIsoLeft
    (supportQuotientOrdinaryIso A i).symm).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoLeft
      (@asIso _ _ _ _ (supportQuotientLocalization A i)
        (supportQuotientLocalization_isIso A i)).symm

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- Cache the existing constant-coefficient sheafification interface at this site.
Source: blueprint small-site convention
(blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable instance supportQuotientWeakSheafify
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) :=
  (GrothendieckTopology.hasSheafify_proEtTopology (ModuleCat.{u + 1} A) X).isRightAdjoint

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The inclusion of the constant module on the open complement into the constant
module on the ambient site, adjoint to the constant inverse-image identification.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientOpenArrow :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) i.openComplement.ι).obj
      ((constantSheaf (Scheme.ProEt.topology i.openComplement.toScheme)
        (ModuleCat.{u + 1} A)).obj (𝟙_ (ModuleCat.{u + 1} A))) ⟶
    (constantSheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A)).obj (𝟙_ (ModuleCat.{u + 1} A)) :=
  ((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) i.openComplement.ι).homEquiv _ _).symm
      ((constantSheafCompUpperStarIso (ModuleCat.{u + 1} A)
        i.openComplement.ι).inv.app (𝟙_ (ModuleCat.{u + 1} A)))

/-- The rank-one support quotient, with real cokernel data.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotient :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) := cokernel (supportQuotientOpenArrow A i)

/-- The ordinary tensor functor Q tensor constant coefficients.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientCoefficients :
    ModuleCat.{u + 1} A ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) :=
  constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⋙
    (supportedSheafTensor A X).obj (supportQuotient A i)

/-- Its quotient-generator map, using the unit and the canonical constant tensor map.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientGenerator (M : ModuleCat.{u + 1} A) :
    (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj M ⟶
      (supportQuotientCoefficients A i).obj M :=
  (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map (λ_ M).inv ≫
    supportedConstantTensor A X (𝟙_ (ModuleCat.{u + 1} A)) M ≫
      ((supportedSheafTensor A X).map (cokernel.π (supportQuotientOpenArrow A i))).app
        ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).obj M)

variable [IsLocallyNoetherian X]

/-- The ordinary comparison is uniquely determined by the quotient generators.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model).
Proof: the open-closed exact sequence identifies the rank-one cokernel with
closed pushforward of A, under the specified quotient. Both tensor with Q and
closed pushforward of constant coefficients preserve coproducts and cokernels.
Extend the rank-one comparison to free modules; it commutes with every matrix
column because each column is a finite linear combination. The functorial
presentation on symbols [m], with additive and scalar relations, then gives the
comparison for every module. Tensor is right exact, so the generator map is epic;
this proves uniqueness. No flatness of the coefficient module is assumed. -/
theorem supportQuotientOrdinary_existsUnique :
    ∃! b : supportQuotientCoefficients A i ≅ supportedCoefficients A i,
      ∀ M : ModuleCat.{u + 1} A,
        supportQuotientGenerator A i M ≫ b.hom.app M = supportedCoefficientQuotient A i M := by
  sorry

/-- The uniquely quotient-normalized ordinary comparison.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientOrdinaryIso :
    supportQuotientCoefficients A i ≅ supportedCoefficients A i :=
  (supportQuotientOrdinary_existsUnique A i).choose

/-- Additivity uses the existing constant-sheaf and tensor functors.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable instance supportQuotientCoefficients_additive :
    (supportQuotientCoefficients A i).Additive :=
  inferInstanceAs ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⋙
    (supportedSheafTensor A X).obj (supportQuotient A i)).Additive)

/-- Exactness transported along the uniquely normalized ordinary comparison.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable instance supportQuotientCoefficients_preservesFiniteLimits :
    PreservesFiniteLimits (supportQuotientCoefficients A i) :=
  preservesFiniteLimits_of_natIso (supportQuotientOrdinaryIso A i).symm

/-- Exactness transported along the uniquely normalized ordinary comparison.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable instance supportQuotientCoefficients_preservesFiniteColimits :
    PreservesFiniteColimits (supportQuotientCoefficients A i) :=
  preservesFiniteColimits_of_natIso (supportQuotientOrdinaryIso A i).symm

/-- The unbounded functor E(V) = Q[0] tensor-derived constant V.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientDerived :
    DerivedCategory (ModuleCat.{u + 1} A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).mapDerivedCategory ⋙
    (derivedTensor (ModuleCat.{u + 1} A) X).obj
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (supportQuotient A i)))

/-- The canonical comparison on an arbitrary complex: constant localization,
lax-monoidal localization of the signed tensor, and collapse of the degree-zero
first factor. Source: blueprint paragraph 4
(blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientLocalizationComponent
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    (supportQuotientDerived A i).obj (DerivedCategory.Q.obj P) ⟶
      (supportQuotientCoefficients A i).mapDerivedCategory.obj (DerivedCategory.Q.obj P) :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj (supportQuotient A i)))).map
      ((constantSheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A)).mapDerivedCategoryFactors.hom.app P) ≫
    supportedDerivedTensorLocalizationGeneric (ModuleCat.{u + 1} A) X
      ((HomologicalComplex.single _ (.up ℤ) 0).obj (supportQuotient A i))
      (((constantSheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)).obj P) ≫
    DerivedCategory.Q.map
      (CochainComplex.mapBifunctorSingle₁Iso (supportedSheafTensor A X)
        (supportQuotient A i)
        (((constantSheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A)).mapHomologicalComplex (.up ℤ)).obj P)).hom ≫
    (supportQuotientCoefficients A i).mapDerivedCategoryFactors.inv.app P

/-- Naturality of the explicit localization components.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model).
Proof: naturality of the constant localization isomorphism, of the lax-monoidal
localization map, and of the single-factor total-complex collapse gives the three
successive commuting squares. Compose them and the inverse exact-localization
square. The tensor differential has the usual sign; the first factor is in degree
zero, so the collapse introduces no sign or exchange of factors. -/
theorem supportQuotientLocalization_naturality
    {P P' : CochainComplex (ModuleCat.{u + 1} A) ℤ} (f : P ⟶ P') :
    (supportQuotientDerived A i).map (DerivedCategory.Q.map f) ≫
        supportQuotientLocalizationComponent A i P' =
      supportQuotientLocalizationComponent A i P ≫
        (supportQuotientCoefficients A i).mapDerivedCategory.map (DerivedCategory.Q.map f) := by
  sorry

/-- The canonical comparison on complexes, before descent through localization.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientLocalizationComplex :
    DerivedCategory.Q ⋙ supportQuotientDerived A i ⟶
      DerivedCategory.Q ⋙ (supportQuotientCoefficients A i).mapDerivedCategory where
  app := supportQuotientLocalizationComponent A i
  naturality _ _ f := supportQuotientLocalization_naturality A i f

/-- Descend the specified complex comparison; localization gives a unique map.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientLocalization :
    supportQuotientDerived A i ⟶ (supportQuotientCoefficients A i).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} A) (.up ℤ))
    _ _ _ _ (supportQuotientLocalizationComplex A i)

/-- The tensor localization comparison is invertible without boundedness assumptions.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model).
Proof: choose a flat-term K-flat module resolution P of V. Constant inverse image
is exact and preserves K-flatness and flat terms. The lax tensor localization map
is thus invertible using its second factor. The single-factor collapse and both
exact-localization comparisons are invertible. Every derived object has such a
representative and naturality transports invertibility along its quasi-isomorphism.
This also proves independence of the chosen resolution. -/
theorem supportQuotientLocalization_isIso : IsIso (supportQuotientLocalization A i) := by
  sorry

/-- The natural comparison, explicitly derived from the ordinary quotient comparison.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientComparison :
    supportQuotientDerived A i ≅ (supportedCoefficients A i).mapDerivedCategory :=
  @asIso _ _ _ _ (supportQuotientLocalization A i)
    (supportQuotientLocalization_isIso A i) ≪≫
      Functor.mapDerivedCategoryNatIso (supportQuotientOrdinaryIso A i)

/-- The quotient-support adjunction, with identity on the existing right adjoint.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
noncomputable def supportQuotientDerivedAdjunction :
    supportQuotientDerived A i ⊣ supportedSectionsDerived A i :=
  (((supportedCoefficientAdjunction A i).ofNatIsoLeft
    (supportQuotientOrdinaryIso A i).symm).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoLeft
      (@asIso _ _ _ _ (supportQuotientLocalization A i)
        (supportQuotientLocalization_isIso A i)).symm

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale

/-- All normalizations of the quotient model for a single closed pair. The
ordinary equality identifies the generator adjunction, the Hom equivalence fixes
identity on the common right adjoint, and the complex formula fixes the derived
extension, including its values on unbounded complexes.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
def SupportQuotientModel (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] : Prop :=
  (∀ M : ModuleCat.{u + 1} A,
    supportQuotientGenerator A i M ≫ (supportQuotientOrdinaryIso A i).hom.app M =
      supportedCoefficientQuotient A i M) ∧
  (∀ (M : ModuleCat.{u + 1} A)
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (f : M ⟶ (supportedEtaleSections A X i.openComplement).obj F),
    supportQuotientGenerator A i M ≫
      (((supportedCoefficientAdjunction A i).ofNatIsoLeft
        (supportQuotientOrdinaryIso A i).symm).homEquiv M F).symm f =
    ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv M F).symm
      (f ≫ (supportedEtaleSectionsι A X i.openComplement).app F)) ∧
  (∀ b : supportQuotientDerived A i ≅ (supportedCoefficients A i).mapDerivedCategory,
    (∀ (V : DerivedCategory (ModuleCat.{u + 1} A))
        (F : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
        (f : (supportedCoefficients A i).mapDerivedCategory.obj V ⟶ F),
      (supportQuotientDerivedAdjunction A i).homEquiv V F (b.hom.app V ≫ f) =
        (supportedCoefficientDerivedAdjunction A i).homEquiv V F f) ↔
      b = supportQuotientComparison A i) ∧
  (∀ P : CochainComplex (ModuleCat.{u + 1} A) ℤ,
    (supportQuotientComparison A i).hom.app (DerivedCategory.Q.obj P) ≫
      (supportedCoefficients A i).mapDerivedCategoryFactors.hom.app P =
    supportQuotientLocalizationComponent A i P ≫
      (supportQuotientCoefficients A i).mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (supportQuotientOrdinaryIso A i) (.up ℤ)).hom.app
          P)) ∧
  (∀ F : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
    (supportQuotientComparison A i).hom.app ((supportedSectionsDerived A i).obj F) ≫
      (supportedCoefficientDerivedAdjunction A i).counit.app F =
    (supportQuotientDerivedAdjunction A i).counit.app F)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- All normalizations of the quotient model for a single closed pair. The
ordinary equality identifies the generator adjunction, the Hom equivalence fixes
identity on the common right adjoint, and the complex formula fixes the derived
extension, including its values on unbounded complexes.
Source: blueprint paragraph 4 (blueprint: lem-pur-supported-product-quotient-model). -/
def SupportQuotientModel (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [Finite A] [IsLocallyNoetherian X] : Prop :=
  (∀ M : ModuleCat.{u + 1} A,
    supportQuotientGenerator A i M ≫ (supportQuotientOrdinaryIso A i).hom.app M =
      supportedCoefficientQuotient A i M) ∧
  (∀ (M : ModuleCat.{u + 1} A)
      (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
      (f : M ⟶ (supportSections i A).obj F),
    supportQuotientGenerator A i M ≫
      (((supportedCoefficientAdjunction A i).ofNatIsoLeft
        (supportQuotientOrdinaryIso A i).symm).homEquiv M F).symm f =
    ((constantSheafΓAdj (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).homEquiv M F).symm
      (f ≫ (supportedModuleSectionsι A i).app F)) ∧
  (∀ b : supportQuotientDerived A i ≅ (supportedCoefficients A i).mapDerivedCategory,
    (∀ (V : DerivedCategory (ModuleCat.{u + 1} A))
        (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
        (f : (supportedCoefficients A i).mapDerivedCategory.obj V ⟶ F),
      (supportQuotientDerivedAdjunction A i).homEquiv V F (b.hom.app V ≫ f) =
        (supportedCoefficientDerivedAdjunction A i).homEquiv V F f) ↔
      b = supportQuotientComparison A i) ∧
  (∀ P : CochainComplex (ModuleCat.{u + 1} A) ℤ,
    (supportQuotientComparison A i).hom.app (DerivedCategory.Q.obj P) ≫
      (supportedCoefficients A i).mapDerivedCategoryFactors.hom.app P =
    supportQuotientLocalizationComponent A i P ≫
      (supportQuotientCoefficients A i).mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (supportQuotientOrdinaryIso A i) (.up ℤ)).hom.app
          P)) ∧
  (∀ F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)),
    (supportQuotientComparison A i).hom.app ((supportedSectionsDerived A i).obj F) ≫
      (supportedCoefficientDerivedAdjunction A i).counit.app F =
    (supportQuotientDerivedAdjunction A i).counit.app F)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

/-- The quotient support model for both topologies and all three closed pairs.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
`lem-pur-kunneth-supported.proof.md`, paragraph 4
(blueprint: lem-pur-supported-product-quotient-model).

Proof: (1) finite type over the field makes X, Y and their fibre product
Noetherian; separatedness makes the ambient schemes quasi-separated and the
complementary open immersions are quasi-compact. (2) The open-closed exact
sequences in both topologies identify the rank-one cokernel and normalized
closed pushforward. (3) Both coefficient functors preserve coproducts and
cokernels. Extend the comparison to free modules and check finite linear
combinations of generators. (4) Use the functorial free presentation of any
module to obtain the unique generator-preserving ordinary comparison; no
coefficient flatness is needed. (5) Use a flat-term K-flat module resolution;
constant inverse image preserves it, so the explicitly defined localization
comparison is invertible. Degreewise naturality derives the ordinary comparison
on every complex and on roofs. (6) The generator equality identifies both
ordinary Hom bijections with the kernel of restriction. Apply this equality to
K-injective representatives and the exact-left-adjoint derived adjunction to
identify the derived Hom bijections. Their counits are the inverse images of
the identity, giving the stated counit equality. (7) An adjunction-preserving
comparison has each component determined by the injective Hom bijection;
therefore it is the displayed comparison. This proves uniqueness with identity
on the common right adjoint, rather than uniqueness merely in degree zero.
The same argument applies to i, j and their product immersion.

DAG proof dependencies by step: (1) `lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-noetherian-open-subscheme-noetherian`, `def-weil-finite-type-morphism`
and `def-weil-proper-morphism`; (2) `lem-weil-pbc-open-closed-short-exact`,
`det-sf-open-closed-sequence-ring-sheaf`, `def-pur-supported-exterior-product`
and `def-pur-proetale-supported-exterior-product`; (3)-(4)
`def-weil-pbc-constant-sheaf`, `lem-pc-sheaf-modules-tensor-closed` and
`lem-weil-pbc-left-adjoint-preserves-colimits`; (5) `lem-pc-kflat-resolution`,
`lem-weil-pbc-ringed-pullback-preserves-kflat`,
`lem-weil-pbc-site-module-presheaf-sheafification-exact`,
`lem-weil-pbc-exact-functor-derived-factorization`, `def-kun-derived-tensor`
and `def-weil-derived-tensor`; (6) `prop-pur-kinjective-resolutions-exist`,
`lem-weil-pbc-termwise-adjunction-homotopy`,
`lem-weil-pbc-right-adjoint-preserves-kinjective`,
`lem-weil-pbc-kinjective-hom-derived` and
`lem-weil-pbc-adjunction-of-natural-bijection`. Step (7) uses injectivity of the
specified adjunction bijection. -/
theorem supported_product_quotient_model
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Z W : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j] :
    (Etale.SupportQuotientModel A i ∧ @ProEtale.SupportQuotientModel A _ _ _ i _ _
      (LocallyOfFiniteType.isLocallyNoetherian f)) ∧
    (Etale.SupportQuotientModel A j ∧ @ProEtale.SupportQuotientModel A _ _ _ j _ _
      (LocallyOfFiniteType.isLocallyNoetherian g)) ∧
    (Etale.SupportQuotientModel A (Etale.supportedProductImmersion f g i j) ∧
      @ProEtale.SupportQuotientModel A _ _ _ (Etale.supportedProductImmersion f g i j) _ _
        (LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g ≫ f))) := by
  sorry

end AlgebraicGeometry
