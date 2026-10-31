/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClassDefsSupplement
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedCoefficientReduction
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierSourceComparison
import WeilConjectures.AlgebraicGeometry.Cartier.CartierConstantComparisonNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit

/-!
# Supported generators under the Cartier source comparison

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-lem-geo-cartier/
sk-lem-geo-cartier.proof.md, opening comparison paragraph
(blueprint: lem-sfb-cartier-source-comparison-generator).

The general unit equation and its finite-coefficient generator consequence use the
specified comparison maps. They assert neither a Kummer class nor a scalar-unit property.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

private theorem constantDirect_section (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) (U : Z.ProEtᵒᵖ) (a : A) :
    (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
        (ModuleCat.of A A)).hom.app U
        ((toSheafify (Scheme.ProEt.topology Z)
          ((Functor.const Z.ProEtᵒᵖ).obj (ModuleCat.of A A))).app U a) =
      (toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
          ((Scheme.proEtaleBaseChange i).op.obj U) a := by
  have h := ((sheafificationAdjunction (Scheme.ProEt.topology Z)
    (ModuleCat.{u + 1} A)).homEquiv
      ((Functor.const Z.ProEtᵒᵖ).obj (ModuleCat.of A A))
      ((Scheme.proEtaleSheafDirectImage i (ModuleCat.{u + 1} A)).obj
        ((constantSheaf (Scheme.ProEt.topology D) (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)))).apply_symm_apply
    (Functor.whiskerLeft (Scheme.proEtaleBaseChange i).op
      (toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of A A))))
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k ↦ k.app U a) h

private theorem comparisonConstant_section (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (U : T.Etaleᵒᵖ) (a : A) :
    (((sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv
      ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))
      ((comparisonLowerStar (ModuleCat.{u + 1} A) T).obj
        ((constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)))).symm
      (Functor.whiskerLeft (Scheme.toProEt T).op
        (toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of A A))))).hom.app U
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app U a) =
      (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of A A))).app
          ((Scheme.toProEt T).op.obj U) a := by
  have h := ((sheafificationAdjunction T.smallEtaleTopology
    (ModuleCat.{u + 1} A)).homEquiv
      ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))
      ((comparisonLowerStar (ModuleCat.{u + 1} A) T).obj
        ((constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)))).apply_symm_apply
    (Functor.whiskerLeft (Scheme.toProEt T).op
      (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of A A))))
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k ↦ k.app U a) h

/-- The specified source comparison transports the ordinary supported constant unit.
Source: blueprint sk-lem-geo-cartier.proof.md, opening comparison paragraph
(blueprint: lem-sfb-cartier-source-comparison-generator).

Proof: transpose the equation through the comparison adjunction at Z. The source
comparison is its defining mate followed by the constant comparison at D, identified
by part (1) of lem-sfb-cartier-constant-comparison-normalization. The mate-transpose
identity reduces the equation to the ordinary supported unit and the transposed
constant comparisons. Transpose once more through sheafification and evaluate on
constant presheaf sections. The source library's formula for the ordinary constant
unit, and the inverse laws of the sheafification Hom equivalence for both comparison
maps and the pro-etale direct-image map, send each coefficient to the same section.
The direct-image commutation isomorphism acts identically on section modules.
Injectivity of both Hom equivalences gives the equation. This uses no Cartier or
finite-coefficient hypothesis and does not need the inverse-image normalization square.
-/
theorem cartierSourceComparison_supportedConstantUnit
    (A : Type (u + 1)) [CommRing A] {D Z : Scheme.{u}}
    (i : D ⟶ Z) [IsClosedImmersion i] :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).map
        (Etale.supportedConstantUnit A i) ≫ geoCartierSourceComparison A i =
      Etale.cartierConstantComparison A Z ≫
        Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
          (ModuleCat.of A A) := by
  unfold geoCartierSourceComparison geoCartierConstant
  rw [← ((Etale.cartierConstantComparison_normalization A).1 D).1]
  apply ((comparisonAdjunction (ModuleCat.{u + 1} A) Z).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  unfold lowerStarComparisonUpperStarBaseChange
  rw [adjunctionMate_transpose]
  rw [Etale.cartierConstantComparison, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_naturality_right]
  rw [Etale.cartierConstantComparison, Equiv.apply_symm_apply]
  have hu : Etale.supportedConstantUnit A i =
      Etale.constantSheafUnit i (ModuleCat.of A A) := by
    unfold Etale.supportedConstantUnit Etale.constantSheafUnit
    rw [Adjunction.homEquiv_unit]
    rfl
  have hd (S : Sheaf (Scheme.ProEt.topology D) (ModuleCat.{u + 1} A))
      (W : Z.Etaleᵒᵖ) :
      (((lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} A)).inv.app S).hom.app W) =
        𝟙 _ := by
    dsimp only [lowerStarCompComparisonLowerStarIso]
    change ((𝟙 _ ≫ S.obj.map (𝟙 _)) ≫ 𝟙 _) = 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact S.obj.map_id _
  apply ((sheafificationAdjunction Z.smallEtaleTopology
    (ModuleCat.{u + 1} A)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let c (T : Scheme.{u}) :=
    (((sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv
      ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))
      ((comparisonLowerStar (ModuleCat.{u + 1} A) T).obj
        ((constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)))).symm
      (Functor.whiskerLeft (Scheme.toProEt T).op
        (toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of A A)))))
  change (((lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} A)).inv.app
      ((constantSheaf (Scheme.ProEt.topology D) (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A A))).hom.app W)
      ((c D).hom.app ((MorphismProperty.Over.pullback @Etale ⊤ i).op.obj W)
        ((Etale.supportedConstantUnit A i).hom.app W
          ((toSheafify Z.smallEtaleTopology
            ((Functor.const Z.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a))) =
    (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
      (ModuleCat.of A A)).hom.app ((Scheme.toProEt Z).op.obj W)
      ((c Z).hom.app W ((toSheafify Z.smallEtaleTopology
        ((Functor.const Z.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a))
  rw [hd]
  change (c D).hom.app ((MorphismProperty.Over.pullback @Etale ⊤ i).op.obj W)
      ((Etale.supportedConstantUnit A i).hom.app W
        ((toSheafify Z.smallEtaleTopology
          ((Functor.const Z.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a)) =
    (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
      (ModuleCat.of A A)).hom.app ((Scheme.toProEt Z).op.obj W)
      ((c Z).hom.app W ((toSheafify Z.smallEtaleTopology
        ((Functor.const Z.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a))
  rw [hu, Etale.constantSheafUnit_app_toSheafify]
  dsimp only [c]
  erw [comparisonConstant_section, comparisonConstant_section, constantDirect_section]
  rfl

end AlgebraicGeometry.ProEtale
