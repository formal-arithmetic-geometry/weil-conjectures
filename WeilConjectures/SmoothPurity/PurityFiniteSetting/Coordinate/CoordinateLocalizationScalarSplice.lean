/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSplice
public import WeilConjectures.AlgebraicGeometry.PrincipalTorsorComparisons.PrincipalTorsorSignTypes
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.AlgebraicGeometry.ConstantModuleTransitionCoefficients
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.KummerLocalizationSplice
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SmoothPurity.EtaleFiniteTwistPullbackRest
public import WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback

/-! # Scalar forgetting of the coordinate localization splice

Source: the finite-coefficient and rank-one paragraphs of the current blueprint,
cor-pur-affine-space-zero-section-purity.proof.md; Stacks Tags 03PL and 0A45
(blueprint: lem-pur-coordinate-localization-scalar-splice).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

private theorem rootCoefficientMap_eq_ordinary (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) :
    P.rootCoefficientMap h T =
      ordinaryFiniteRootMap P.Coefficient P.exponent (P.exponent_coefficient_eq_zero h) T := by
  exact ((Classical.choose_spec (P.existsUnique_rootCoefficientMap h T)).2 _
    (fun _ _ ↦ rfl)).symm

-- Under the constant-sheaf adjunction both coefficient generators send one to one.

private theorem integerToConstant_eq_ordinary (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    P.integerToConstant T = ordinaryFiniteIntegralGenerator P.Coefficient T := by
  apply ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).homEquiv _ _).injective
  unfold ordinaryFiniteIntegralGenerator
  erw [Equiv.apply_symm_apply]
  unfold integerToConstant
  rw [Adjunction.homEquiv_naturality_left]
  rw [constantSheafAdj_homEquiv_apply]
  have hc := coefficient_generators P.Coefficient
    (ModuleCat.of P.Coefficient P.Coefficient) T
    (op (Scheme.Etale.mk (𝟙 T)))
  erw [← hc]
  simp only [Category.assoc]
  have hi := congrArg (fun k ↦ k.hom.app (op (Scheme.Etale.mk (𝟙 T))))
    ((constantCommuteCompose T.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1})).hom_inv_id_app
        (ModuleCat.of P.Coefficient P.Coefficient))
  change ((constantCommuteCompose T.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1})).hom.app
        (ModuleCat.of P.Coefficient P.Coefficient)).hom.app
          (op (Scheme.Etale.mk (𝟙 T))) ≫
      ((constantCommuteCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1})).inv.app
          (ModuleCat.of P.Coefficient P.Coefficient)).hom.app
            (op (Scheme.Etale.mk (𝟙 T))) = 𝟙 _ at hi
  erw [hi, Category.comp_id]
  ext n
  change ((forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).map
      ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of P.Coefficient P.Coefficient))).app
          (op (Scheme.Etale.mk (𝟙 T))))).hom (n.down • (1 : P.Coefficient)) =
    ((forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).map
      ((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of P.Coefficient P.Coefficient))).app
          (op (Scheme.Etale.mk (𝟙 T))))).hom (n.down : P.Coefficient)
  simp

-- The scalar comparison is injective and both representatives realize the same boundary.

private theorem kummerEtale_eq_finite (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level)
    (T : Scheme.{u}) (hr : IsUnit (P.exponent : Γ(T, ⊤)))
    (s : Γ(T, ⊤)ˣ) :
    P.kummerEtale h T hr s = finiteKummerUnitClass P.Coefficient P.exponent
      (P.exponent_coefficient_eq_zero h) T hr s := by
  apply (P.moduleClassToAbelian_bijective T (P.twistEtale h T)).injective
  have hc := ordinaryFiniteClass_extHomEquiv P.Coefficient T
    (Scheme.finiteEtaleTateLine T P.exponent P.Coefficient
      (P.exponent_coefficient_eq_zero h)) 1
    (finiteKummerUnitClass P.Coefficient P.exponent
      (P.exponent_coefficient_eq_zero h) T hr s)
  rw [finiteKummerUnitClass, Equiv.apply_symm_apply] at hc
  rw [← ordinaryFiniteClassEquiv_apply, Equiv.apply_symm_apply] at hc
  have hk : P.moduleClassToAbelian T (P.twistEtale h T) (P.kummerEtale h T hr s) =
      Sheaf.H.map (P.rootCoefficientMap h T) 1
        (T.kummerδ₀ P.exponent hr (Additive.ofMul s)) :=
    (Equiv.ofBijective _ (P.moduleClassToAbelian_bijective T
      (P.twistEtale h T))).apply_symm_apply _
  rw [hk]
  simpa only [moduleClassToAbelian, integerToConstant_eq_ordinary,
    rootCoefficientMap_eq_ordinary, ordinaryFiniteExtClassCore,
    finiteKummerUnitClass, forgetEtale, twistEtale, Scheme.finiteEtaleTateSheaf,
    Scheme.finiteEtaleTateTwist] using hc

-- The normalized roots square uniquely determines the coefficient-line pullback.

private theorem twistEtalePullback_eq_line (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level)
    (t : OrdinaryFiniteTwistTransport P.Coefficient P.exponent
      (P.exponent_coefficient_eq_zero h))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (P.exponent : Γ(Y, ⊤))) :
    P.twistEtalePullback h f = (t.line f hY).hom := by
  have hr : P.rootPullback f = (t.roots f hY).hom := by
    exact ((Classical.choose_spec (P.existsUnique_rootPullback f)).2 _
      (t.roots_normalization f hY).symm).symm
  apply Eq.symm
  apply (Classical.choose_spec (P.existsUnique_twistEtalePullback h f)).2
  rw [hr, rootCoefficientMap_eq_ordinary, rootCoefficientMap_eq_ordinary]
  exact rootMap_pullback P.Coefficient P.exponent (P.exponent_coefficient_eq_zero h) t f hY


-- The open localization classes agree after the unit and twist identifications.

private theorem coordinateOpenClass_eq_finite (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level)
    (t : OrdinaryFiniteTwistTransport P.Coefficient P.exponent
      (P.exponent_coefficient_eq_zero h))
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) :
    P.coordinateLocalizationOpenClass h T aT =
      finiteKummerOpenClass P.Coefficient P.exponent (P.exponent_coefficient_eq_zero h)
        t (Line T) ((Line T).basicOpen (coordinate T))
        (P.exponent_isUnit (Line T) (lineProjection T ≫ aT)) (coordinateUnit T) := by
  unfold coordinateLocalizationOpenClass finiteKummerOpenClass
  rw [kummerEtale_eq_finite]
  have ht := twistEtalePullback_eq_line P h t (openImmersion T)
    (P.exponent_isUnit (Line T) (lineProjection T ≫ aT))
  simp only [openImmersion] at ht
  simp only [openImmersion, Punctured, ht, IsIso.Iso.inv_hom, twistEtale,
    Scheme.finiteEtaleTateSheaf, Scheme.finiteEtaleTateTwist]

-- Associate the open Kummer class with the coefficient localization extension.

private theorem coordinateClass_eq_finite (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level)
    (t : OrdinaryFiniteTwistTransport P.Coefficient P.exponent
      (P.exponent_coefficient_eq_zero h))
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) :
    P.coordinateLocalizationClass h T aT =
      finiteKummerLocalizationBoundary P.Coefficient P.exponent
        (P.exponent_coefficient_eq_zero h) t (zeroSection T)
        ((Line T).basicOpen (coordinate T)) (coordinateLocalization_complement T)
        (P.exponent_isUnit (Line T) (lineProjection T ≫ aT)) (coordinateUnit T) := by
  unfold coordinateLocalizationClass finiteKummerLocalizationBoundary
  rw [coordinateOpenClass_eq_finite P h t]
  exact Ext.comp_assoc _ _ _ (zero_add 1) rfl (zero_add 2)

-- Only the roots-normalized degree-one part of finite twist transport is needed.

private theorem exists_coordinateTwistTransport (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) :
    Nonempty (OrdinaryFiniteTwistTransport P.Coefficient P.exponent
      (P.exponent_coefficient_eq_zero h)) := by
  have hn : 0 < P.exponent := pow_pos (Fact.out : P.coefficients.l.Prime).pos _
  obtain ⟨r, c, p, hcover, hr, hc, hrest⟩ := Scheme.etaleFiniteTwistPullback
    P.Coefficient P.exponent hn (P.exponent_coefficient_eq_zero h)
  exact ⟨{
    roots := r
    line := fun f hY ↦ c f hY (by simpa using hY.map f.appTop.hom) 1
    roots_normalization := hr
    line_normalization := fun f hY ↦ hc f hY (by simpa using hY.map f.appTop.hom)
  }⟩

/-- Scalar forgetting and the integral generator carry the coordinate module
localization splice to the integral localization pushout spliced with Kummer.
This statement involves no Cartier ideal, frame torsor, exceptional functor or
orientation chart.
Source: Stacks 03PL, 0A45; the finite-coefficient paragraph of the current blueprint
(blueprint: lem-pur-coordinate-localization-scalar-splice).

Proof: forgetting scalars is exact and commutes with the two inverse-image
functors, closed direct image and extension by zero. The constant integral
generator therefore gives a morphism from the integral open-closed sequence to
the underlying coefficient open-closed sequence. More explicitly, write c_q for
the constant pullback comparison along q and g for the integral generator on each
site. The closed component is i_* applied to c_i(Z).hom, then g on the closed
site, then forget(c_i(A).inv), using the literal closed-image/forgetting equality.
The open component is the analogous composite under j_!, followed by the inverse
extension-by-zero/forgetting mate. The unit and counit squares commute by the
adjunction identities; on constant generators they both take one to one. Thus the
closed component is exactly supportedIntegralGenerator conjugated by the constant
comparisons, not a freely chosen comparison.
Use Ext.mapExactFunctor_comp_mk₀_eq_sheaf across the exact-functor comparison
isomorphisms. Naturality of the short-exact Ext class identifies pullback of the
coefficient localization extension with pushout of the integral localization extension.
By definition of kummerEtale as the inverse scalar comparison, its image is the
positive Kummer connecting class of the coordinate, followed by the root
coefficient map. The degree-zero cohomology/section adjunction expresses that
connecting class as the unit section morphism spliced with the Kummer sequence.
The normalized openSection comparison sends precisely this morphism to the
coordinate section. To see uniqueness of that comparison, use naturality on the
localization inclusion and the identity of its open source: both possible images
of that identity map to one under the monic inclusion on open sections, so are
equal. Naturality then determines the comparison on every morphism. Identify the
two integral constant-generator constructions by their common value on one under
the constant-sheaf adjunction. Move the open counit past the Kummer
extension by Ext-class naturality. Reassociate the three Yoneda factors, using
the canonical root pullback and the inverse twist pullback in the open class.
They cancel by naturality of the root coefficient map. Finally all comparisons
are additive, so the minus sign on the module class is the inverse-coordinate
section in the integral pushout. This proves the equation, including on empty
schemes and for coefficients of characteristic two. -/
theorem coordinateLocalization_scalarSplice (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    (C : Etale.PrincipalTorsorComparisons.{u}) (hC : C.Normalized)
    (hL : (Etale.principalTorsorLocalization (zeroSection T)
      ((Line T).basicOpen (coordinate T))
      (coordinateLocalization_complement T)).ShortExact) :
    (Ext.mk₀ (Etale.supportedIntegralGenerator P.Coefficient (zeroSection T))).comp
        ((-P.coordinateLocalizationClass h T aT).mapExactFunctor
          (Etale.RawModuleScalarComparison.forget P.Coefficient (Line T))) (zero_add 2) =
      (((Ext.mk₀ ((Etale.lowerStar AddCommGrpCat.{u + 1} (zeroSection T)).map
          ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
            (zeroSection T)).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)).comp
        (hL.extClass.comp (Ext.mk₀ ((C.openSection (Line T) T (zeroSection T)
          ((Line T).basicOpen (coordinate T))
          (coordinateLocalization_complement T) (Line T).gmSheaf).symm
            (-(ULift.up (Additive.ofMul (coordinateUnit T)))))) (add_zero 1))
        (zero_add 1)).comp
        ((Line T).kummerSequence_shortExact P.exponent
          (P.exponent_isUnit (Line T) (lineProjection T ≫ aT))).extClass
        (rfl : 1 + 1 = 2)).comp
        (Ext.mk₀ (Etale.ordinaryFiniteRootMap P.Coefficient P.exponent
          (P.exponent_coefficient_eq_zero h) (Line T))) (add_zero 2) := by
  obtain ⟨t⟩ := exists_coordinateTwistTransport P h
  have hs := kummerLocalizationSplice P.Coefficient P.exponent
    (P.exponent_coefficient_eq_zero h) t C hC (zeroSection T)
    ((Line T).basicOpen (coordinate T)) (coordinateLocalization_complement T)
    (P.exponent_isUnit (Line T) (lineProjection T ≫ aT)) (coordinateUnit T)
  rw [← coordinateClass_eq_finite P h t T aT] at hs
  have hl : hL.extClass =
      (shortExact_openClosedShortComplex AddCommGrpCat.{u + 1}
        ((Line T).basicOpen (coordinate T)).ι (zeroSection T)
        (supportedIntegralConstant (Line T)) (coordinateLocalization_complement T)).extClass := by
    rfl
  unfold integralLocalizationBoundary at hs
  erw [← hl] at hs
  simp only [map_neg, Ext.mk₀_neg, Ext.comp_neg,
    Ext.neg_comp, ← Functor.mapExtAddHom_apply, constantEtale, ordinaryFiniteConstant, twistEtale,
    Scheme.finiteEtaleTateSheaf, Scheme.finiteEtaleTateTwist] at hs ⊢
  convert congrArg Neg.neg hs using 1
  congr 8

end WeilConjectures.PurityFiniteSetting
