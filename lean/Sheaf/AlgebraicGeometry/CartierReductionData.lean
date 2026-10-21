/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.AlgebraicGeometry.CartierPoleBoundary
public import Sheaf.AlgebraicGeometry.GeoCartierCycleClassDefs
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Sheaf.Paper.DivisibleExtensionDerivedReduction
public import Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleComparisonExt
import Sheaf.AlgebraicGeometry.ComparisonForgetScalars
import Sheaf.AlgebraicGeometry.ScalarUnitExtComparison
import Sheaf.AlgebraicGeometry.ScalarUnitExt
public import Sheaf.AlgebraicGeometry.DerivedScalarExtUnit
import Sheaf.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit
import Sheaf.AlgebraicGeometry.CartierComplementFrame
import Sheaf.AlgebraicGeometry.OpenClosedIntegralSections
import Sheaf.CategoryTheory.Sites.RelativeTorsorExtension
import Sheaf.AlgebraicGeometry.ProEtaleUnitsComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison

import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

/-!
# Cartier boundary and normalized reduction constructions

Source: blueprint main-20261015, sk-lem-geo-cartier.proof.md, (G1), derived reduction,
and opening comparison paragraphs (blueprint: lem-sp-cartier-reduction-site-comparison).

The derived scalar units below are expressed by their Hom adjunction against every
unbounded complex. This is an equivalent, model-independent specification of derived
extension of scalars at the supported constant and at G_m. In particular the equality
of reduced maps is an equality in module Ext, not a test on the global section one.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u uC uB vC vB wC wB wE
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Etale sheafification for integral coefficients.
Source: Stacks 00WJ (blueprint: def-sfb-cartier-reduction-data). -/
theorem cartierEtaleAbSheafify (Z : Scheme.{u}) :
    HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u + 1} := inferInstance

/-- Pro-etale sheafification for integral coefficients.
Source: Stacks 00WJ (blueprint: def-sfb-cartier-reduction-data). -/
theorem cartierProAbSheafify (Z : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1} := inferInstance

/-- Etale sheafification for fixed module coefficients.
Source: Stacks 00WJ (blueprint: def-sfb-cartier-reduction-data). -/
theorem cartierEtaleModuleSheafify (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    HasSheafify Z.smallEtaleTopology (ModuleCat.{u + 1} A) := inferInstance

/-- Pro-etale sheafification for fixed module coefficients.
Source: Stacks 00WJ (blueprint: def-sfb-cartier-reduction-data). -/
theorem cartierProModuleSheafify (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A) := inferInstance

/-- Small Ext for the etale coefficient category.
Source: Grothendieck sheaf categories (blueprint: def-sfb-cartier-reduction-data). -/
theorem cartierEtaleAbHasExt (Z : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) := inferInstance

/-- Small Ext for the etale coefficient category.
Source: Grothendieck sheaf categories (blueprint: def-sfb-cartier-reduction-data). -/
theorem cartierEtaleModuleHasExt (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance

/-- Small Ext for the pro coefficient category.
Source: Grothendieck sheaf categories (blueprint: def-sfb-cartier-reduction-data). -/
theorem cartierProAbHasExt (Z : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1}) := inferInstance

/-- Small Ext for the pro coefficient category.
Source: Grothendieck sheaf categories (blueprint: def-sfb-cartier-reduction-data). -/
theorem cartierProModuleHasExt (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) := inferInstance

end AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.cartierEtaleAbSheafify
  AlgebraicGeometry.cartierProAbSheafify AlgebraicGeometry.cartierEtaleModuleSheafify
  AlgebraicGeometry.cartierProModuleSheafify

attribute [local instance] AlgebraicGeometry.cartierEtaleAbHasExt
  AlgebraicGeometry.cartierProAbHasExt AlgebraicGeometry.cartierEtaleModuleHasExt
  AlgebraicGeometry.cartierProModuleHasExt

namespace AlgebraicGeometry.Etale

private theorem supported_one_restrict {D Z : Scheme.{u}} (i : D ⟶ Z)
    (U : Z.Etaleᵒᵖ) :
    ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D)).obj.map
      ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Z).from U.unop).op
      ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 Z)))
        (supportedIntegralOne Z)) =
    (supportedIntegralUnit i).hom.app U ((toSheafify Z.smallEtaleTopology
      ((Functor.const Z.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U ⟨1⟩) := by
  let v := ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Z).from U.unop).op
  have hq := ConcreteCategory.congr_hom ((supportedIntegralUnit i).hom.naturality v)
    (supportedIntegralOne Z)
  have h1 := ConcreteCategory.congr_hom
    ((toSheafify Z.smallEtaleTopology
      ((Functor.const Z.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality v)
    (ULift.up 1)
  simp only [ConcreteCategory.comp_apply, Functor.const_obj_map] at hq h1
  exact hq.symm.trans (congrArg ((supportedIntegralUnit i).hom.app U) h1.symm)


/-- The pole extension has one relative extension class.
Source: blueprint Cartier proof (G1), local lifts paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison).
Proof: glue the subsheaves of meromorphic units generated by units and t inverse.
The quotient sends t inverse to +1; regularity makes the exponent unique on D.
Its fibre over supported one is the frame torsor of the dual ideal, with the
canonical complementary section sent to zero. Conversely an extension with this
relative fibre is reconstructed by local integer powers of such lifts and units.
The reconstruction respects the prescribed complementary splitting and is the
identity on kernel and quotient. Hence all such extensions have the same Ext class. -/
theorem cartierPoleBoundary_existsUnique {D Z : Scheme.{u}} (i : D ⟶ Z)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    ∃! β : Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D))
      Z.gmSheaf 1, CartierPoleBoundarySpec i hI β := by
  have := hI.isInvertible_dual_toModules
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual i.ker.toModules)
  let W : Z.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let P := Scheme.Modules.etaleIsoTorsor (Scheme.Modules.dual i.ker.toModules)
  let τ : P.sheaf.obj.obj (op (Scheme.Etale.mk W.ι)) :=
    Scheme.Modules.etaleIsoTorsorMk (Scheme.Modules.dual i.ker.toModules)
      (U := op (Scheme.Etale.mk W.ι))
    (supportedDivisorSectionPullback i W) (cartierDivisorSectionPullback_isIso i W rfl)
  obtain ⟨L, t, htq, hT, η, hη, hηt⟩ := exists_integral_openClosed_sections i W rfl
  obtain ⟨β, hβ, huniq⟩ := Sheaf.Torsor.relative_extension_existsUnique Z P
    (Scheme.Etale.mk W.ι) τ t (supportedIntegralUnit i) htq hT η hη hηt
  refine ⟨β, ?_, ?_⟩
  · intro W' hW'
    have hWW : W' = W := by apply SetLike.coe_injective; exact hW'
    subst W'
    obtain ⟨E, a, b, hab, hE, f, hfa, hfb, hfτ, hβ⟩ := hβ
    refine ⟨τ, E, a, b, hab, hE, ObjectProperty.homMk f, rfl, ?_, ?_, hfτ, hβ⟩
    · intro U g p
      exact (hfa U g p).trans (add_comm _ _)
    · intro U p
      exact (hfb U p).trans (supported_one_restrict i U).symm
  · intro β' hβ'
    obtain ⟨τ', E, a, b, hab, hE, f, hτ', hfa, hfb, hfτ, hβ'⟩ := hβ' W rfl
    have hτ : τ' = τ := by
      apply Scheme.Modules.etaleIsoTorsorVal_injective (Scheme.Modules.dual i.ker.toModules)
      exact hτ'
    apply huniq β'
    refine ⟨E, a, b, hab, hE, f.hom, ?_, ?_, ?_, hβ'⟩
    · intro U g p
      exact (hfa U g p).trans (add_comm _ _)
    · intro U p
      exact (hfb U p).trans (supported_one_restrict i U)
    · rw [← hτ]
      exact hfτ

/-- The unique relative pole-extension class. No representative extension is chosen.
Source: blueprint Cartier proof (G1)
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierPoleBoundary {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) :
    Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D))
      Z.gmSheaf 1 :=
  Classical.choose (cartierPoleBoundary_existsUnique i hI)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] comparisonUpperStar Etale.cartierPoleBoundary
attribute [local instance 0] IsGroupoid.all_isIso isIso_of_isDiscrete
  HasZeroObject.zero_to_zero_isIso to_initial_isIso terminal_isIso_from initial_isIso_to

/-- Scalar forgetting on the pro-etale site.
Source: blueprint Cartier proof, integral reduction
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
abbrev cartierForget (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :=
  sheafCompose (Scheme.ProEt.topology Z)
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})

/-- Scalar forgetting is exact on the original pro-etale site.
Source: Stacks 03D7 (blueprint: lem-sp-cartier-reduction-site-comparison).
Proof: kernels are sectionwise, and cokernels are the sheafifications of the same
abelian presheaf cokernels. The scalar action descends uniquely to these cokernels. -/
theorem cartierForget_exact (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    PreservesFiniteLimits (cartierForget A Z) ∧
      PreservesFiniteColimits (cartierForget A Z) := by
  constructor
  · have : PreservesFiniteLimits (cartierForget A Z ⋙ sheafToPresheaf _ _) :=
      inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})))
    exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  · have := (Sheaf.forget₂CoinduceAdj (Scheme.ProEt.topology Z) A).isLeftAdjoint
    infer_instance

/-- Exactness on finite limits. Source: Stacks 03D7
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
instance cartierForgetLimits (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    PreservesFiniteLimits (cartierForget A Z) := (cartierForget_exact A Z).1

/-- Exactness on finite colimits. Source: Stacks 03D7
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
instance cartierForgetColimits (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    PreservesFiniteColimits (cartierForget A Z) := (cartierForget_exact A Z).2

/-- Additivity on sections. Source: Stacks 03D7
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
instance cartierForgetAdditive (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    (cartierForget A Z).Additive where

/-- The unit-normalized comparison with scalar forgetting, as the adjoint of the
module comparison unit after forgetting scalars.
Source: Stacks 00WX and the Cartier opening comparison paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierForgetComparison (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u})
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (comparisonUpperStar AddCommGrpCat.{u + 1} Z).obj
        ((Etale.RawModuleScalarComparison.forget A Z).obj M) ⟶
      (cartierForget A Z).obj ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj M) :=
  ((comparisonAdjunction AddCommGrpCat.{u + 1} Z).homEquiv _ _).symm
    ((Etale.RawModuleScalarComparison.forget A Z).map
      ((comparisonAdjunction (ModuleCat.{u + 1} A) Z).unit.app M))

/-- The units comparison is adjoint to identity on the units of every etale object.
Source: blueprint Cartier opening comparison paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierUnitsComparison (Z : Scheme.{u}) :
    (comparisonUpperStar AddCommGrpCat.{u + 1} Z).obj Z.gmSheaf ⟶
      Scheme.proEtaleUnitsSheaf Z :=
  ((comparisonAdjunction AddCommGrpCat.{u + 1} Z).homEquiv _ _).symm ⟨𝟙 _⟩

/-- The canonical comparison on integral constants, normalized by its adjunction unit.
Source: blueprint Cartier comparison paragraph
(blueprint: def-sfb-cartier-reduction-data). -/
def cartierIntegralConstantComparisonIso (D : Scheme.{u}) :
    (comparisonUpperStar AddCommGrpCat.{u + 1} D).obj
        (Etale.supportedIntegralConstant D) ≅
      (constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  (((((constantSheafAdj D.smallEtaleTopology AddCommGrpCat.{u + 1}
        (Scheme.Etale.isTerminalMkId D)).comp
          (comparisonAdjunction AddCommGrpCat.{u + 1} D)).ofNatIsoRight
        ((Scheme.toProEt D).sheafPushforwardContinuousCompSheafSectionsObjIso
          AddCommGrpCat.{u + 1} D.smallEtaleTopology (Scheme.ProEt.topology D)
          (op (Scheme.Etale.mk (𝟙 D))))).leftAdjointUniq
        (constantSheafAdj (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}
          (Scheme.ProEt.isTerminalMkId D))).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

attribute [local irreducible] cartierIntegralConstantComparisonIso

/-- The integral supported source and its canonical mate.
Source: blueprint Cartier opening comparison paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierIntegralSourceComparison {D Z : Scheme.{u}} (i : D ⟶ Z) :
    (comparisonUpperStar AddCommGrpCat.{u + 1} Z).obj
        ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj (Etale.supportedIntegralConstant D)) ⟶
      (lowerStar AddCommGrpCat.{u + 1} i).obj
        ((constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  (lowerStarComparisonUpperStarBaseChange i AddCommGrpCat.{u + 1}).app
      (Etale.supportedIntegralConstant D) ≫
    (lowerStar AddCommGrpCat.{u + 1} i).map
      (cartierIntegralConstantComparisonIso D).hom

/-- Closed direct image comparison on integral coefficients is the invertible
adjunction mate. Source: blueprint Cartier proof, comparison paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison).
Proof: i is finite, hence qcqs. Apply discrete integral direct-image comparison.
Etale finite direct image is exact. Degree zero on the pro-etale side is ordinary
direct image by a nonnegative injective resolution. The unit equation identifies
the resulting isomorphism with this mate, including supported restriction. -/
theorem cartierIntegralSourceComparison_isIso {D Z : Scheme.{u}} (i : D ⟶ Z)
    [IsClosedImmersion i] : IsIso (cartierIntegralSourceComparison i) := by
  have := isIso_lowerStarComparisonUpperStarBaseChange i AddCommGrpCat.{u + 1}
  dsimp only [cartierIntegralSourceComparison]
  infer_instance

/-- The supported mate as an isomorphism, with its actual underlying map.
Source: blueprint Cartier comparison paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierIntegralSourceIso {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    (comparisonUpperStar AddCommGrpCat.{u + 1} Z).obj
        ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj (Etale.supportedIntegralConstant D)) ≅
      (lowerStar AddCommGrpCat.{u + 1} i).obj
        ((constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  @asIso _ _ _ _ (cartierIntegralSourceComparison i)
    (cartierIntegralSourceComparison_isIso i)

attribute [local irreducible] cartierIntegralSourceComparison cartierIntegralSourceIso
  cartierUnitsComparison

/-- Transport of an extension boundary through an exact functor and endpoint maps.
Source: Stacks 0152, naturality of extension classes
(blueprint: def-sfb-cartier-reduction-data). -/
def cartierBoundaryImage
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{wC} C]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{wB} B]
    (U : C ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {F G : C} {F' G' : B} (s : F' ⟶ U.obj F) (t : U.obj G ⟶ G')
    (β : Ext.{wC} F G 1) : Ext.{wB} F' G' 1 :=
  (Ext.mk₀ s).comp ((β.mapExactFunctor U).comp (Ext.mk₀ t) (add_zero 1)) (zero_add 1)

/-- The positive connecting class followed by a change of kernel coefficients.
Source: Stacks 0152 and 03PL
(blueprint: def-sfb-cartier-reduction-data). -/
def cartierKummerClass
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{wC} C]
    {S : ShortComplex C} (hS : S.ShortExact) {H : C} (f : S.X₁ ⟶ H) :
    Ext.{wC} S.X₃ H 1 :=
  (ShortComplex.ShortExact.extClass.{wC} hS).comp (Ext.mk₀ f) (add_zero 1)

/-- The complete integral boundary, pushed from comparison units to the full units.
Source: blueprint Cartier proof (G1) and comparison paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierProBoundary {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (β : Ext.{u + 1} ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
      (Etale.supportedIntegralConstant D)) Z.gmSheaf 1) :
    Ext.{u + 1} ((lowerStar AddCommGrpCat.{u + 1} i).obj
      ((constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) (Scheme.proEtaleUnitsSheaf Z) 1 :=
  cartierBoundaryImage (comparisonUpperStar AddCommGrpCat.{u + 1} Z)
    (cartierIntegralSourceIso i).inv (cartierUnitsComparison Z) β

/-- Restriction of roots, followed by the etale kernel inclusion, is killed by n.
Source: Stacks 03PL (blueprint: lem-sp-cartier-reduction-site-comparison).
Proof: the units comparison is additive, so commutes with n. Apply it to the
kernel equation on the etale side; exact inverse image preserves that equation. -/
theorem cartierRootsComparison_condition (Z : Scheme.{u}) (n : ℕ) :
    ((comparisonUpperStar AddCommGrpCat.{u + 1} Z).map
        (kernel.ι (n • 𝟙 Z.gmSheaf)) ≫ cartierUnitsComparison Z) ≫
      Scheme.proEtaleUnitsPower Z n = 0 := by
  have h := congrArg (comparisonUpperStar AddCommGrpCat.{u + 1} Z).map
    (kernel.condition (n • 𝟙 Z.gmSheaf))
  have hk : n • (comparisonUpperStar AddCommGrpCat.{u + 1} Z).map
      (kernel.ι (n • 𝟙 Z.gmSheaf)) = 0 := by
    simpa only [Functor.map_comp, Functor.map_nsmul, Functor.map_id,
      Functor.map_zero, Preadditive.comp_nsmul, Category.comp_id] using h
  simp only [Scheme.proEtaleUnitsPower, Preadditive.comp_nsmul, Category.comp_id,
    ← Preadditive.nsmul_comp, hk, zero_comp]

/-- The roots-induced target map, fixed by its inclusion in full pro-etale units.
Source: blueprint Cartier comparison paragraph, Stacks 0GLZ and 03PL
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierRootsComparison (Z : Scheme.{u}) (n : ℕ) :
    (comparisonUpperStar AddCommGrpCat.{u + 1} Z).obj (Z.rootsOfUnitySheaf n) ⟶
      Scheme.proEtaleRootsOfUnitySheaf Z n :=
  kernel.lift (Scheme.proEtaleUnitsPower Z n)
    ((comparisonUpperStar AddCommGrpCat.{u + 1} Z).map
      (kernel.ι (n • 𝟙 Z.gmSheaf)) ≫ cartierUnitsComparison Z)
    (cartierRootsComparison_condition Z n)

private theorem unitsComparison_isIso (Z : Scheme.{u}) : IsIso (cartierUnitsComparison Z) := by
  unfold cartierUnitsComparison
  rw [Adjunction.homEquiv_counit]
  let e : Z.gmSheaf ≅
      (comparisonLowerStar AddCommGrpCat.{u + 1} Z).obj (Scheme.proEtaleUnitsSheaf Z) :=
    ⟨⟨𝟙 _⟩, ⟨𝟙 _⟩, by ext U x; rfl, by ext U x; rfl⟩
  have : IsIso e.hom := e.isIso_hom
  have := proEtaleUnitsCounit_isIso Z
  infer_instance

/-- Roots comparison is invertible for invertible n.
Source: blueprint Cartier comparison paragraph, Stacks 0GLZ
(blueprint: lem-sp-cartier-reduction-site-comparison).
Proof: the comparison-section formula evaluates inverse image at U as etale
sections on U. Etale roots pullback, preserving inclusion in units, identifies
these with the n-th roots in Γ(U,O). These natural identifications induce the
kernel lift just defined, and preserve the power action. -/
theorem cartierRootsComparison_isIso (Z : Scheme.{u}) (n : ℕ)
    (hn : 0 < n) (hZ : IsUnit (n : Γ(Z, ⊤))) :
    IsIso (cartierRootsComparison Z n) := by
  have hhn : 0 < n := hn
  have hhZ : IsUnit (n : Γ(Z, ⊤)) := hZ
  clear hhn hhZ
  let F := comparisonUpperStar AddCommGrpCat.{u + 1} Z
  let f := n • 𝟙 Z.gmSheaf
  let g := Scheme.proEtaleUnitsPower Z n
  let a := cartierUnitsComparison Z
  have : IsIso a := unitsComparison_isIso Z
  have w : F.map f ≫ a = a ≫ g := by
    dsimp only [f, g]
    rw [F.map_nsmul, F.map_id]
    simp only [Scheme.proEtaleUnitsPower, Preadditive.nsmul_comp,
      Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]
  let k := kernel.map (F.map f) g a a w
  have : IsIso k := inferInstance
  have heq : cartierRootsComparison Z n = (PreservesKernel.iso F f).hom ≫ k := by
    apply (cancel_mono (kernel.ι g)).1
    change cartierRootsComparison Z n ≫ kernel.ι g =
      (PreservesKernel.iso F f).hom ≫ (k ≫ kernel.ι g)
    have hl : cartierRootsComparison Z n ≫ kernel.ι g = F.map (kernel.ι f) ≫ a :=
      kernel.lift_ι g _ _
    have hk : k ≫ kernel.ι g = kernel.ι (F.map f) ≫ a := kernel.lift_ι g _ _
    rw [hl, hk, ← Category.assoc, PreservesKernel.iso_hom,
      kernelComparison_comp_ι]
  rw [heq]
  infer_instance

/-- The canonical roots isomorphism.
Source: blueprint Cartier comparison paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierRootsIso (Z : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hZ : IsUnit (n : Γ(Z, ⊤))) :
    (comparisonUpperStar AddCommGrpCat.{u + 1} Z).obj (Z.rootsOfUnitySheaf n) ≅
      Scheme.proEtaleRootsOfUnitySheaf Z n :=
  @asIso _ _ _ _ (cartierRootsComparison Z n) (cartierRootsComparison_isIso Z n hn hZ)

attribute [local irreducible] cartierRootsComparison cartierRootsIso

/-- The root tensor map to the finite pro-etale Tate line.
Source: blueprint Cartier finite coefficient extension paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierProRootMap (A : Type (u + 1)) [CommRing A] (n : ℕ) (hA : (n : A) = 0)
    (Z : Scheme.{u}) (hn : 0 < n) (hZ : IsUnit (n : Γ(Z, ⊤))) :
    Scheme.proEtaleRootsOfUnitySheaf Z n ⟶
      (cartierForget A Z).obj (geoCartierLine A n hA Z) :=
  (cartierRootsIso Z n hn hZ).inv ≫
    (comparisonUpperStar AddCommGrpCat.{u + 1} Z).map
      (Etale.ordinaryFiniteRootMap A n hA Z) ≫
    cartierForgetComparison A Z (Scheme.finiteEtaleTateLine Z n A hA)

/-- The coefficient unit on the supported integral constant, induced by 1 ↦ 1.
Source: blueprint Cartier source normalization paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierProIntegralGenerator (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    (lowerStar AddCommGrpCat.{u + 1} i).obj
        ((constantSheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ⟶
      (cartierForget A Z).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D)) :=
  (cartierIntegralSourceIso i).inv ≫
    (comparisonUpperStar AddCommGrpCat.{u + 1} Z).map
      (Etale.supportedIntegralGenerator A i) ≫
    cartierForgetComparison A Z
      ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj (Etale.ordinaryFiniteConstant A D)) ≫
    (cartierForget A Z).map (geoCartierSourceComparison A i)

attribute [local irreducible] cartierProRootMap cartierProIntegralGenerator

/-- The actual pro-etale Kummer short complex, with its kernel inclusion.
Source: Stacks 03PL (blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierProKummerComplex (Z : Scheme.{u}) (n : ℕ) :
    ShortComplex (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (Scheme.proEtaleRootsOfUnityInclusion Z n)
    (Scheme.proEtaleUnitsPower Z n) (kernel.condition (Scheme.proEtaleUnitsPower Z n))

/-- Kummer is exact on every pro-etale scheme object.
Source: Stacks 03PL and blueprint Cartier reduction paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison).
Proof: the first map is the kernel inclusion. For a unit on any pro-etale U,
Kummer on U produces an etale covering on which it has an n-th root. These are
pro-etale coverings of U, proving epimorphy of the power map. -/
theorem cartierProKummer_exact (Z : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hZ : IsUnit (n : Γ(Z, ⊤))) : (cartierProKummerComplex Z n).ShortExact := by
  have hhn : 0 < n := hn
  clear hhn
  let F := comparisonUpperStar AddCommGrpCat.{u + 1} Z
  have : F.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (comparisonAdjunction AddCommGrpCat.{u + 1} Z)
  let f := n • 𝟙 Z.gmSheaf
  let a := cartierUnitsComparison Z
  have : IsIso a := unitsComparison_isIso Z
  have : Epi f := (Z.kummerSequence_shortExact n hZ).epi_g
  have : Epi (F.map f) := F.map_epi f
  have w : F.map f ≫ a = a ≫ Scheme.proEtaleUnitsPower Z n := by
    dsimp only [f]
    rw [F.map_nsmul, F.map_id]
    simp only [Scheme.proEtaleUnitsPower, Preadditive.nsmul_comp,
      Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]
  have hepi : Epi (F.map f ≫ a) := by infer_instance
  have : Epi (Scheme.proEtaleUnitsPower Z n) := epi_of_epi_fac w.symm
  exact
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
      mono_f := by dsimp [cartierProKummerComplex, Scheme.proEtaleRootsOfUnityInclusion]
                   infer_instance
      epi_g := by
        change Epi (Scheme.proEtaleUnitsPower Z n)
        infer_instance }

/-- The normalized Kummer scalar unit on etale units, expressed in abelian Ext.
Source: blueprint Cartier reduction paragraph, Stacks 0152 and 03PL
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierEtaleKummerUnit (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : (n : A) = 0) (Z : Scheme.{u}) (hZ : IsUnit (n : Γ(Z, ⊤))) :
    Ext.{u + 1} Z.gmSheaf ((Etale.RawModuleScalarComparison.forget A Z).obj
      (Scheme.finiteEtaleTateLine Z n A hA)) 1 :=
  cartierKummerClass (Z.kummerSequence_shortExact n hZ)
    (Etale.ordinaryFiniteRootMap A n hA Z)

/-- The normalized Kummer scalar unit on full pro-etale units.
Source: blueprint Cartier reduction paragraph, Stacks 0152 and 03PL
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierProKummerUnit (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : (n : A) = 0) (Z : Scheme.{u}) (hn : 0 < n)
    (hZ : IsUnit (n : Γ(Z, ⊤))) :
    Ext.{u + 1} (Scheme.proEtaleUnitsSheaf Z)
      ((cartierForget A Z).obj (geoCartierLine A n hA Z)) 1 :=
  cartierKummerClass (cartierProKummer_exact Z n hn hZ)
    (cartierProRootMap A n hA Z hn hZ)

attribute [local irreducible] cartierProBoundary cartierEtaleKummerUnit cartierProKummerUnit

/-- The scalar adjunct equation of a boundary, for exact coefficient forgetting.
Source: blueprint Cartier reduction paragraphs
(blueprint: def-sfb-cartier-reduction-data).
This factors the common Ext equation through abstract abelian categories, keeping
its concrete coefficient and site constructions out of the composition API. -/
def cartierScalarBoundaryEquation
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{wC} C]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{wB} B]
    (U : C ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {F G : B} {P Q : C} (η : F ⟶ U.obj P) (c : Ext.{wC} P Q 2)
    (β : Ext.{wB} F G 1) (κ : Ext.{wB} G (U.obj Q) 1) : Prop :=
  (Ext.mk₀ η).comp (c.mapExactFunctor U) (zero_add 2) = β.comp κ (rfl : 1 + 1 = 2)

/-- The etale reduction is the scalar adjunct of the entire pole boundary followed
by the positive Kummer unit. This is an equation on the supported integral sheaf,
not its section one.
Source: blueprint Cartier derived reduction paragraphs
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def CartierEtaleReductionSpec (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : (n : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hZ : IsUnit (n : Γ(Z, ⊤)))
    (c : Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
      (Etale.ordinaryFiniteConstant A D)) (Scheme.finiteEtaleTateLine Z n A hA) 2) : Prop :=
  cartierScalarBoundaryEquation (Etale.RawModuleScalarComparison.forget A Z)
    (Etale.supportedIntegralGenerator A i) c (Etale.cartierPoleBoundary i hI)
    (cartierEtaleKummerUnit A n hA Z hZ)

/-- The pro-etale reduction uses the same full-boundary adjunct equation, with the
canonical supported mate, full units comparison, and roots-induced target.
Source: blueprint Cartier derived reduction and comparison paragraphs
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def CartierProReductionSpec (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : (n : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hn : 0 < n) (hZ : IsUnit (n : Γ(Z, ⊤)))
    (c : GeoCartierClass A n hA i) : Prop :=
  cartierScalarBoundaryEquation (cartierForget A Z) (cartierProIntegralGenerator A i) c
    (cartierProBoundary i (Etale.cartierPoleBoundary i hI))
    (cartierProKummerUnit A n hA Z hn hZ)

attribute [local irreducible] CartierEtaleReductionSpec CartierProReductionSpec

private theorem cartierSourceComparison_isIso (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    IsIso (geoCartierSourceComparison A i) := by
  have := isIso_lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)
  unfold geoCartierSourceComparison
  infer_instance

private theorem cartierProIntegralGenerator_ext_bijective
    (A : Type (u + 1)) [CommRing A] [Finite A] (n : ℕ) (hn : 0 < n)
    (hA : (n : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    Function.Bijective (fun c : GeoCartierClass A n hA i ↦
      (Ext.mk₀.{u + 1} (cartierProIntegralGenerator A i)).comp
        (c.mapExactFunctor (cartierForget A Z)) (zero_add 2)) := by
  have hsource := Etale.supported_integral_derived_unit Z n hn A hA i
  have hU := scalar_unit_ext_bijective
    (Etale.RawModuleScalarComparison.forget A Z)
    (Q := Scheme.finiteEtaleTateLine Z n A hA)
    (Etale.supportedIntegralGenerator A i) hsource 2
  have : IsIso (geoCartierSourceComparison A i) := cartierSourceComparison_isIso A i
  have hF := comparison_mapExt_bijective (ModuleCat.{u + 1} A) Z
    ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj (Etale.ordinaryFiniteConstant A D))
    (Scheme.finiteEtaleTateLine Z n A hA) 2
  have hG := comparison_mapExt_bijective AddCommGrpCat.{u + 1} Z
    ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj (Etale.supportedIntegralConstant D))
    ((Etale.RawModuleScalarComparison.forget A Z).obj
      (Scheme.finiteEtaleTateLine Z n A hA)) 2
  have h := Ext.scalar_unit_ext_comparison_bijective
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z)
    (comparisonUpperStar AddCommGrpCat.{u + 1} Z)
    (Etale.RawModuleScalarComparison.forget A Z) (cartierForget A Z)
    (forgetComparisonIso A Z) (Etale.supportedIntegralGenerator A i)
    (cartierIntegralSourceIso i) (asIso (geoCartierSourceComparison A i)) 2 hU hF hG
  unfold cartierProIntegralGenerator cartierForgetComparison
  simpa only [forgetComparisonIso_hom, asIso_hom, cartierForget, Functor.comp_obj,
    GeoCartierClass, geoCartierLine] using h

/-- Existence and uniqueness of the two canonically normalized reduced arrows.
Source: blueprint Cartier derived reduction paragraphs, Stacks 06YY and 0152
(blueprint: lem-sp-cartier-reduction-site-comparison).
Proof: supported integral constants have stalk Z or zero, so their derived reduction
is the residue supported constant with the quotient unit. Kummer identifies derived
reduction of G_m with the roots shifted once, with its scalar unit the Kummer boundary.
The divisible-extension theorem gives this sign and its naturality. Flatness of the
roots line extends these identifications from Z/n to every finite n-torsion A, including
nonflat A. The scalar adjunction then gives one and only one arrow with each displayed
adjunct equation. The same argument applies to full pro-etale units by Kummer there. -/
theorem cartierReduction_existsUnique (A : Type (u + 1)) [CommRing A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hA : (n : A) = 0) {D Z : Scheme.{u}}
    (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit (n : Γ(Z, ⊤))) :
    (∃! c : Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
        (Etale.ordinaryFiniteConstant A D)) (Scheme.finiteEtaleTateLine Z n A hA) 2,
      CartierEtaleReductionSpec A n hA i hI hZ c) ∧
    (∃! c : GeoCartierClass A n hA i,
      CartierProReductionSpec A n hA i hI hn hZ c) := by
  have hsource := Etale.supported_integral_derived_unit Z n hn A hA i
  have hE := scalar_unit_ext_bijective
    (Etale.RawModuleScalarComparison.forget A Z)
    (Q := Scheme.finiteEtaleTateLine Z n A hA)
    (Etale.supportedIntegralGenerator A i) hsource 2
  have hP := cartierProIntegralGenerator_ext_bijective A n hn hA i
  constructor
  · unfold CartierEtaleReductionSpec cartierScalarBoundaryEquation
    exact hE.existsUnique ((Etale.cartierPoleBoundary i hI).comp
      (cartierEtaleKummerUnit A n hA Z hZ) (rfl : 1 + 1 = 2))
  · unfold CartierProReductionSpec cartierScalarBoundaryEquation
    exact hP.existsUnique ((cartierProBoundary i (Etale.cartierPoleBoundary i hI)).comp
      (cartierProKummerUnit A n hA Z hn hZ) (rfl : 1 + 1 = 2))

/-- The etale reduced arrow, uniquely determined by its scalar adjunct.
Source: blueprint Cartier reduction paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierReducedEtale (A : Type (u + 1)) [CommRing A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hA : (n : A) = 0) {D Z : Scheme.{u}}
    (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit (n : Γ(Z, ⊤))) :
    Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj
      (Etale.ordinaryFiniteConstant A D)) (Scheme.finiteEtaleTateLine Z n A hA) 2 :=
  Classical.choose (cartierReduction_existsUnique A n hn hA i hI hZ).1

/-- The pro-etale reduced arrow, uniquely determined by its scalar adjunct.
Source: blueprint Cartier reduction paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierReducedPro (A : Type (u + 1)) [CommRing A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hA : (n : A) = 0) {D Z : Scheme.{u}}
    (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit (n : Γ(Z, ⊤))) : GeoCartierClass A n hA i :=
  Classical.choose (cartierReduction_existsUnique A n hn hA i hI hZ).2

attribute [local irreducible] cartierReducedEtale cartierReducedPro

/-- The Hom universal property of a derived scalar unit with a shifted sheaf target.
It is tested against every unbounded complex, and therefore determines the target up
to its unique unit-compatible isomorphism.
Source: Stacks 09T5, 0FND and blueprint Cartier reduction paragraphs
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def CartierScalarUnit
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B] [HasExt.{wE} B]
    (U : C ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (F : B) (H : C) (n : ℕ) (e : Ext F (U.obj H) n) : Prop :=
  U.DerivedExtUnit F H n e

/-- The coefficient ring R = Z/(ℓ^r), lifted to the common sheaf universe.
Source: blueprint Cartier reduction paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
abbrev cartierResidueRing (ℓ r : ℕ) := ULift.{u + 1} (ZMod (ℓ ^ r))

/-- The modulus annihilates its residue coefficient ring.
Source: blueprint Cartier reduction paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison).
Proof: the integer ℓ^r maps to zero in Z/(ℓ^r); the ring equivalence ULift preserves casts. -/
theorem cartierResidue_cast (ℓ r : ℕ) : ((ℓ ^ r : ℕ) : cartierResidueRing.{u} ℓ r) = 0 := by
  apply ULift.ringEquiv.injective
  simpa only [map_natCast, map_zero] using ZMod.natCast_self (ℓ ^ r)

/-- The specified R-algebra structure on A, uniquely determined by its integer action.
Source: blueprint Cartier finite coefficient extension paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierResidueAlgebra (ℓ r : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : ((ℓ ^ r : ℕ) : A) = 0) : cartierResidueRing.{u} ℓ r →+* A :=
  (Scheme.finiteEtaleTwistScalar (ℓ ^ r) A hA).comp ULift.ringEquiv.toRingHom

/-- The prime-power residue ring is finite.
Source: blueprint Cartier reduction paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison).
Proof: a prime is positive, so its power is nonzero; ZMod of a nonzero natural
number is finite, and lifting a finite type preserves finiteness. -/
theorem cartierResidue_finite (ℓ : ℕ) (hℓ : ℓ.Prime) (r : ℕ) :
    Finite (cartierResidueRing.{u} ℓ r) := by
  have : NeZero (ℓ ^ r) := ⟨ne_of_gt (pow_pos hℓ.pos r)⟩
  exact Finite.of_equiv (ZMod (ℓ ^ r)) Equiv.ulift.symm

/-- The normalized residue-coefficient arrow, with finiteness supplied explicitly.
Source: blueprint Cartier reduction paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierResidueReducedPro (ℓ : ℕ) (hℓ : ℓ.Prime) (r : ℕ)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))) :
    GeoCartierClass (cartierResidueRing.{u} ℓ r) (ℓ ^ r) (cartierResidue_cast ℓ r) i :=
  letI : Finite (cartierResidueRing.{u} ℓ r) := cartierResidue_finite ℓ hℓ r
  cartierReducedPro (cartierResidueRing.{u} ℓ r) (ℓ ^ r) (pow_pos hℓ.pos r)
    (cartierResidue_cast ℓ r) i hI hZ

attribute [local irreducible] cartierResidueReducedPro

end AlgebraicGeometry.ProEtale
