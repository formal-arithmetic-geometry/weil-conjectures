/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H7
-/
module

public import Sheaf.Paper.SectionCompactSourceMaps
import Sheaf.Paper.SectionSourceProExchangeTransport
import Sheaf.Paper.SectionSourceProExchangeConstantSquare

/-! # A component of section compact-source exchange

Source: blueprint rank-one Thom proof, Step 3; Stacks Tags 0F7F and 0D6E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Abelian.toPreadditive
attribute [local irreducible] Functor.rightDerivedFunctorPlus Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
attribute [local implicit_reducible] Functor.mapDerivedCategoryPlus
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem transport_section
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    (N : C ⥤ E) (N' : D ⥤ H) (U : C ⥤ D) (V : E ⥤ H)
    (rho : U ⋙ N' ≅ N ⋙ V)
    {K F : C} {K' F' : D} {P M : E} {P' M' : H}
    (q : N.obj K ≅ M) (q' : N'.obj K' ≅ M')
    (a : K ⟶ F) (a' : K' ⟶ F') (T : N.obj F ⟶ P) (T' : N'.obj F' ⟶ P')
    (e : U.obj F ⟶ F') (d : V.obj P ⟶ P') (k : U.obj K ⟶ K') (kp : V.obj M ⟶ M')
    (hc : V.map T ≫ d = rho.inv.app F ≫ N'.map e ≫ T')
    (hu : rho.hom.app K ≫ V.map q.hom ≫ kp = N'.map k ≫ q'.hom)
    (he : U.map a ≫ e = k ≫ a') :
    V.map (q.inv ≫ N.map a ≫ T) ≫ d = kp ≫ q'.inv ≫ N'.map a' ≫ T' := by
  have hinv : V.map q.inv ≫ rho.inv.app K ≫ N'.map k = kp ≫ q'.inv := by
    apply (cancel_mono q'.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hu]
    simp only [← V.map_comp_assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id,
      V.map_id, Category.id_comp]
  have hn := rho.inv.naturality a
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hc, reassoc_of% hn, ← N'.map_comp_assoc, he, N'.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun t ↦ t ≫ N'.map a' ≫ T') hinv

namespace AlgebraicGeometry.SectionCompactSource
attribute [local implicit_reducible] etaleConstant proConstant etaleSupported proSupported
  compareConstant compareSupported constantPull proConstantPull etaleBeta proBeta
variable (A : Type (u + 1)) [CommRing A]

/-- The pro-etale component of the section exchange.  This is the transport of
`etale_section_exchange_component` through the compact-support site comparison.
Source: Stacks Tags 099R and 0F7F (blueprint: lem-pur-section-source-pro-exchange).
Proof: expand proSource as compareConstant inverse, comparison of etaleSource,
and sourceComparison. Finite-level compact-support site coherence expresses the
actual pro-etale exchange, conjugated by sourceComparison, as comparison of the
etale exchange with its specified endpoint comparison. Naturality moves the
supported-constant maps across the compact-support functors. The closed part of
supported-constant comparison_square identifies the endpoint with proBeta,
while comparison-pullback coherence identifies the initial endpoint with
pullback of compareConstant. The scalar-unit comparison square identifies the
constant pullback with proConstantPull. Substitute the assumed etale equation,
use functoriality, and cancel inverse comparison factors. The result is the
stated pro-etale equation. All comparisons apply after arbitrary base change,
including an empty or non-Noetherian new base. -/
theorem pro_section_exchange_component [Finite A]
    {B X B' X' : Scheme.{u}} {h : X ⟶ B} {h' : X' ⟶ B'}
    {v : X' ⟶ X} {g : B' ⟶ B} (sq : IsPullback v h' h g)
    (c : Compactification h) (s : B ⟶ X) (s' : B' ⟶ X')
    [IsClosedImmersion s] [IsClosedImmersion s']
    (hs : s ≫ h = 𝟙 B) (hs' : s' ≫ h' = 𝟙 B')
    (sqS : ChosenCartesianSquare g s' s v)
    (he : (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.map
        (etaleSource A c s hs).hom ≫
      (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq c).app
        (etaleSupported A s) ≫
      (Etale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).map (etaleBeta A sqS) =
      (constantPull A g).hom ≫ (etaleSource A (c.ofIsPullback sq) s' hs').hom) :
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.map
        (proSource A c s hs) ≫
      proExchange A sq c (proSupported A s) ≫
      (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).map (proBeta A sqS) =
      (proConstantPull A g).hom ≫ proSource A (c.ofIsPullback sq) s' hs' := by
  exact transport_section
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) B).mapDerivedCategoryPlus
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) B').mapDerivedCategoryPlus
    (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus
    (ProEtale.fixedComparisonPullbackPlus A g)
    (compareConstant A B) (compareConstant A B')
    (etaleSource A c s hs).hom (etaleSource A (c.ofIsPullback sq) s' hs').hom
    (sourceComparison A c s) (sourceComparison A (c.ofIsPullback sq) s')
    _ _ (constantPull A g).hom (proConstantPull A g).hom
    (sourceComparison_exchange A sq c s s' sqS) (constant_square A g) he

end AlgebraicGeometry.SectionCompactSource
