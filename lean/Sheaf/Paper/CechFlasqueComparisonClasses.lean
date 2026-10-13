module

public import Sheaf.Paper.CechCupResolutionComparisonData
public import Sheaf.Paper.CechFlasqueComparisonCore

@[expose] public section
universe v
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Homology identifications and canonical-class compatibilities for the core maps.
Source: Stacks Project, Tags 01EQ and 0FKV, cancellation against the injective
resolution comparison.
(blueprint: lem-sc-cech-flasque-resolution-comparison-classes)

Given the core maps and their quasi-isomorphism, compare the computing resolution
with the chosen injective resolution. The resulting invertible homology map defines
`iso`; cancellation in the alpha square gives `alpha_class`, while the beta square
and the defining injective Cech comparison give `beta_class`. -/
theorem cechFlasqueComparisonClasses {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F : X.Modules} (D : CupAcyclicResolution F)
    (alpha : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K ⟶ (cupCechDouble U D.K).total (ComplexShape.up ℕ))
    (beta : (cechComplexFunctor U).obj F.presheafModuleCat ⟶
      (cupCechDouble U D.K).total (ComplexShape.up ℕ)) [QuasiIso alpha]
    (halpha : ∀ n : ℕ, alpha.f n = moduleCechZero U (D.K.X n) ≫
      (cupCechDouble U D.K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp))
    (hbeta : ∀ n : ℕ, beta.f n =
      ((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (D.augmentation.f 0).val)).f n ≫
      (cupCechDouble U D.K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp)) :
    ∃ iso : ∀ n : ℕ, (RingedSpace.moduleCohomology X.toRingedSpace n).obj F ≅
      ((cupCechDouble U D.K).total (ComplexShape.up ℕ)).homology n,
      (∀ (n : ℕ)
        (z : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K),
        (iso n).hom (D.class n z) =
          HomologicalComplex.homologyMap alpha n (cupCycleClass _ n z)) ∧
      (∀ (n : ℕ)
        (c : ((cechComplexFunctor U).obj F.presheafModuleCat).homology n ⟶
          (RingedSpace.moduleCohomology X.toRingedSpace n).obj F),
        IsModuleCechComparison U F n c →
        ∀ z : (((cechComplexFunctor U).obj F.presheafModuleCat).sc n).moduleCatLeftHomologyData.K,
          (iso n).hom (c (cupCycleClass _ n z)) =
            HomologicalComplex.homologyMap beta n (cupCycleClass _ n z)) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
