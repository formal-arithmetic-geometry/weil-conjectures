/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Sheaf.AlgebraicGeometry.QcoherentPullbackSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap

/-! # Section formulas and the constructed coherent etale pullback map -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange
attribute [local irreducible] tensorPullback tensorPullbackObj tensorSectionsComp
  tensorSectionsUnit qcoherentPullbackSection
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

/-- The exact structural section formula for a coherent etale coefficient map.
Source: Stacks Project, Tags 03Q8 and 03DR.
(blueprint: def-weil-pbc-coherent-etale-pullback-data). -/
structure HasQcoherentPullbackSectionFormula {X Y : Scheme.{u}}
    (g : Y ⟶ X) (F : X.Modules) (G : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (ψ : (tensorPullback g).obj F ⟶ G)
    (θ : liftedCoherentEtaleSheaf F ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (liftedCoherentEtaleSheaf G)) : Prop where
  app : ∀ (U : X.Etale) (s : (etaleTensorSectionsSheaf F).obj.obj (op U)),
    θ.hom.app (op U) (ULift.up s) = ULift.up
      (qcoherentPullbackSection g F G ψ U
        ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj U)
        (pullback.fst U.hom g) pullback.condition s)

/-- The named section formula is exactly the displayed formula for all sections.
Source: Stacks Project, Tags 03Q8 and 03DR.
(blueprint: def-weil-pbc-coherent-etale-pullback-data).
Proof: project the universal section equation, or package that equation in the proposition. -/
theorem hasQcoherentPullbackSectionFormula_iff {X Y : Scheme.{u}}
    (g : Y ⟶ X) (F : X.Modules) (G : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (ψ : (tensorPullback g).obj F ⟶ G)
    (θ : liftedCoherentEtaleSheaf F ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (liftedCoherentEtaleSheaf G)) :
    HasQcoherentPullbackSectionFormula g F G ψ θ ↔
      ∀ (U : X.Etale) (s : (etaleTensorSectionsSheaf F).obj.obj (op U)),
        θ.hom.app (op U) (ULift.up s) = ULift.up
          (qcoherentPullbackSection g F G ψ U
            ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ g).obj U)
            (pullback.fst U.hom g) pullback.condition s) := by
  exact ⟨fun h ↦ h.app, fun h ↦ ⟨h⟩⟩

/-- Equal module morphisms have the same structural section formula.
Source: Stacks Project, Tag 03DR; equality substitution.
(blueprint: def-weil-pbc-coherent-etale-pullback-data).
Proof: substitute the equality of coefficient morphisms; the given formula then
has exactly the required type. -/
theorem hasQcoherentPullbackSectionFormula_congr {X Y : Scheme.{u}}
    (g : Y ⟶ X) (F : X.Modules) (G : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ ψ' : (tensorPullback g).obj F ⟶ G) (h : ψ = ψ')
    (θ : liftedCoherentEtaleSheaf F ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (liftedCoherentEtaleSheaf G)) :
    HasQcoherentPullbackSectionFormula g F G ψ θ →
      HasQcoherentPullbackSectionFormula g F G ψ' θ := by
  cases h
  exact fun hθ ↦ hθ

/-- Cohomological pullback followed by the adjunct coefficient morphism.
Source: Stacks Project, Tags 03Q8 and 03FD.
(blueprint: def-weil-pbc-coherent-etale-pullback-data). -/
@[irreducible] def coherentEtalePullbackMap {X Y : Scheme.{u}}
    (g : Y ⟶ X) (F : X.Modules) (G : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (θ : liftedCoherentEtaleSheaf F ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (liftedCoherentEtaleSheaf G)) (q : ℕ) :
    Sheaf.H (liftedCoherentEtaleSheaf F) q → Sheaf.H (liftedCoherentEtaleSheaf G) q :=
  fun x ↦ Sheaf.H.map
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
      (liftedCoherentEtaleSheaf F) (liftedCoherentEtaleSheaf G) |>.symm θ)
    q (Etale.cohomologyMap g (liftedCoherentEtaleSheaf F) q x)

/-- Evaluation of the constructed pullback map gives the prescribed composite.
Source: Stacks Project, Tags 03Q8 and 03FD.
(blueprint: def-weil-pbc-coherent-etale-pullback-data).
Proof: unfold the function and evaluate it at x. -/
theorem coherentEtalePullbackMap_apply {X Y : Scheme.{u}}
    (g : Y ⟶ X) (F : X.Modules) (G : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (θ : liftedCoherentEtaleSheaf F ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (liftedCoherentEtaleSheaf G)) (q : ℕ)
    (x : Sheaf.H (liftedCoherentEtaleSheaf F) q) :
    coherentEtalePullbackMap g F G θ q x = Sheaf.H.map
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
        (liftedCoherentEtaleSheaf F) (liftedCoherentEtaleSheaf G) |>.symm θ)
      q (Etale.cohomologyMap g (liftedCoherentEtaleSheaf F) q x) := by
  unfold coherentEtalePullbackMap
  rfl

end
end AlgebraicGeometry.Scheme.Modules
