/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.CategoryTheory.ModuleObjects.LiftExact
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Projection

/-!
# Balanced open projection for internal modules

Source: blueprint `sec-six-functors-basics/sk-lem-int-tensor/`
`det-lem-int-tensor-projection.proof.md`, open immersions, sheaves
(blueprint: lem-pd-open-module-balanced-projection).

The comparison uses the recorded ordinary balanced tensor comparison, transported to
extension-of-scalars inverse image. The two separate balancing equations retain the
coefficient-factor normalization, as well as the actual map on the coequalizers.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The coefficient identification of the underlying module pullback with abelian pullback.
Source: blueprint open-immersion calculation, coefficient identification alpha
(blueprint: lem-pd-open-module-balanced-projection). -/
noncomputable def openModulePullbackUnderlyingIso {U Z : Scheme.{u}} (j : U ⟶ Z)
    (N : supportModules Λ Z) :
    ((upperStar Λ j).obj N).X ≅ (ProEtale.upperStar Ab.{u + 1} j).obj N.X :=
  (Mod.forget (condensedRingObj Λ U)).mapIso
    ((supportPullbackIsoUpperStar Λ j).symm.app N)

/-- The inverse of the recorded ordinary tensor comparison, on the specified module pullback.
Source: blueprint open-immersion calculation, the map nu induced on balanced generators
(blueprint: lem-pd-open-module-balanced-projection). -/
noncomputable def openModuleTensorComparison {U Z : Scheme.{u}} (j : U ⟶ Z)
    (A B : supportModules Λ Z) :
    (upperStar Λ j).obj A ⊗ (upperStar Λ j).obj B ⟶ (upperStar Λ j).obj (A ⊗ B) :=
  (tensorIso ((supportPullbackIsoUpperStar Λ j).symm.app A)
      ((supportPullbackIsoUpperStar Λ j).symm.app B)).hom ≫
    (supportTensorComparison Λ j A B).inv ≫
      (supportPullbackIsoUpperStar Λ j).hom.app (A ⊗ B)

/-- The specified adjunction mate theta, with its tensor-unit and counit formula.
Source: blueprint open-immersion calculation, definition of theta
(blueprint: lem-pd-open-module-balanced-projection). -/
noncomputable def openModuleBalancedProjectionMap {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (M : supportModules Λ U) (N : supportModules Λ Z) :
    (openImmersionLowerShriek Λ j).obj (M ⊗ (upperStar Λ j).obj N) ⟶
      (openImmersionLowerShriek Λ j).obj M ⊗ N :=
  (openImmersionLowerShriek Λ j).map
      ((openImmersionLowerShriekUpperStarAdjunction Λ j).unit.app M ▷
          (upperStar Λ j).obj N ≫
        openModuleTensorComparison Λ j ((openImmersionLowerShriek Λ j).obj M) N) ≫
    (openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app
      ((openImmersionLowerShriek Λ j).obj M ⊗ N)

/-- The abelian projection isomorphism in the order M tensor j-star L, obtained by braiding.
Source: blueprint open-immersion calculation, abelian projection and its coefficient factor
(blueprint: lem-pd-open-module-balanced-projection). -/
noncomputable def openModuleAbelianProjectionIso {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (M : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
    (L : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :
    (ProEtale.openImmersionLowerShriek Ab.{u + 1} j).obj
        (M ⊗ (ProEtale.upperStar Ab.{u + 1} j).obj L) ≅
      (ProEtale.openImmersionLowerShriek Ab.{u + 1} j).obj M ⊗ L :=
  (ProEtale.openImmersionLowerShriek Ab.{u + 1} j).mapIso (β_ _ _) ≪≫
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j
      ).projectionFormula.iso L M ≪≫ β_ _ _

/-- H0: the canonical abelian comparison at the targets of the two balancing arrows.
Source: blueprint open-immersion calculation, balanced-coequalizer proof Step 5
(blueprint: lem-pd-open-module-balanced-projection). -/
noncomputable def openModuleBalanceTargetIso {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (M : supportModules Λ U) (N : supportModules Λ Z) :
    (ProEtale.openImmersionLowerShriek Ab.{u + 1} j).obj
        (M.X ⊗ ((upperStar Λ j).obj N).X) ≅
      ((openImmersionLowerShriek Λ j).obj M).X ⊗ N.X :=
  (ProEtale.openImmersionLowerShriek Ab.{u + 1} j).mapIso
      (tensorIso (Iso.refl M.X) (openModulePullbackUnderlyingIso Λ j N)) ≪≫
    openModuleAbelianProjectionIso j M.X N.X

/-- H1: the canonical abelian comparison including the coefficient factor.
It uses alpha-inverse, the abelian tensorator and the same projection isomorphism as H0.
Source: blueprint open-immersion calculation, balanced-coequalizer proof Step 5
(blueprint: lem-pd-open-module-balanced-projection). -/
noncomputable def openModuleBalanceSourceIso {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (M : supportModules Λ U) (N : supportModules Λ Z) :
    (ProEtale.openImmersionLowerShriek Ab.{u + 1} j).obj
        ((M.X ⊗ condensedRingObj Λ U) ⊗ ((upperStar Λ j).obj N).X) ≅
      (((openImmersionLowerShriek Λ j).obj M).X ⊗ condensedRingObj Λ Z) ⊗ N.X :=
  (ProEtale.openImmersionLowerShriek Ab.{u + 1} j).mapIso
      ((α_ _ _ _) ≪≫ tensorIso (Iso.refl M.X)
        (tensorIso (asIso (condensedPullbackHom Λ j)).symm
            (openModulePullbackUnderlyingIso Λ j N) ≪≫
          asIso (Functor.LaxMonoidal.μ (ProEtale.upperStar Ab.{u + 1} j)
            (condensedRingObj Λ Z) N.X))) ≪≫
    openModuleAbelianProjectionIso j M.X (condensedRingObj Λ Z ⊗ N.X) ≪≫
      (α_ _ _ _).symm

/-- Exactness, the normalized invertible unit, and the balanced open projection formula.
Source: blueprint `det-lem-int-tensor-projection.proof.md`, open immersions, sheaves
(blueprint: lem-pd-open-module-balanced-projection).

Proof:
1. Identify j-star Lambda_Z with Lambda_U by the canonical alpha. Scalar extension and
coextension along alpha are restriction along its inverse. The specified linearized
adjunction restricts the abelian Hom bijection, so its unit forgets to the abelian unit.
2. Extension by zero is additive and exact. Abelian inverse image is additive and exact;
transporting its module action along alpha proves the same for module inverse image.
3. Abelian extension by zero is fully faithful, so its adjunction unit is invertible by
fullness, faithfulness and the two triangle identities. Its inverse is linear: multiply
the action-compatibility equation of the unit on both sides by the inverse.
4. Braid the abelian projection formula to the order M tensor j-star N. The action on
extension by zero is its linearized action using the inverse coefficient-factor projection.
The projection formula's associativity coherence includes an additional coefficient factor.
5. H0 and H1 are the displayed abelian projections, with alpha restored. Naturality in N
identifies the second balancing arrow; the coefficient action formula and associativity
coherence identify the first. Each equation retains the original order of the arrows.
6. Abelian extension by zero preserves the balancing coequalizer. H0,H1 and their inverses
therefore induce inverse maps on the two coequalizers. The quotient actions are through
M. Precomposing with the coefficient tensor quotient shows the induced map is linear;
tensor preserves the coequalizer, so that precomposition detects equality. Its inverse
is linear by the inverse action equation.
7. The balanced-generator characterization of the recorded comparison shows that the
transpose of the induced quotient map is unit tensor identity followed by nu. The quotient
is epic, so these transposes agree. The specified module Hom bijection identifies the
quotient map with theta, exactly the displayed counit formula.
8. Naturality of H0,H1 and the quotient maps proves naturality in M,N after precomposing
with the epic image of the source quotient. No derived or constructibility claim is used. -/
theorem openModuleBalancedProjection
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {U Z : Scheme.{u}} [U.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [LocallyOfFiniteType (U ↘ Spec (.of k))]
    [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    (j : U ⟶ Z) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] :
    (openImmersionLowerShriek Λ j).Additive ∧
    PreservesFiniteLimits (openImmersionLowerShriek Λ j) ∧
    PreservesFiniteColimits (openImmersionLowerShriek Λ j) ∧
    (upperStar Λ j).Additive ∧ PreservesFiniteLimits (upperStar Λ j) ∧
    PreservesFiniteColimits (upperStar Λ j) ∧
    (∀ M : supportModules Λ U,
      ∃ e : M ≅ (upperStar Λ j).obj ((openImmersionLowerShriek Λ j).obj M),
        e.hom = (openImmersionLowerShriekUpperStarAdjunction Λ j).unit.app M ∧
        e.hom.hom ≫
            (openModulePullbackUnderlyingIso Λ j ((openImmersionLowerShriek Λ j).obj M)).hom =
          (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).unit.app M.X ∧
        γ[condensedRingObj Λ U,((upperStar Λ j).obj
            ((openImmersionLowerShriek Λ j).obj M)).X] ≫ e.inv.hom =
          condensedRingObj Λ U ◁ e.inv.hom ≫ γ[condensedRingObj Λ U,M.X]) ∧
    (∀ (M : supportModules Λ U) (N : supportModules Λ Z),
      IsIso (openModuleBalancedProjectionMap Λ j M N) ∧
      (openImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv _ _
          (openModuleBalancedProjectionMap Λ j M N) =
        (openImmersionLowerShriekUpperStarAdjunction Λ j).unit.app M ▷
            (upperStar Λ j).obj N ≫
          openModuleTensorComparison Λ j ((openImmersionLowerShriek Λ j).obj M) N) ∧
    (∀ (M M' : supportModules Λ U) (N N' : supportModules Λ Z)
        (a : M ⟶ M') (b : N ⟶ N'),
      (openImmersionLowerShriek Λ j).map (a ⊗ₘ (upperStar Λ j).map b) ≫
          openModuleBalancedProjectionMap Λ j M' N' =
        openModuleBalancedProjectionMap Λ j M N ≫
          ((openImmersionLowerShriek Λ j).map a ⊗ₘ b)) ∧
    ∀ (M : supportModules Λ U) (N : supportModules Λ Z),
      (ProEtale.openImmersionLowerShriek Ab.{u + 1} j).map
          (((β_ M.X (condensedRingObj Λ U)).hom ≫
            γ[condensedRingObj Λ U,M.X]) ▷ ((upperStar Λ j).obj N).X) ≫
          (openModuleBalanceTargetIso Λ j M N).hom =
        (openModuleBalanceSourceIso Λ j M N).hom ≫
          (((β_ ((openImmersionLowerShriek Λ j).obj M).X (condensedRingObj Λ Z)).hom ≫
            γ[condensedRingObj Λ Z,((openImmersionLowerShriek Λ j).obj M).X]) ▷ N.X) ∧
      (ProEtale.openImmersionLowerShriek Ab.{u + 1} j).map
          ((α_ M.X (condensedRingObj Λ U) ((upperStar Λ j).obj N).X).hom ≫
            M.X ◁ γ[condensedRingObj Λ U,((upperStar Λ j).obj N).X]) ≫
          (openModuleBalanceTargetIso Λ j M N).hom =
        (openModuleBalanceSourceIso Λ j M N).hom ≫
          ((α_ ((openImmersionLowerShriek Λ j).obj M).X (condensedRingObj Λ Z) N.X).hom ≫
            ((openImmersionLowerShriek Λ j).obj M).X ◁ γ[condensedRingObj Λ Z,N.X]) ∧
      (ProEtale.openImmersionLowerShriek Ab.{u + 1} j).map
          (Mod.tensorObjπ M ((upperStar Λ j).obj N)) ≫
          (openModuleBalancedProjectionMap Λ j M N).hom =
        (openModuleBalanceTargetIso Λ j M N).hom ≫
          Mod.tensorObjπ ((openImmersionLowerShriek Λ j).obj M) N := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
