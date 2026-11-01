/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelTateComparison
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1StrengthProjectionAction
import all WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1ShiftedTateSelfBraiding

import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Even shifted integral Tate self-symmetry -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
open DiagonalCoefficients RationalP1
set_option allowUnsafeReducibility true in
attribute [local reducible] traceTate

open Opposite

attribute [local implicit_reducible]
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Monoidal.induced
  Sheaf.monoidalCategory Sheaf.symmetricCategory Sheaf.braidedCategory

attribute [local instance 20000] Sheaf.monoidalCategory
  Sheaf.symmetricCategory Sheaf.braidedCategory
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal

private local instance internal_comm
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    @IsCommMonObj _ _ _ (inferInstance : SymmetricCategory
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})).toBraidedCategory
      (condensedRingObj Λ X) _ := by
  exact isCommMonObj_condensedRingObj Λ X

private local instance internal_braided
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    BraidedCategory (Modules Λ X) := by
  exact (Mod.braidedCategory
    (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (R := condensedRingObj Λ X))

private local instance internal_closed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    MonoidalClosed (Modules Λ X) := by
  exact (Mod.monoidalClosed
    (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (R := condensedRingObj Λ X))

private local instance internal_resolution
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution (Modules Λ X) := by
  exact (Mod.hasFunctorialFlatResolution
    (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (R := condensedRingObj Λ X))

set_option maxHeartbeats 800000 in
-- Elaborate the fixed native derived comparisons without unfolding their instances.
private theorem line_flat_and_braiding
    (l : ℕ) [Fact l.Prime] (E₀ : PadicAlgCl.FiniteIntermediateField l)
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] :
    ObjectProperty.flat (spIntegralTwist X l E₀) ∧
      (β_ (spIntegralTwist X l E₀) (spIntegralTwist X l E₀)).hom = 𝟙 _ := by
  classical
  let R := condensedRingObj (Profinite.padicIntegersRingObj l E₀.val) X
  let : MonObj R := inferInstanceAs (MonObj (condensedRingObj (Profinite.padicIntegersRingObj l
    E₀.val) X))
  let : IsCommMonObj R :=
    isCommMonObj_condensedRingObj (Profinite.padicIntegersRingObj l E₀.val) X
  let E := InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology X) R
  let M := E.functor.obj (spIntegralTwist X l E₀)
  have hM : M.IsFiniteLocallyFreeOfRank 1 := by
    dsimp only [M, E, R]
    convert! (transparency := .all) (spTwists_locallyFree X l E₀).1 using 1
  let := hM
  constructor
  · apply (InternalAbelianSheafModule.flat_iff_sectionModule
      (Scheme.ProEt.topology X) R (spIntegralTwist X l E₀)).2
    change SheafOfModules.IsFlatOnSite M
    simpa only [SheafOfModules.IsFlatOnSite, exactFunctor_iff,
      WeilConjectures.coefficientTwistLine,
      WeilConjectures.coefficientTwistPower,
      SheafOfModules.scalarTensorPower] using
      (WeilConjectures.coefficientTwistLine_exact X M 1).2
  · obtain ⟨_, e, _, _, _, _, _, _, _, hb, _⟩ :=
      InternalAbelianSheafModule.internal_section_tensor_comparison
        (Scheme.ProEt.topology X) R
    apply E.functor.map_injective
    apply (cancel_mono (e (spIntegralTwist X l E₀) (spIntegralTwist X l E₀)).hom).1
    have hb' : E.functor.map (β_ (spIntegralTwist X l E₀) (spIntegralTwist X l E₀)).hom ≫
        (e (spIntegralTwist X l E₀) (spIntegralTwist X l E₀)).hom =
        (e (spIntegralTwist X l E₀) (spIntegralTwist X l E₀)).hom ≫ (β_ M M).hom := by
      convert! (transparency := .all) (hb (spIntegralTwist X l E₀) (spIntegralTwist X l E₀)).symm
        using 1
    refine hb'.trans ?_
    rw [section_line_self_braiding X _ M]
    exact (Category.comp_id _).trans
      ((congrArg (fun k ↦ k ≫ (e (spIntegralTwist X l E₀) (spIntegralTwist X l E₀)).hom)
        (E.functor.map_id (spIntegralTwist X l E₀ ⊗ spIntegralTwist X l E₀))).trans
          (Category.id_comp _)).symm

set_option maxHeartbeats 800000 in
-- Elaborate the fixed native derived comparisons without unfolding their instances.
/-- The integral positive Tate line shifted by two has identity self-braiding.
Source: the integral projective-line triangle calculation, second identity.
(blueprint: lem-integral-kernel-second-tate-symmetry).
Proof: on a local rank-one frame the tensor flip is the identity, since the
coefficient ring is commutative. The section-module equivalence transfers this
equality and flatness to internal modules. The native derived tensor comparison
then transfers the equality to the single complex shifted by two. Its Koszul sign
is (-1)^(2*2)=1, as expressed by evenShiftCanonicalSelfSymmetry. -/
theorem integralKernel_second_tate_symmetry
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] :
    (tensorBraiding (Profinite.padicIntegersRingObj l E.val) X
      (traceTate l E X) (traceTate l E X)).hom =
        𝟙 (traceTate l E X ⊗ traceTate l E X) := by
  obtain ⟨hf, hb⟩ := line_flat_and_braiding l E X
  unfold tensorBraiding internalMonoidal internalTensorBundle nativeTensorBundle
  exact Etale.CoordinateTrace.evenShiftCanonicalSelfSymmetry (spIntegralTwist X l E) hf hb 1

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
