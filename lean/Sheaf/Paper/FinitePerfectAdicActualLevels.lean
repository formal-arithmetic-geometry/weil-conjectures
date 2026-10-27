/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E7
-/
module

public import Sheaf.Paper.FinitePerfectAdicConstantNormalization
public import Sheaf.Paper.FinitePerfectAdicStalkModels

/-! # Levelwise actual finite quotient data

Source: Stacks Project, Tags 09AL and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The levelwise part of the actual quotient normalization package.
Source: Stacks Tags 09AL and 09C6, finite quotient descent and balancing.
(blueprint: lem-weil-pbc-finite-perfect-adic-actual-levels). -/
structure FinitePerfectAdicActualLevelData
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d) where
  K : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology
    (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))))
  boundedK : ∀ n : ℕ, ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) i).obj (K n))
  lisseK : ∀ (n : ℕ) (i : ℤ), IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) i).obj (K n))
  stalk : ∀ (n : ℕ) (Ω : Type t) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ V.left), Nonempty
      ((pointSmallEtale x).sheafFiber.obj
        (derivedLocalIsomorphismSheaf (finitePerfectAdicEtaleConstant V.left T n) (K n)))
  dK : ∀ n : ℕ, K (n + 1) ⟶
    (normalizationRestrict V.left.smallEtaleTopology
      (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj (K n)
  universalK : ∀ n : ℕ, EtaleUniversalNormalization V.left
    (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) (dK n)

/-- Separate finite quotient descent supplies the levelwise actual data.
The finite-ring constructible comparison gives the descended complexes, their bounded
finite locally constant cohomology, the descended consecutive arrows and their universal
normalization property; geometric stalks are obtained from the supplied markings.
Source: Stacks Tags 09AL and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-actual-levels). -/
theorem finitePerfectAdic_actual_levels
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d)
    (hperfect : ∀ n : ℕ, DerivedCategory.IsPerfect (T.level n))
    (hmark : FinitePerfectAdicLevelMarkings X d φ M V T) :
    Nonempty (FinitePerfectAdicActualLevelData X d M V T) := by sorry

end AlgebraicGeometry.Scheme
