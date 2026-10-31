/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantNormalization
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicStalkModels

/-! # Geometric stalk sections for descended finite levels

Source: Stacks Project, Tags 09AL and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-actual-level-stalk).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The level markings provide a local isomorphism section at every geometric point.
After the descended object is fixed, restrict a marking to the point and pass through
the sheafification unit of the derived Isom presheaf.  This is independent for each
level and requires no common covering.  Source: Tags 09AL and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-actual-level-stalk). -/
theorem finitePerfectAdic_actual_level_stalk
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d)
    (hmark : FinitePerfectAdicLevelMarkings X d φ M V T)
    (K : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))))) :
    ∀ (n : ℕ) (Ω : Type t) [Field Ω] [IsSepClosed Ω]
      (x : Spec (.of Ω) ⟶ V.left), Nonempty
        ((pointSmallEtale x).sheafFiber.obj
          (derivedLocalIsomorphismSheaf (finitePerfectAdicEtaleConstant V.left T n) (K n))) := by
  sorry

end AlgebraicGeometry.Scheme
