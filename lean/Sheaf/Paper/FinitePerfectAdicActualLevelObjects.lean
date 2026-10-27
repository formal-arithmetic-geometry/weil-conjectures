/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FinitePerfectAdicConstantNormalization
public import Sheaf.Paper.FinitePerfectAdicStalkModels
import Sheaf.Paper.FinitePerfectAdicMarkedOrigin

/-! # Finite-level descended objects and their cohomology

Source: Stacks Project, Tags 09AL and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-actual-level-objects).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Finite quotient descent produces the etale complexes and their bounded lisse
cohomology.  The construction descends the marked pro-etale complexes through the
finite-coefficient comparison, level by level; boundedness and finite local constancy
are transported across the comparison.  This is the object and cohomology part of
Tags 09AL and 09C6, before stalk sections or transition arrows are chosen.
(blueprint: lem-weil-pbc-finite-perfect-adic-actual-level-objects). -/
theorem finitePerfectAdic_actual_level_objects
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d)
    (hperfect : ∀ n : ℕ, DerivedCategory.IsPerfect (T.level n))
    (hmark : FinitePerfectAdicLevelMarkings X d φ M V T) :
    ∃ K : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))),
      (∀ n : ℕ, ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero
        ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
          (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) i).obj (K n))) ∧
      (∀ (n : ℕ) (i : ℤ), IsFiniteLocallyConstantSheaf
        ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
          (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) i).obj (K n))) := by
  classical
  have _hcompat := hcompat
  choose K hb hl _ _ using fun n ↦
    finitePerfectAdic_marked_origin X d φ hφ M V T hmark n (hperfect n)
  exact ⟨K, hb, hl⟩

end AlgebraicGeometry.Scheme
