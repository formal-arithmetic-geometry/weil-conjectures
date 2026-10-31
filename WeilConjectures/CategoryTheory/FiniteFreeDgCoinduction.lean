/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SheafDgHomotopySystem
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-! # Finite free sheaf dg coinduction

Source: Stacks Project, `sdga.tex`, Tags 0FRS, 0FTN and 0FTQ, and the finite-basis
evaluation calculation (blueprint: lem-sf-finite-free-dg-coinduction).

The model below specifies the ordinary internal Hom by its representing evaluation,
in the existing category of unbounded complexes. This avoids a second Hom construction
or a restriction on site universes: the signed tensor represents exactly the product
Hom with differential `d(f) = d_M f - (-1)^degree(f) f d_A`. The equations fix the
right action, both ordinary adjunction maps, and their localized counterparts.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}}

set_option maxHeartbeats 800000 in
-- Tensor coherence equations require a larger elaboration budget.
/-- Ordinary tensor, coinduction, and the tensor-dual evaluation comparison.
The evaluation universal property determines the full internal Hom object, including
its differential, uniquely up to the evaluation-preserving isomorphism. The action
equation is `(f a)(b) = f(ab)`, with no braiding and hence no extra sign.
The dual is coinduction of the tensor unit; its action is consequently the same action.
No object is selected from a mere existence assertion.

Source: Stacks 0FRS and the bounded finite-free evaluation calculation
(blueprint: lem-sf-finite-free-dg-coinduction). -/
structure OrdinaryFiniteFreeCoinduction (A : Algebra O) where
  extension : Complex O ⥤ Module A
  extensionIso : extension ⋙ underlying A ≅ tensorRight A.X
  extension_action (M : Complex O) :
    action (extension.obj M) ≫ (extensionIso.hom.app M) =
      (extensionIso.hom.app M ▷ A.X) ≫ (α_ M A.X A.X).hom ≫
        (M ◁ (MonObj.mul : A.X ⊗ A.X ⟶ A.X))
  leftAdjunction : extension ⊣ underlying A
  unit (M : Complex O) :
    leftAdjunction.unit.app M ≫ extensionIso.hom.app M =
      (ρ_ M).inv ≫ (M ◁ (MonObj.one : 𝟙_ (Complex O) ⟶ A.X))
  coinduction : Complex O ⥤ Module A
  evaluation (M : Complex O) : (underlying A).obj (coinduction.obj M) ⊗ A.X ⟶ M
  hom_universal (M L : Complex O) : Function.Bijective
    (fun f : L ⟶ (underlying A).obj (coinduction.obj M) ↦
      (f ▷ A.X) ≫ evaluation M)
  evaluation_natural {M N : Complex O} (f : M ⟶ N) :
    ((underlying A).map (coinduction.map f) ▷ A.X) ≫ evaluation N = evaluation M ≫ f
  hom_action (M : Complex O) :
    (action (coinduction.obj M) ▷ A.X) ≫ evaluation M =
      (α_ ((underlying A).obj (coinduction.obj M)) A.X A.X).hom ≫
        (((underlying A).obj (coinduction.obj M)) ◁
          (MonObj.mul : A.X ⊗ A.X ⟶ A.X)) ≫ evaluation M
  rightAdjunction : underlying A ⊣ coinduction
  counit (M : Complex O) :
    rightAdjunction.counit.app M =
      (ρ_ ((underlying A).obj (coinduction.obj M))).inv ≫
        (((underlying A).obj (coinduction.obj M)) ◁
          (MonObj.one : 𝟙_ (Complex O) ⟶ A.X)) ≫ evaluation M
  tensorDual : Complex O ⥤ Module A
  tensorDualIso : tensorDual ⋙ underlying A ≅
    tensorRight ((underlying A).obj (coinduction.obj (𝟙_ (Complex O))))
  tensorDual_action (M : Complex O) :
    action (tensorDual.obj M) ≫ tensorDualIso.hom.app M =
      (tensorDualIso.hom.app M ▷ A.X) ≫
        (α_ M ((underlying A).obj (coinduction.obj (𝟙_ (Complex O)))) A.X).hom ≫
        (M ◁ action (coinduction.obj (𝟙_ (Complex O))))
  comparison : tensorDual ≅ coinduction
  comparison_evaluation (M : Complex O) :
    ((underlying A).map (comparison.hom.app M) ▷ A.X) ≫ evaluation M =
      (tensorDualIso.hom.app M ▷ A.X) ≫
        (α_ M ((underlying A).obj (coinduction.obj (𝟙_ (Complex O)))) A.X).hom ≫
        (M ◁ evaluation (𝟙_ (Complex O))) ≫ (ρ_ M).hom

variable [HasDerivedCategory.{w} (Coeff O)]

set_option maxHeartbeats 800000 in
-- Elaborate the localization factorization equations with the same budget.
/-- The ordinary constructions and their localized adjunctions, on the fixed dg
localization and Mathlib's ordinary derived category. The factorization isomorphisms
are natural on all complexes and chain maps. The unit, counit and comparison equations
fix the localized ordinary maps; an arbitrary abstract adjoint does not suffice.

Source: Stacks 0FTN and 0FTQ, specialized to the regular bimodule in both orientations
(blueprint: lem-sf-finite-free-dg-coinduction). -/
structure FiniteFreeCoinductionSystem (A : Algebra O) where
  ordinary : OrdinaryFiniteFreeCoinduction A
  [derivedStructure : DerivedStructure A]
  forget : Derived A ⥤ DerivedCategory (Coeff O)
  forgetIso : Q A ⋙ forget ≅ underlying A ⋙ DerivedCategory.Q
  [forgetShift : forget.CommShift ℤ]
  forgetExact : forget.IsTriangulated
  extension : DerivedCategory (Coeff O) ⥤ Derived A
  extensionIso : DerivedCategory.Q ⋙ extension ≅ ordinary.extension ⋙ Q A
  coinduction : DerivedCategory (Coeff O) ⥤ Derived A
  coinductionIso : DerivedCategory.Q ⋙ coinduction ≅ ordinary.coinduction ⋙ Q A
  leftAdjunction : extension ⊣ forget
  rightAdjunction : forget ⊣ coinduction
  unit (M : Complex O) :
    leftAdjunction.unit.app (DerivedCategory.Q.obj M) ≫
        forget.map (extensionIso.hom.app M) ≫
        forgetIso.hom.app (ordinary.extension.obj M) =
      DerivedCategory.Q.map (ordinary.leftAdjunction.unit.app M)
  counit (M : Complex O) :
    rightAdjunction.counit.app (DerivedCategory.Q.obj M) =
      forget.map (coinductionIso.hom.app M) ≫
        forgetIso.hom.app (ordinary.coinduction.obj M) ≫
        DerivedCategory.Q.map (ordinary.rightAdjunction.counit.app M)
  tensorDual : DerivedCategory (Coeff O) ⥤ Derived A
  tensorDualIso : DerivedCategory.Q ⋙ tensorDual ≅ ordinary.tensorDual ⋙ Q A
  comparison : tensorDual ≅ coinduction
  comparison_eq (M : Complex O) :
    comparison.hom.app (DerivedCategory.Q.obj M) =
      tensorDualIso.hom.app M ≫ (Q A).map (ordinary.comparison.hom.app M) ≫
        coinductionIso.inv.app M

/-- Finite free sheaf dg coinduction, with the actual evaluation counit and
tensor-dual comparison, for arbitrary unbounded input complexes.

The support bounds constrain only `A.X`. The term condition says that each term is
a finite direct sum of the rank-one coefficient module, allowing rank zero.
The existing monoid and right-module objects encode associative unital multiplication,
central coefficients, the signed Leibniz differential and the right-module convention.
The universal evaluation in `OrdinaryFiniteFreeCoinduction` is ordinary internal Hom:
on homogeneous sections it is `f ⊗ a ↦ f(a)`. Its action equation gives `(f a)(b)=f(ab)`.
The comparison equation therefore says `(m ⊗ λ)(a)=λ(a)m`; the tensor unit is concentrated
in degree zero, so evaluation vanishes unless `degree(λ)+degree(a)=0`.

Source: Stacks `sdga.tex`, Tags 0FRS, 0FTN, 0FTQ and finite-basis evaluation
(blueprint: lem-sf-finite-free-dg-coinduction).

Proof plan:
1. Use lem-sfb-sheaf-dg-homotopy-system and its underlying ringed-site module
construction for right dg modules, signed tensor, cones and the unbounded localization.
2. The bounded finite-free underlying complex is K-flat by
lem-sfb-bounded-above-flat-kflat. Thus ordinary tensor with A preserves quasi-isomorphisms.
3. Construct the ordinary free right module and internal Hom; check the signed
differentials and the action `(f a)(b)=f(ab)` on local sections. Ordinary adjunction
has unit inserting 1 and coinduction counit evaluation at 1 (Stacks 0FRS).
4. lem-sf-finite-free-dg-coordinate-evaluation identifies tensor with the dual with
internal Hom. The finite homogeneous-basis expansion is valid for unbounded M,
is right A-linear, and proves that coinduction preserves quasi-isomorphisms.
5. Apply lem-sf-dg-derived-tensor-hom-adjunction with the regular (R,A)-bimodule
and the regular (A,R)-bimodule. Identify Hom_A(A,-) with forgetting by evaluation
at 1, and - tensor_A A with forgetting by action. Localize the ordinary adjunctions
and the natural tensor-dual isomorphism. Their factorization diagrams give precisely
the stated unit, counit and comparison equations; forgetting preserves shifts and cones.
-/
theorem finite_free_dg_coinduction (A : Algebra O)
    (bounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (A.X.X n))
    (finiteFree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (A.X.X n ≅ ∐ (fun _ : Fin r ↦ 𝟙_ (Coeff O)))) :
    Nonempty (FiniteFreeCoinductionSystem A) := by
  sorry

end CategoryTheory.RingedSiteDg
