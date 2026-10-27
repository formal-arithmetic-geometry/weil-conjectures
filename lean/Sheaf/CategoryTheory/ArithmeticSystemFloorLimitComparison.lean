/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import Sheaf.CategoryTheory.ArithmeticSystemRightAdjointData

/-! # Common-coefficient comparison for arithmetic floor extension

Source: Stacks Tags 0940, 0941 and 0H9K and the arithmetic-restriction paragraph of
integral-adjunction normalization (blueprint: lem-sp-arithmetic-system-floor-limit).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048

universe u v w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C]

/-- Forgetting scalars identifies selected floor-extension levels with the original
tower, and the resulting total derived limits have the normalized comparison.

Source: the arithmetic restriction paragraph of integral-adjunction normalization;
Stacks Tags 0940, 0941 and 0H9K
(blueprint: lem-sp-arithmetic-system-floor-limit).

Proof: on a strict B-system M, restrict M_n along α_n to A at every level.
The naturality square of α makes every original transition A-linear. The original
identity, composition, and morphism squares give the tower functor F, with the
specified component and section formulas. Construct G in the same way using β.
Both functors are additive and exact, since restriction of scalars is exact and
kernels and cokernels of towers and strict systems are computed componentwise.
At the selected level e(n+1)-1=r n, d.selected identifies the underlying module
of R N with N_n, while hβ identifies the two scalar actions. These actual
identifications form a natural isomorphism (R ⋙ F) ⋙ restriction e ≅ G:
its components are the identity on the original sections and its transition
squares follow from the original selected transitions. This proves selection_sections.
Apply the constant-coefficient arithmetic-restriction comparison to the underlying
A-tower, using the coefficient-universe small-site model when necessary. Whisker
its derived isomorphism by (R ⋙ F).mapDerivedCategory and compose with the exact
functor compositor and the localization of selection. This gives comparison.
The ordinary-limit normalization of arithmetic restriction, followed by naturality
of η for the complex map induced by selection, gives precisely normalization;
the exact-functor comparison factors cancel in that equation. Thus no countable
product exactness or restriction on the derived universe is introduced. At e=1
this specializes to the identity restriction comparison; zero prefix components
for e>1 do not occur in selected levels and add no assumptions.
-/
theorem arithmeticSystemFloorLimitComparison
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (e : ℕ) (he : 1 ≤ e)
    (r : ℕ ↪o ℕ) (hr : ∀ n : ℕ, r n = e * (n + 1) - 1)
    (hf : ∀ k : ℕ, e ≤ k + 1 → r ((k + 1) / e - 1) ≤ k)
    (R : StrictRingSystem (selectedSystemRings B r) ⥤ StrictRingSystem B)
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (d : ArithmeticSystemOrdinaryFloorData B e r hf R)
    (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    (β : (Functor.const ℕᵒᵖ).obj A ⟶ selectedSystemRings B r)
    (hβ : ∀ n : ℕ, β.app (op n) = α.app (op (r n)))
    [HasDerivedCategory.{z} (SheafOfModules.{w}
      (derivedChangeRingIndependentCoefficients J A))]
    [HasDerivedCategory.{z} (ℕᵒᵖ ⥤ SheafOfModules.{w}
      (derivedChangeRingIndependentCoefficients J A))]
    (RF : DerivedCategory.{z} (ℕᵒᵖ ⥤ SheafOfModules.{w}
      (derivedChangeRingIndependentCoefficients J A)) ⥤
      DerivedCategory.{z} (SheafOfModules.{w}
        (derivedChangeRingIndependentCoefficients J A)))
    (η : CategoryTheory.StrictTowerArithmetic.limitComplex _ ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ SheafOfModules.{w}
        (derivedChangeRingIndependentCoefficients J A)) (.up ℤ)))
    (hη : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I)) :
    ∃ (F : ArithmeticSystemScalarForgetting B A α)
      (G : ArithmeticSystemScalarForgetting (selectedSystemRings B r) A β),
      Nonempty (ArithmeticSystemLimitData B e r R A α β F G RF η) := by sorry

end SheafOfModules
