/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.AffinePerfectMapLift
import WeilConjectures.AlgebraicGeometry.AffinePerfectPlusShift
import WeilConjectures.AlgebraicGeometry.AffineSupportIteratedCones
import WeilConjectures.AlgebraicGeometry.AffineSupportPoweredGenerators
import WeilConjectures.AlgebraicGeometry.AffineBinomialProjectorCone
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.PerfectTwoOutOfThree
import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated

/-! # Affine perfect support extension

Source: Stacks Project, Derived Categories of Schemes, Tag 08EK (Lemma 36.13.10)
(blueprint: lem-sc-affine-perfect-support-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem exists_scalar_cone_chain (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (s : ℕ)
    (g : Fin s → RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (E : schemeDerivedCategory X) :
    ∃ C : Fin (s + 1) → schemeDerivedCategory X, C 0 = E ∧
      ∃ (b : ∀ i : Fin s, C i.castSucc ⟶ C i.succ)
        (d : ∀ i : Fin s, C i.succ ⟶ (C i.castSucc)⟦(1 : ℤ)⟧),
        ∀ i : Fin s,
          CategoryTheory.Pretriangulated.Triangle.mk
            (schemeDerivedScalar X (g i) (𝟙 (C i.castSucc))) (b i) (d i) ∈
              CategoryTheory.Pretriangulated.distinguishedTriangles
                (C := schemeDerivedCategory X) := by
  classical
  let gN : ℕ → RingCat.sectionsSubring
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}) :=
    fun n ↦ if hn : n < s then g ⟨n, hn⟩ else 0
  have h (n : ℕ) (K : schemeDerivedCategory X) :=
    CategoryTheory.Pretriangulated.distinguished_cocone_triangle
      (schemeDerivedScalar X (gN n) (𝟙 K))
  choose Z b d hZ using h
  let Cn : ℕ → schemeDerivedCategory X :=
    Nat.rec E (fun n K ↦ Z n K)
  refine ⟨fun i ↦ Cn i.val, rfl,
    (fun i ↦ b i.val (Cn i.val)), (fun i ↦ d i.val (Cn i.val)), ?_⟩
  intro i
  simpa [gN, i.isLt, Fin.castSucc] using hZ i.val (Cn i.val)

end AlgebraicGeometry.Scheme
