/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact

/-! # Evaluation for a finite projective sheaf of modules

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ, proof of
`lemma-dual-perfect-complex`, finite-free and direct-summand calculation.
(blueprint: lem-pc-finite-projective-internal-hom-evaluation).
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SheafOfModules

attribute [local instance] monoidalCategory symmetricCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- The canonical map sending `b tensor phi` to `e ↦ b * phi(e)`.
Source: Stacks Project, Tag 08DQ, proof of `lemma-dual-perfect-complex`.
(blueprint: lem-pc-finite-projective-internal-hom-evaluation). -/
def moduleDualEvaluation (R : Sheaf J CommRingCat.{u})
    (E B : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    B ⊗ homObj E (𝟙_ _) ⟶ homObj E B :=
  tensorHomEquiv E _ B
    ((β_ E (B ⊗ homObj E (𝟙_ _))).hom ≫
      (α_ B (homObj E (𝟙_ _)) E).hom ≫
      B ◁ ((β_ (homObj E (𝟙_ _)) E).hom ≫
        (tensorHomEquiv E (homObj E (𝟙_ _)) (𝟙_ _)).symm (𝟙 _)) ≫
      (ρ_ B).hom)

/-- Canonical tensor-dual evaluation is invertible for a retract of a finite free sheaf.
Source: Stacks Project, Tag 08DQ, proof of `lemma-dual-perfect-complex`.
(blueprint: lem-pc-finite-projective-internal-hom-evaluation).

Proof: for the free sheaf on `Fin m`, internal Hom is the finite product of `m`
copies of the target, and the dual is the free sheaf on the same basis. Tensoring
with that free sheaf is the finite coproduct of `m` copies of B. The finite
product/coproduct identification sends the evaluation map to the identity on
these copies: its j-th coordinate evaluates the j-th basis vector. For the
retraction `i ≫ p = id`, precomposition induces retractions on both the dual
and Hom. Naturality of evaluation gives a morphism of the resulting split
idempotents. Its inverse for the free sheaf commutes with these idempotents,
so restrict it by the inclusion and projection to obtain the inverse for E.
The two inverse equations reduce to the free inverse equations and `i ≫ p = id`.
For `m = 0` both free objects are zero; the same retraction argument applies.
-/
theorem isIso_moduleDualEvaluation_of_retract (R : Sheaf J CommRingCat.{u})
    (E B : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hE : ∃ m : ℕ,
      ∃ (i : E ⟶ free (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
          (ULift.{u} (Fin m)))
        (p : free (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
          (ULift.{u} (Fin m)) ⟶ E), i ≫ p = 𝟙 E) :
    IsIso (moduleDualEvaluation R E B) := by sorry

end SheafOfModules
