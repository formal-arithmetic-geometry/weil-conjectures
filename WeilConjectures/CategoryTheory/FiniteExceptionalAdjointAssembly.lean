/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Counit-normalized adjoint comparison

The elementary adjunction assembly in steps 2--3 of
`lem-sf-condensed-finite-exceptional-comparison`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u₁ u₂ v₁ v₂
open CategoryTheory
namespace CategoryTheory

/-- A left-adjoint comparison identifies right adjoints, uniquely by the counit,
and carries the actual unit to the actual unit.
Source: blueprint sk-thm-sf-package.proof.md, clause (1), adjoint uniqueness
(blueprint: lem-sf-finite-exceptional-adjoint-assembly).

Proof: conjugate the inverse left comparison. The conjugation counit identity and
naturality of the left comparison give the displayed counit equation. Transpose
this equation through the second adjunction to obtain uniqueness. The conjugation
unit identity, followed by the right functor of the forward left comparison,
gives the unit equation after cancelling the inverse comparison.
-/
theorem finiteExceptionalAdjointAssembly
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (χ : F ≅ F') :
    ∃ θ : G ≅ G',
      (∀ L, F.map (θ.hom.app L) ≫ χ.hom.app (G'.obj L) ≫ b.counit.app L =
        a.counit.app L) ∧
      (∀ t : G ≅ G',
        (∀ L, F.map (t.hom.app L) ≫ χ.hom.app (G'.obj L) ≫ b.counit.app L =
          a.counit.app L) → t = θ) ∧
      (∀ K, a.unit.app K ≫ θ.hom.app (F.obj K) ≫ G'.map (χ.hom.app K) =
        b.unit.app K) := by
  let θ := conjugateIsoEquiv a b χ.symm
  have hc (L : D) : F'.map (θ.hom.app L) ≫ b.counit.app L =
      χ.inv.app (G.obj L) ≫ a.counit.app L :=
    conjugateEquiv_counit a b χ.inv L
  refine ⟨θ, ?_, ?_, ?_⟩
  · intro L
    rw [χ.hom.naturality_assoc, hc, Iso.hom_inv_id_app_assoc]
  · intro t ht
    apply Iso.ext
    ext L
    apply (b.homEquiv (G.obj L) L).symm.injective
    change F'.map (t.hom.app L) ≫ b.counit.app L =
      F'.map (θ.hom.app L) ≫ b.counit.app L
    rw [hc]
    apply (cancel_epi (χ.hom.app (G.obj L))).mp
    rw [← χ.hom.naturality_assoc, ht, Iso.hom_inv_id_app_assoc]
  · intro K
    have hu := unit_conjugateEquiv a b χ.inv K
    change a.unit.app K ≫ θ.hom.app (F.obj K) =
      b.unit.app K ≫ G'.map (χ.inv.app K) at hu
    rw [← Category.assoc, hu]
    simp only [Category.assoc, ← G'.map_comp, Iso.inv_hom_id_app,
      G'.map_id]
    exact Category.comp_id (b.unit.app K)

end CategoryTheory
