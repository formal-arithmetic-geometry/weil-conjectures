/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines

/-! # Uniqueness of normalized monoidal extension of scalars

Source: the canonical source identification in det-sp-purity-coefficient-change.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe v₁ v₂ u₁ u₂ u
open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace CategoryTheory

/-- The cotensorator determines a strong monoidal structure.
Source: balanced tensor normalization of the coefficient source identification
(blueprint: lem-pur-coefficient-monoidal-normalization).
Proof: the left unit law and cancellation of the invertible cotensorator identify
the two counits after tensoring with F(1). This object is isomorphic to 1. Tensor
exchange followed by the second counit and the right unitor therefore cancels this
tensor factor and identifies the counits themselves. The oplax structures agree,
and their inverses determine the lax structures. -/
theorem monoidal_eq_of_cotensorator
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (m n : F.Monoidal)
    (hδ : ∀ X Y, m.toOplaxMonoidal.δ X Y = n.toOplaxMonoidal.δ X Y) : m = n := by
  let := m
  have ht : m.toOplaxMonoidal.η ▷ F.obj (𝟙_ C) =
      n.toOplaxMonoidal.η ▷ F.obj (𝟙_ C) := by
    apply (cancel_epi
      (F.map (λ_ (𝟙_ C)).inv ≫ m.toOplaxMonoidal.δ (𝟙_ C) (𝟙_ C))).1
    simpa only [Category.assoc, hδ] using
      (m.toOplaxMonoidal.oplax_left_unitality (𝟙_ C)).symm.trans
        (n.toOplaxMonoidal.oplax_left_unitality (𝟙_ C))
  let := n
  have hz := congrArg (fun f ↦ f ≫ (𝟙_ D) ◁ n.toOplaxMonoidal.η) ht
  rw [← whisker_exchange, ← whisker_exchange] at hz
  have hr := (cancel_epi (F.obj (𝟙_ C) ◁ n.toOplaxMonoidal.η)).1 hz
  have hu := congrArg (fun f ↦ f ≫ (ρ_ (𝟙_ D)).hom) hr
  rw [rightUnitor_naturality, rightUnitor_naturality] at hu
  have hη := (cancel_epi (ρ_ (F.obj (𝟙_ C))).hom).1 hu
  apply Functor.Monoidal.toOplaxMonoidal_injective F
  apply Functor.OplaxMonoidal.ext
  · exact hη
  · exact funext fun X ↦ funext fun Y ↦ hδ X Y

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- Scalar-unit normalization determines the strong monoidal scalar structure.
Source: the balanced tensor source identification in coefficient change
(blueprint: lem-pur-coefficient-monoidal-normalization).
Proof: apply the scalar adjunction's injective Hom equivalence and precompose with
the epimorphic balanced tensor projection. Both cotensorators become the same
specified arrow on pure tensors. The preceding monoidal uniqueness theorem finishes. -/
theorem scalarMonoidal_unique (ell : ℕ) [Fact ell.Prime]
    {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (X : Scheme.{u})
    (m n : (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X)).Monoidal)
    (hm : ∀ M N, Mod.tensorObjπ M N ≫
      (Mod.extendUnit (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X) (M ⊗ N)).hom ≫
        (m.toOplaxMonoidal.δ M N).hom =
      ((Mod.extendUnit (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X) M).hom ⊗ₘ
        (Mod.extendUnit (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X) N).hom) ≫
        Mod.tensorObjπ
          ((Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
            a.hom.hom X)).obj M)
          ((Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
            a.hom.hom X)).obj N))
    (hn : ∀ M N, Mod.tensorObjπ M N ≫
      (Mod.extendUnit (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X) (M ⊗ N)).hom ≫
        (n.toOplaxMonoidal.δ M N).hom =
      ((Mod.extendUnit (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X) M).hom ⊗ₘ
        (Mod.extendUnit (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X) N).hom) ≫
        Mod.tensorObjπ
          ((Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
            a.hom.hom X)).obj M)
          ((Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
            a.hom.hom X)).obj N)) : m = n := by
  apply monoidal_eq_of_cotensorator
  intro M N
  apply (Mod.extendHomEquiv (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X) (M ⊗ N) _).injective
  apply Mod.hom_ext
  apply (cancel_epi (Mod.tensorObjπ M N)).1
  exact (hm M N).trans (hn M N).symm

private theorem line_eq_rec (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    (X : Scheme.{u}) (d : ℕ) :
    c.line ell X d = Nat.rec (𝟙_ _) (fun _ N ↦ N ⊗ c.firstLine ell X) d := by
  induction d with
  | zero => rfl
  | succ d ih => exact congrArg (fun N ↦ N ⊗ c.firstLine ell X) ih

private theorem mapIso_eqToIso {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D) {X Y : C} (h : X = Y) :
    F.mapIso (eqToIso h) = eqToIso (congrArg F.obj h) := by
  cases h
  apply Iso.ext
  exact F.map_id X

private theorem iso_transport_heq {C : Type u₁} [Category.{v₁} C]
    {X X' Y Y' : C} (hX : X = X') (hY : Y = Y') (e : X' ≅ Y') :
    HEq (eqToIso hX ≪≫ e ≪≫ eqToIso hY.symm) e := by
  cases hX
  cases hY
  simp

end AlgebraicGeometry.ProEtale.PurityTransport
