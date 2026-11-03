/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Balanced scalar coordinates on native Tate powers

Source: the pullback/Tate comparison of sk-lem-sp-field-extension,
using the balanced tensor construction of sk-def-sp-tate-twist.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.PurityTransport
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace CategoryTheory
private theorem monoidal_eq_of_delta
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (m n : F.Monoidal)
    (hd : ∀ X Y, m.toOplaxMonoidal.δ X Y = n.toOplaxMonoidal.δ X Y) : m = n := by
  let := m
  have hu : m.toOplaxMonoidal.η = n.toOplaxMonoidal.η := by
    apply Functor.eq_of_leftUnitality (m.toOplaxMonoidal.δ (𝟙_ C) (𝟙_ C))
    · exact Functor.OplaxMonoidal.left_unitality_hom F (𝟙_ C)
    · rw [hd]
      exact @Functor.OplaxMonoidal.left_unitality_hom _ _ _ _ _ _ F
        n.toOplaxMonoidal (𝟙_ C)
  have hμ (X Y : C) : m.toLaxMonoidal.μ X Y = n.toLaxMonoidal.μ X Y := by
    apply (cancel_mono (m.toOplaxMonoidal.δ X Y)).1
    rw [Functor.Monoidal.μ_δ, hd]
    exact (@Functor.Monoidal.μ_δ _ _ _ _ _ _ F n X Y).symm
  have hε : m.toLaxMonoidal.ε = n.toLaxMonoidal.ε := by
    apply (cancel_mono m.toOplaxMonoidal.η).1
    rw [Functor.Monoidal.ε_η, hu]
    exact (@Functor.Monoidal.ε_η _ _ _ _ _ _ F n).symm
  apply Functor.Monoidal.ext
  · exact hε
  · exact funext fun X ↦ funext fun Y ↦ hμ X Y
  · exact hu
  · exact funext fun X ↦ funext fun Y ↦ hd X Y
end CategoryTheory
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]
/-- Native Tate scalar coordinates exist for every map respecting Z_ell.
Source: sk-lem-sp-field-extension, native source comparison
(blueprint: lem-pur-native-scalar-line-coordinates).

Proof. Take the scalar-unit-normalized strong monoidal structure on extension
of scalars. Any two such structures have the same cotensorator: precompose with
the scalar adjunction unit and the balanced tensor epimorphism. The strong
monoidal unit laws then identify the counits, and uniqueness of inverses
identifies the lax maps, so the structures coincide. Extend the first Tate line
by scalar associativity. Recursively extend each tensor power using this
monoidal structure; power zero is its scalar unitor. Uniqueness proves the
required power equation for every scalar-unit-normalized monoidal structure. -/
theorem scalarLineCoordinates_nonempty {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell) (X : Scheme.{u}) :
    Nonempty (ScalarLineCoordinates ell a ha X) := by
  let φ := coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X
  obtain ⟨m, hm⟩ := Mod.exists_extendScalarsMonoidal φ
  have unique (n : (Mod.extendScalars φ).Monoidal)
      (hn : ∀ M N, Mod.tensorObjπ M N ≫ (Mod.extendUnit φ (M ⊗ N)).hom ≫
        (n.toOplaxMonoidal.δ M N).hom =
          ((Mod.extendUnit φ M).hom ⊗ₘ (Mod.extendUnit φ N).hom) ≫
            Mod.tensorObjπ ((Mod.extendScalars φ).obj M) ((Mod.extendScalars φ).obj N)) :
      n = m := by
    apply monoidal_eq_of_delta
    intro M N
    apply (Mod.extendHomEquiv φ (M ⊗ N) _).injective
    apply Mod.hom_ext
    apply (cancel_epi (Mod.tensorObjπ M N)).mp
    exact (hn M N).trans (hm M N).symm
  let := m
  let first := scalarFirst ell a ha X
  have line_eq (b : Coefficient ell) (d : ℕ) :
      b.line ell X d = Nat.rec (𝟙_ _) (fun _ N ↦ N ⊗ b.firstLine ell X) d := by
    induction d with
    | zero => rfl
    | succ d ih => exact congrArg (fun N ↦ N ⊗ b.firstLine ell X) ih
  have powers (d : ℕ) : ∃ p : (Mod.extendScalars φ).obj (c.line ell X d) ≅ c'.line ell X d,
      HEq p (powerPull (Mod.extendScalars φ) (c.firstLine ell X)
        (c'.firstLine ell X) first d) := by
    rw [line_eq c d, line_eq c' d]
    exact ⟨_, HEq.rfl⟩
  choose power hp using powers
  refine ⟨{ first := first
            first_normalized := HEq.rfl
            power := power
            power_normalized := ?_ }⟩
  intro n hn d
  have hnm := unique n hn
  subst n
  exact hp d
end AlgebraicGeometry.ProEtale.PurityTransport
