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
/-- Normalized scalar Tate-line coordinates exist for each compatible ring map.
Source: the canonical scalar source identification in coefficient change
(blueprint: lem-pur-coefficient-monoidal-normalization).
Proof: use the proved normalized strong monoidal scalar structure. Take the first
line to be scalarFirst, and all powers to be its monoidal tensor powers. Any other
normalized strong monoidal structure equals the chosen one by scalarMonoidal_unique,
so all required normalization equations hold. -/
theorem scalarLineCoordinates_nonempty (ell : ℕ) [Fact ell.Prime]
    {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell) (X : Scheme.{u}) :
    Nonempty (ScalarLineCoordinates ell a ha X) := by
  obtain ⟨m, hm⟩ := Mod.exists_extendScalarsMonoidal
    (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X)
  let := m
  refine ⟨{ first := scalarFirst ell a ha X
            first_normalized := HEq.rfl
            power := fun d ↦
              (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
                a.hom.hom X)).mapIso (eqToIso (line_eq_rec ell c X d)) ≪≫
              powerPull (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
                a.hom.hom X)) (c.firstLine ell X) (c'.firstLine ell X)
                (scalarFirst ell a ha X) d ≪≫ eqToIso (line_eq_rec ell c' X d).symm
            power_normalized := ?_ }⟩
  intro n hn d
  have h := scalarMonoidal_unique ell a X n m hn hm
  subst n
  rw [mapIso_eqToIso]
  exact iso_transport_heq
    (congrArg (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X)).obj (line_eq_rec ell c X d))
    (line_eq_rec ell c' X d)
    (powerPull (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
      a.hom.hom X)) (c.firstLine ell X) (c'.firstLine ell X) (scalarFirst ell a ha X) d)

end AlgebraicGeometry.ProEtale.PurityTransport
