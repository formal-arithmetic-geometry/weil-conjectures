/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison

/-! # Existence of normalized scalar Tate-line coordinates

Source: smooth trace properties (2), scalar transport of Tate lines
(blueprint: new-det-sp-trace-cartier-scalar-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- Normalized scalar coordinates exist for every integral-compatible coefficient
map.  Use the uniquely normalized balanced tensor structure, the scalar
association comparison for the first line, and recursively its tensor powers.
Uniqueness of the normalized tensor structure gives the normalization field for
every other normalized structure.
Source: smooth trace properties (2), scalar transport
(blueprint: new-det-sp-trace-cartier-scalar-coordinates). -/
theorem trace_scalar_coordinates_nonempty
    {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell)
    (X : Scheme.{u}) : Nonempty (ScalarLineCoordinates ell a ha X) := by
  let m₀ := internalScalarMonoidal (R := c.obj ell) (S := c'.obj ell) a.hom.hom X
  let := m₀
  have line_eq (c : Coefficient ell) (d : ℕ) :
      c.line ell X d = Nat.rec (𝟙_ _) (fun _ N ↦ N ⊗ c.firstLine ell X) d := by
    induction d with
    | zero => rfl
    | succ d ih => exact congrArg (fun N ↦ N ⊗ c.firstLine ell X) ih
  have powers (d : ℕ) : ∃ p :
      (Mod.extendScalars (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell)
        a.hom.hom X)).obj (c.line ell X d) ≅ c'.line ell X d,
      HEq p (powerPull (Mod.extendScalars
        (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X))
        (c.firstLine ell X) (c'.firstLine ell X) (scalarFirst ell a ha X) d) := by
    rw [line_eq c d, line_eq c' d]
    exact ⟨_, HEq.rfl⟩
  choose power hpower using powers
  refine ⟨{ first := scalarFirst ell a ha X
            first_normalized := HEq.rfl
            power := power
            power_normalized := ?_ }⟩
  intro m hm d
  have heq : m = m₀ :=
    (internalScalarMonoidalNormalized_existsUnique
      (R := c.obj ell) (S := c'.obj ell) a.hom.hom X).unique
      hm (internalScalarMonoidalNormalized_existsUnique
        (R := c.obj ell) (S := c'.obj ell) a.hom.hom X).exists.choose_spec
  subst m
  exact hpower d

end AlgebraicGeometry.ProEtale.PurityTransport
