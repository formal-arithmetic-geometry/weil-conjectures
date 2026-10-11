/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude

/-!
# Bounded flat models on the pro-étale site

Finite Tor amplitude in `[a, b]` of a bounded constructible complex of pro-étale sheaves is the
same as admitting a bounded flat model concentrated in `[a, b]` (`sk-lem-sf-flat-model`,
`lem-sf-flat-model`). This is the pro-étale counterpart of
`AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatModel`.

## Main statements

- `AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_iff_exists_flatModel`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

variable {X : Scheme.{u}}

namespace ProEtale.DerivedCategory

/-- Blueprint `sk-lem-sf-flat-model` (also `lem-sf-flat-model`): Bounded flat model of finite
Tor amplitude, on the small pro-étale site.

For `K ∈ D^b_c(X_proét, A)` and integers `a ≤ b` the following are equivalent: `K` has Tor
amplitude in `[a, b]`; and `K` is isomorphic in `D(X_proét, A)` to a bounded complex `P` of flat
pro-étale sheaves with `P^q = 0` for `q ∉ [a, b]`.

A bounded complex of flat sheaves is K-flat, so its derived tensor product with a sheaf is the
tensor product of complexes, concentrated in `[a, b]`. Conversely one truncates a bounded above
flat resolution in degree `a`, whose term in degree `a` is flat by the Tor criterion
(`DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat`). -/
theorem torAmplitudeIn_iff_exists_flatModel (a b : ℤ) (_hab : a ≤ b)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (_hK : DerivedCategory.boundedConstructible A X K) :
    torAmplitudeIn A X a b K ↔
      ∃ P : CochainComplex (Sheaf (Scheme.ProEt.topology X) A) ℤ,
        ((∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧ ∀ q : ℤ, ObjectProperty.flat (P.X q)) ∧
          Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P) := by
  refine (_root_.DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat a b K).trans
    ⟨fun ⟨P, h₁, h₂, h₃, ⟨e⟩⟩ ↦ ⟨P, ⟨fun q hq ↦ ?_, h₃⟩, ⟨e.symm⟩⟩,
      fun ⟨P, ⟨h₁, h₂⟩, ⟨e⟩⟩ ↦ ⟨P, ?_, ?_, h₂, ⟨e.symm⟩⟩⟩
  · rcases hq with hq | hq
    · exact P.isZero_of_isStrictlyGE a q hq
    · exact P.isZero_of_isStrictlyLE b q hq
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun q hq ↦ h₁ q (.inl hq)
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun q hq ↦ h₁ q (.inr hq)

end ProEtale.DerivedCategory

end AlgebraicGeometry
