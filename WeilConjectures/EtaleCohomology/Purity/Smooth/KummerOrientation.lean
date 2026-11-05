/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerRelative
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionComp
public import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence

/-!
# The global orientation of the zero section of the affine line

For a rank-one datum whose Kummer class generates `R¹π_* Λ(1)` and a separated `k`-scheme `Y`
of finite type over an algebraically closed field `k`, the Kummer boundary `∂κ(t)` of the
coordinate of `𝔸¹_Y` is the fundamental class of the zero section `V(t) ≅ Y`: its adjoint
`Λ_{V(t)} ⟶ Rs^! (Λ(1)[2])` is an isomorphism.

The adjoint is pushed down to `Y` along `p : 𝔸¹_Y ⟶ Y`. There a class `γ` with supports on
`V(t)` becomes the morphism `Λ_Y ⟶ Rp_* Rs_! Rs^! (Λ(1)[2])` adjoint to `γ`, and the direct
image of the localization triangle of `(V(t), 𝔾_{m,Y})` identifies the latter target with
`R¹π_* Λ(1)`, concentrated in degree zero; under this identification the Kummer boundary is the
Kummer class, which generates.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The conjugate of a natural transformation of left adjoints, applied to the adjoint of a
morphism. -/
lemma Adjunction.homEquiv_comp_conjugateEquiv_app {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) {c : C}
    {d : D} (β : L₁.obj c ⟶ d) :
    adj₁.homEquiv c d β ≫ (conjugateEquiv adj₁ adj₂ α).app d =
      adj₂.homEquiv c d (α.app c ≫ β) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc,
    (conjugateEquiv adj₁ adj₂ α).naturality β, ← Category.assoc, unit_conjugateEquiv,
    Category.assoc, ← R₂.map_comp]

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The derived pushforward along an isomorphism is an equivalence. -/
instance isEquivalence_rightDerivedLowerStar_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] :
    (R((e)_*[ModuleCat.{u + 1} Λ])).IsEquivalence :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
    e).isEquivalence_right_of_isEquivalence_left

section Triangle

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  (T : Pretriangulated.Triangle (_root_.DerivedCategory C)) (hT : T ∈ distTriang _)
  (h₂ : ∀ m : ℤ, m ≠ 0 → IsZero ((_root_.DerivedCategory.homologyFunctor C m).obj T.obj₂))
  (h₃ : ∀ m : ℤ, m ≠ 0 → m ≠ 1 →
    IsZero ((_root_.DerivedCategory.homologyFunctor C m).obj T.obj₃))
  (hmor : IsIso ((_root_.DerivedCategory.homologyFunctor C 0).map T.mor₂))

include hT h₂ in
/-- In a distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` with `B` concentrated in degree `0`, the
boundary `H¹(C) ⟶ H²(A)` is invertible. -/
lemma isIso_homologySequenceδ_one_two :
    IsIso (_root_.DerivedCategory.HomologySequence.δ T 1 2) := by
  open _root_.DerivedCategory.HomologySequence in
  have : Mono (δ T 1 2) :=
    (exact₃ T hT 1 2).mono_g ((h₂ 1 one_ne_zero).eq_of_src _ _)
  have : Epi (δ T 1 2) := (exact₁ T hT 1 2).epi_f ((h₂ 2 (by norm_num)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end Triangle

section Orientation

variable [Finite Λ] [HasKummerClass Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
  [QuasiCompact aY]

end Orientation

end Etale

end AlgebraicGeometry
