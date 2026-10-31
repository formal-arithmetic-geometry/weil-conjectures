/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingAdjunctionData
import WeilConjectures.SixFunctors.IntegralDualizingExceptionalPresentation

/-! # The prescribed dualizing limit is an exceptional value

Source: current blueprint prop-coef-integral-dualizing.proof.md, first paragraph.
(blueprint: lem-coef-integral-dualizing-exceptional-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Any complete presentation of the finite dualizing objects is the exceptional value.
Source: current blueprint prop-coef-integral-dualizing.proof.md, first paragraph
(blueprint: lem-coef-integral-dualizing-exceptional-realization).

Proof: the exceptional-presentation theorem gives an adjunction record A whose value
has a Roos triangle on the actual evaluations of T. Unpack both presentations using
the same published countable-product instance. Their middle arrows are the same
1-minus-shift endomorphism. The triangle morphism axiom completes the identity square
of the two products to a map between the first vertices. Its second and third components
are identities, so its first component is an isomorphism. This includes the zero diagram
and the empty scheme; no equality or uniqueness of arbitrary integral arrows is claimed.
-/
theorem integralDualizing_exceptional_realization
    (T : NormalizedDVRTower l E X D hl)
    (e : ∀ n : ℕ, T.M n ≅ integralDualizingFiniteTerm l E D X n)
    (he : ∀ {m n : ℕ} (h : n ≤ m),
      T.tau h ≫ (normalizedDVRRes l E X h).map (e n).hom =
        (e m).hom ≫
          (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
            (integralDualizingFiniteComparison l E D X hl h))
    (M : sfIntegralConstructibleCategory l E X)
    (hM : IntegralDualizingLimitPresentation l E D hl X T M.obj) :
    ∃ A : IntegralDualizingAdjunctionData D l hl E X,
      Nonempty (M.obj ≅ (A.right.obj A.unit).obj) := by
  obtain ⟨A, hA⟩ := integralDualizing_exceptional_presentation D l hl E X T e he
  let : HasCountableProducts (completedIntegralDerivedCategory l E X D hl) :=
    integralOperationsDerivedCountableProducts l E X
  obtain ⟨p, δ, htriangle, _, _⟩ := hM
  obtain ⟨q, ε, htriangleA, _, _⟩ := hA
  let U := CategoryTheory.Pretriangulated.Triangle.mk p
    (towerTransitionEndomorphism
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)) δ
  let V := CategoryTheory.Pretriangulated.Triangle.mk q
    (towerTransitionEndomorphism
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)) ε
  obtain ⟨a, ha₁, ha₃⟩ :=
    CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism₁
      U V htriangle htriangleA (𝟙 _) (𝟙 _) (by simp [U, V])
  let f : U ⟶ V := CategoryTheory.Pretriangulated.Triangle.homMk U V a (𝟙 _) (𝟙 _)
    ha₁ (by simp [U, V]) ha₃
  have : IsIso f.hom₂ := by
    dsimp [f, CategoryTheory.Pretriangulated.Triangle.homMk]
    infer_instance
  have : IsIso f.hom₃ := by
    dsimp [f, CategoryTheory.Pretriangulated.Triangle.homMk]
    infer_instance
  have : IsIso a := CategoryTheory.Pretriangulated.isIso₁_of_isIso₂₃
    f htriangle htriangleA inferInstance inferInstance
  exact ⟨A, ⟨asIso a⟩⟩


end WeilConjectures
