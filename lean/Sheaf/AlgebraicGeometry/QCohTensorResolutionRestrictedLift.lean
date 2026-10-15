module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An augmented map into a restricted projective resolution lifts degreewise. -/
theorem tensorResolutionRestrictedLift
    (A C : Type u) [CommRing A] [CommRing C] (φ : A →+* C)
    (M : ModuleCat.{u} A) (N : ModuleCat.{u} C)
    (P : ProjectiveResolution M) (R : ProjectiveResolution N)
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) :
    ∃ a : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
        (.down ℕ)).obj R.complex,
      a.f 0 ≫ (ModuleCat.restrictScalars φ).map (R.π.f 0) = P.π.f 0 ≫ f := by
  classical
  let F := ModuleCat.restrictScalars φ
  let L := (F.mapHomologicalComplex (.down ℕ)).obj R.complex
  let e := F.map (R.π.f 0)
  let z := Projective.factorThru (P.π.f 0 ≫ f) e
  have hz : z ≫ e = P.π.f 0 ≫ f := Projective.factorThru_comp _ _
  have h₀ := R.exact₀.map F
  let o := h₀.liftFromProjective (P.complex.d 1 0 ≫ z) (by
    change (P.complex.d 1 0 ≫ z) ≫ e = 0
    rw [Category.assoc, hz, ← Category.assoc, P.complex_d_comp_π_f_zero,
      Limits.zero_comp])
  have ho : o ≫ L.d 1 0 = P.complex.d 1 0 ≫ z :=
    h₀.liftFromProjective_comp _ _
  let step : ∀ (n : ℕ)
      (p : Σ' (g : P.complex.X n ⟶ L.X n)
        (g' : P.complex.X (n + 1) ⟶ L.X (n + 1)),
        g' ≫ L.d (n + 1) n = P.complex.d (n + 1) n ≫ g),
      Σ' g'' : P.complex.X (n + 2) ⟶ L.X (n + 2),
        g'' ≫ L.d (n + 2) (n + 1) = P.complex.d (n + 2) (n + 1) ≫ p.2.1 := by
    intro n p
    have hn := (R.exact_succ n).map F
    let b := P.complex.d (n + 2) (n + 1) ≫ p.2.1
    have hb : b ≫ L.d (n + 1) n = 0 := by
      dsimp only [b]
      rw [Category.assoc, p.2.2, ← Category.assoc, HomologicalComplex.d_comp_d,
        Limits.zero_comp]
    exact ⟨hn.liftFromProjective b hb, hn.liftFromProjective_comp b hb⟩
  exact ⟨ChainComplex.mkHom P.complex L z o ho step, hz⟩

end AlgebraicGeometry
