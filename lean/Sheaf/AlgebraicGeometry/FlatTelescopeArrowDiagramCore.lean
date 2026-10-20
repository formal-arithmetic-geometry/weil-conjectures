module

public import WeilConjectures.AlgebraicGeometry.FlatTelescopeStageMap

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

-- The unchanged interface names existential maps not used in its property clauses.
set_option linter.unusedVariables false in
/-- Structural flat towers and level maps needed for the arrow-diagram construction.
Source: the first construction step of `lem-sc-flat-telescope-arrow-diagram`.
Proof: extract the bounded-above flat towers E and E' presenting P and P'.
Take E₀ = E₁ = E and E₂ = E', with their supplied transitions, the identity
level maps a and zero level maps b. The six required properties are the
boundedness and flatness already supplied by the two telescope hypotheses.
Compatibility with f is not asserted here; it belongs to the companion
arrow-diagram construction theorem.
(blueprint: lem-sc-flat-telescope-arrow-diagram-core) -/
theorem exists_flat_telescope_arrow_core (Y : Scheme.{u})
    (P P' : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : isFlatTelescope Y P) (hP' : isFlatTelescope Y P') (f : P ⟶ P') :
    let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
    ∃ (E₀ E₁ E₂ : ℕ → CochainComplex A ℤ)
      (t₀ : ∀ n : ℕ, E₀ n ⟶ E₀ (n + 1))
      (t₁ : ∀ n : ℕ, E₁ n ⟶ E₁ (n + 1))
      (t₂ : ∀ n : ℕ, E₂ n ⟶ E₂ (n + 1))
      (a : ∀ n : ℕ, E₀ n ⟶ E₁ n) (b : ∀ n : ℕ, E₀ n ⟶ E₂ n),
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₀ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₀ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₁ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₁ n).X i)) ∧
      (∀ n : ℕ, ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero ((E₂ n).X i)) ∧
      (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E₂ n).X i)) := by
  obtain ⟨E, t, hbound, hflat, _⟩ := hP
  obtain ⟨E', t', hbound', hflat', _⟩ := hP'
  exact ⟨E, E, E', t, t, t', (fun n ↦ 𝟙 (E n)), (fun _ ↦ 0),
    hbound, hflat, hbound, hflat, hbound', hflat'⟩

end AlgebraicGeometry
