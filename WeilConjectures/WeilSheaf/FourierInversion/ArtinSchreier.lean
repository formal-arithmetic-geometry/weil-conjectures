/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ArtinSchreierPullback

/-!
# Fourier inversion: Artin–Schreier sheaves of functions

Multiplicativity of the Artin–Schreier sheaves `ℒ_{ψ,a}` (blueprint `lem-fd-as-lisse`,
`lem-fd-as-characters`) and their compatibility with pullback.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- Blueprint `lem-fd-as-lisse` (multiplicativity of the Artin–Schreier sheaves, from the
isotypic decomposition `lem-fd-as-characters`): `ℒ_{ψ,a} ⊗ ℒ_{ψ,b} ≅ ℒ_{ψ,a+b}`. -/
theorem nonempty_iso_tensorObj_artinSchreierOf (ψ : AddChar k₀ (PadicAlgCl l))
    (a b : Γ(X, ⊤)) :
    Nonempty ((artinSchreierOf ψ a).tensorObj (artinSchreierOf ψ b)
        (isLisse_artinSchreierOf ψ a) ≅ artinSchreierOf ψ (a + b)) :=
  sorry

/-- Blueprint `lem-fd-as-lisse` / `lem-fd-as-characters`: `ℒ_{ψ⁻¹,a} ≅ ℒ_{ψ,-a}`. -/
theorem nonempty_iso_artinSchreierOf_inv (ψ : AddChar k₀ (PadicAlgCl l)) (a : Γ(X, ⊤)) :
    Nonempty (artinSchreierOf ψ⁻¹ a ≅ artinSchreierOf ψ (-a)) :=
  sorry

/-- Blueprint `lem-fd-as-characters` (`ℒ_{ψ,0}` is the constant sheaf, the Artin–Schreier
cover of the zero function being the trivial torsor): `ℒ_{ψ,0} ≅ ℚ̄_ℓ`. -/
theorem nonempty_iso_artinSchreierOf_zero (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (artinSchreierOf ψ (0 : Γ(X, ⊤)) ≅ WeilSheaf.adicConstant k₀ l X) := by
  letI := Fintype.ofFinite k₀
  -- the zero function factors through the Artin–Schreier map, `0 ^ q - 0 = 0`
  have h : affineLine.homOfSection k₀ (0 : Γ(X, ⊤)) ≫ affineLine.smul k₀ 1 =
      affineLine.homOfSection k₀ (0 : Γ(X, ⊤)) ≫ affineLine.artinSchreierMap k₀ := by
    rw [affineLine.homOfSection_comp_smul, affineLine.homOfSection_comp_artinSchreierMap,
      mul_zero, zero_pow Fintype.card_ne_zero, sub_zero]
  exact ⟨(WeilSheaf.upperStarCompIso _ _).symm.app _ ≪≫ (WeilSheaf.upperStarCongrIso h).app _ ≪≫
    (WeilSheaf.upperStarCompIso _ _).app _ ≪≫
    (WeilSheaf.upperStar _).mapIso (WeilSheaf.upperStarArtinSchreierMapImageIso ψ) ≪≫
    WeilSheaf.upperStarAdicConstantIso _⟩

/-- Pullback of Artin–Schreier sheaves of functions: `φ^* ℒ_{ψ,a} ≅ ℒ_{ψ,φ^* a}`, from
`φ ≫ a = φ^* a` as morphisms to `𝔸¹` and the composition of pullbacks of Weil sheaves. -/
theorem nonempty_iso_upperStar_artinSchreierOf {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (φ : Y ⟶ X)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (ψ : AddChar k₀ (PadicAlgCl l)) (a : Γ(X, ⊤)) :
    Nonempty ((WeilSheaf.upperStar φ).obj (artinSchreierOf ψ a) ≅
      artinSchreierOf ψ (φ.appTop a)) :=
  ⟨(WeilSheaf.upperStarCompIso φ (affineLine.homOfSection k₀ a)).symm.app _ ≪≫
    (WeilSheaf.upperStarCongrIso (affineLine.comp_homOfSection φ a)).app _⟩


end AlgebraicGeometry
