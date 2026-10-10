/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.SectionTransport

/-!
# Morphisms between constant pro-étale sheaves are locally constant

Let `Y` be a scheme, `Λ` a commutative ring, `V` a finitely generated `Λ`-module and `E` a
`Λ`-module. A morphism `f : c(V) ⟶ c(E)` of constant pro-étale sheaves need not be of the form
`c(A)` for a linear map `A : V ⟶ E`, but it is so after pullback to the members of a covering
sieve of the terminal object of `Y_proét`
(`AlgebraicGeometry.ProEtale.exists_sieve_upperStar_map_eq_constantSheaf_map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open _root_.AlgebraicGeometry.Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {Y : Scheme.{u}}

/-- Constant sections over the terminal object are linear in the element. -/
lemma constSection_terminal_sum {E : ModuleCat.{u + 1} Λ} {ι : Type*} (s : Finset ι)
    (a : ι → Λ) (e : ι → E) (U : Y.ProEt) :
    constSection E U (∑ i ∈ s, a i • e i) = ∑ i ∈ s, a i • constSection E U (e i) := by
  simp only [constSection, map_sum, map_smul]

/-- **Morphisms between constant sheaves are locally constant.** For a morphism
`f : c(V) ⟶ c(E)` of constant pro-étale sheaves on `Y` with `V` finitely generated, there is a
covering sieve of the terminal object of `Y_proét` such that for every member `W`, with
structure morphism `g`, the pullback `g^* f` is `c(A)` for a linear map `A : V ⟶ E`, up to the
identifications `g^* c(-) ≅ c(-)`. -/
lemma exists_sieve_upperStar_map_eq_constantSheaf_map {V E : ModuleCat.{u + 1} Λ}
    [Module.Finite Λ V]
    (f : (constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)).obj V ⟶
      (constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)).obj E) :
    ∃ R ∈ Scheme.ProEt.topology Y (terminalProEt Y), ∀ ⦃W : Y.ProEt⦄ (h : W ⟶ terminalProEt Y),
      R h → ∃ A : V ⟶ E,
        (upperStarConstantSheafIso W.hom).inv.app V ≫ (W.hom)^*[ModuleCat.{u + 1} Λ].map f ≫
          (upperStarConstantSheafIso W.hom).hom.app E =
        (constantSheaf (Scheme.ProEt.topology W.left) (ModuleCat.{u + 1} Λ)).map A := by
  obtain ⟨S, hS, hS'⟩ := exists_mem_forall_exists_linearMap (T := terminalProEt Y)
    (Scheme.ProEt.topology Y) V E f
  refine ⟨S, hS, fun W h hh ↦ ?_⟩
  by_cases hW : (⊥ : Sieve W) ∈ Scheme.ProEt.topology Y W
  · sorry
  obtain ⟨A, hA⟩ := hS' h hh hW
  refine ⟨A, constantSheaf_hom_ext fun e ↦ ?_⟩
  sorry

end AlgebraicGeometry.ProEtale
