/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.CompletedBaseChange.FrobeniusTower

/-!
# Finite reduction of the completed base change map

Let `𝔏 : TowerLimitFormalism 𝒯 T` be a derived limit formalism. A *reconstruction system*
(`CategoryTheory.TowerLimitFormalism.ReconstructionSystem`) consists of the finite reductions
`red_n : T ⥤ T` (`M ↦ M ⊗ᴸ P_n`) with the quotient maps `red_{n+1} ⟶ red_n` and natural maps
`rec_n : red_n (R lim M_•) ⟶ M_n` compatible with the transitions; for the reduction towers
of derived complete objects these are the isomorphisms of the reconstruction lemma
(`lem-weil-pbc-finite-reduction-reconstruction`), which enter here only as an input.

For a completion datum `𝔠` of a base change square, the *completed reduction square*
(`def-weil-pbc-completed-reduction-square`) has edges

```
  σ_n : S ⊗ P_n ⟶ A_n,   τ_n : T ⊗ P_n ⟶ C_n,   α_n = h_n σ_n,   δ_n = h'_n τ_n,
  ξ̄_n = Ex^comp ⊗ 1 : S ⊗ P_n ⟶ T ⊗ P_n,
```

where `τ_n` is the inverse of the direct-image completion `c = t ∘ R lim h' : C_∞ ≅ T` reduced
modulo `P_n`, followed by reconstruction. The main result
(`CategoryTheory.BaseChangeSquare.CompletionDatum.completedMapReduction`,
`lemma-weil-pbc-completed-map-reduction`) is `δ_n ξ̄_n = v'_n α_n`: the reduction of the
completed exchange map is the finite-level exchange map `v'_n = Ex_{□, K_n}`, compatibly with
the transitions and with Frobenius structures.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite Endofunctor

namespace CategoryTheory

namespace TowerLimitFormalism

variable {𝒯 : Type u₁} [Category.{v₁} 𝒯] {T : Type u₂} [Category.{v₂} T]
  [HasZeroObject T] [HasShift T ℤ] [Preadditive T] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] (𝔏 : TowerLimitFormalism 𝒯 T)

/-- A *reconstruction system* for a derived limit formalism: finite reductions
`red n : T ⥤ T` (`M ↦ M ⊗ᴸ P_n`) with quotient maps `q n : red (n + 1) ⟶ red n`, and natural
reconstruction maps `recon n : red n (R lim M_•) ⟶ M_n` compatible with the quotients and the
transitions (the derived counit of `lem-weil-pbc-finite-reduction-reconstruction`). -/
structure ReconstructionSystem where
  /-- The finite reduction `- ⊗ᴸ P_n`. -/
  red (n : ℕ) : T ⥤ T
  /-- The quotient map `- ⊗ᴸ P_{n+1} ⟶ - ⊗ᴸ P_n`. -/
  q (n : ℕ) : red (n + 1) ⟶ red n
  /-- The reconstruction map `(R lim M_•) ⊗ᴸ P_n ⟶ M_n`. -/
  recon (n : ℕ) : 𝔏.rlim ⋙ red n ⟶ 𝔏.ev n
  /-- Reconstruction is compatible with the quotients and the transitions. -/
  recon_comm (n : ℕ) (M : 𝒯) :
    (q n).app (𝔏.rlim.obj M) ≫ (recon n).app M = (recon (n + 1)).app M ≫ (𝔏.transition n).app M

end TowerLimitFormalism

namespace BaseChangeSquare

variable {𝒳 : Type u₁} {𝒴 : Type u₂} {𝒳' : Type u₃} {𝒴' : Type u₄}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{v₃} 𝒳'] [Category.{v₄} 𝒴']
  {𝒯 : Type u₅} {𝒰 : Type u₆} {𝒯' : Type u₇} {𝒰' : Type u₈}
  [Category.{v₅} 𝒯] [Category.{v₆} 𝒰] [Category.{v₇} 𝒯'] [Category.{v₈} 𝒰']
  [HasZeroObject 𝒳'] [HasShift 𝒳' ℤ] [Preadditive 𝒳']
  [∀ n : ℤ, (shiftFunctor 𝒳' n).Additive] [Pretriangulated 𝒳']
  [HasZeroObject 𝒴'] [HasShift 𝒴' ℤ] [Preadditive 𝒴']
  [∀ n : ℤ, (shiftFunctor 𝒴' n).Additive] [Pretriangulated 𝒴']

namespace CompletionDatum

variable {𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴'} {𝔗 : BaseChangeSquare 𝒯 𝒰 𝒯' 𝒰'}
  (𝔠 : CompletionDatum 𝔇 𝔗) (𝔯 : 𝔠.limY'.ReconstructionSystem) (K : 𝒳)

/-- The direct-image completion `c = t ∘ R lim h' : C_∞ ⟶ T` (with `t` the inverse of the
direct-image/limit commutation); `d c = H'` for `d = t⁻¹`. -/
def directImageCompletion :
    𝔠.limY'.rlim.obj (𝔠.ρ.cornerC.obj K) ⟶ 𝔇.lowerF'.obj (𝔠.completedPullback'.obj K) :=
  𝔠.limY'.rlim.map (𝔠.ρ.arrowH'.app K) ≫ 𝔠.lowerLim.inv.app (𝔗.upperG'.obj (𝔠.ρ.redX.obj K))

instance [IsIso (𝔠.ρ.arrowH'.app K)] : IsIso (𝔠.directImageCompletion K) := by
  dsimp [directImageCompletion]; infer_instance

/-- The completed exchange map factors as `Ex^comp = c ∘ V`. -/
lemma completedExchange_app_eq_comp (K : 𝒳) :
    𝔠.completedExchange.app K =
      𝔠.limY'.rlim.map (𝔠.ρ.arrowV.app K) ≫ 𝔠.directImageCompletion K := by
  rw [completedExchange_app_eq, directImageCompletion]

/-- The edge `σ_n : S ⊗ᴸ P_n ⟶ A_n`, finite reduction of the completed pullback (Blueprint
`def-weil-pbc-completed-reduction-square`). -/
def reductionσ (n : ℕ) :
    (𝔯.red n).obj ((𝔇.lowerF ⋙ 𝔠.completedPullback).obj K) ⟶
      (𝔠.limY'.ev n).obj (𝔠.ρ.cornerA.obj K) :=
  (𝔯.recon n).app (𝔠.ρ.cornerA.obj K)

variable [IsIso (𝔠.ρ.arrowH'.app K)]

/-- The edge `τ_n : T ⊗ᴸ P_n ⟶ C_n`: the inverse of the direct-image completion reduced modulo
`P_n`, followed by finite reduction (Blueprint `def-weil-pbc-completed-reduction-square`). -/
noncomputable def reductionτ (n : ℕ) :
    (𝔯.red n).obj (𝔇.lowerF'.obj (𝔠.completedPullback'.obj K)) ⟶
      (𝔠.limY'.ev n).obj (𝔠.ρ.cornerC.obj K) :=
  (𝔯.red n).map (inv (𝔠.directImageCompletion K)) ≫ (𝔯.recon n).app (𝔠.ρ.cornerC.obj K)

/-- The edge `α_n = h_n σ_n : S ⊗ᴸ P_n ⟶ B_n`. -/
noncomputable def reductionα (n : ℕ) :
    (𝔯.red n).obj ((𝔇.lowerF ⋙ 𝔠.completedPullback).obj K) ⟶
      (𝔠.limY'.ev n).obj (𝔠.ρ.cornerB.obj K) :=
  𝔠.reductionσ 𝔯 K n ≫ (𝔠.limY'.ev n).map (𝔠.ρ.arrowH.app K)

/-- The edge `δ_n = h'_n τ_n : T ⊗ᴸ P_n ⟶ D_n`. -/
noncomputable def reductionδ (n : ℕ) :
    (𝔯.red n).obj (𝔇.lowerF'.obj (𝔠.completedPullback'.obj K)) ⟶
      (𝔠.limY'.ev n).obj (𝔠.ρ.cornerD.obj K) :=
  𝔠.reductionτ 𝔯 K n ≫ (𝔠.limY'.ev n).map (𝔠.ρ.arrowH'.app K)

/-- The edge `ξ̄_n = Ex^comp ⊗ 1 : S ⊗ᴸ P_n ⟶ T ⊗ᴸ P_n`. -/
def reductionξ (n : ℕ) :
    (𝔯.red n).obj ((𝔇.lowerF ⋙ 𝔠.completedPullback).obj K) ⟶
      (𝔯.red n).obj (𝔇.lowerF'.obj (𝔠.completedPullback'.obj K)) :=
  (𝔯.red n).map (𝔠.completedExchange.app K)

/-- `τ_n ξ̄_n = v_n σ_n`: functorial finite reduction and the limit rectangle. -/
@[reassoc]
lemma reductionξ_comp_reductionτ (n : ℕ) :
    𝔠.reductionξ 𝔯 K n ≫ 𝔠.reductionτ 𝔯 K n =
      𝔠.reductionσ 𝔯 K n ≫ (𝔠.limY'.ev n).map (𝔠.ρ.arrowV.app K) := by
  have h := (𝔯.recon n).naturality (𝔠.ρ.arrowV.app K)
  dsimp at h
  simp only [reductionξ, reductionτ, reductionσ, completedExchange_app_eq_comp,
    Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc, IsIso.hom_inv_id,
    Category.comp_id]
  exact h

/-- **Finite reduction of the completed map** (Blueprint
`lemma-weil-pbc-completed-map-reduction`): the completed reduction square commutes,
`δ_n ξ̄_n = v'_n α_n`. Hence, conjugated by the reduction isomorphisms `α_n`, `δ_n`, the
reduction of `Ex^comp` modulo `P_n` is the finite-level exchange map `v'_n = Ex_{□, K_n}`. -/
theorem completedMapReduction (n : ℕ) :
    𝔠.reductionξ 𝔯 K n ≫ 𝔠.reductionδ 𝔯 K n =
      𝔠.reductionα 𝔯 K n ≫ (𝔠.limY'.ev n).map (𝔠.ρ.arrowV'.app K) := by
  rw [reductionδ, reductionξ_comp_reductionτ_assoc, reductionα, Category.assoc,
    𝔠.limY'.ev_rectangle (𝔠.ρ.rectangle_app K) n]

/-- If `α_n` and `δ_n` are isomorphisms (the reconstruction and projection-formula
isomorphisms), the reduction `ξ̄_n` of the completed exchange map is conjugate to the
finite-level exchange map `v'_n`. -/
lemma reductionξ_eq (n : ℕ) [IsIso (𝔠.reductionδ 𝔯 K n)] :
    𝔠.reductionξ 𝔯 K n = 𝔠.reductionα 𝔯 K n ≫ (𝔠.limY'.ev n).map (𝔠.ρ.arrowV'.app K) ≫
      inv (𝔠.reductionδ 𝔯 K n) := by
  rw [← Category.assoc, ← completedMapReduction, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

/-- The edge `σ_n` commutes with the quotient maps `n + 1 ⟶ n`. -/
@[reassoc]
lemma reductionσ_comm (n : ℕ) :
    (𝔯.q n).app _ ≫ 𝔠.reductionσ 𝔯 K n =
      𝔠.reductionσ 𝔯 K (n + 1) ≫ (𝔠.limY'.transition n).app (𝔠.ρ.cornerA.obj K) :=
  𝔯.recon_comm n _

/-- The edge `τ_n` commutes with the quotient maps `n + 1 ⟶ n`. -/
@[reassoc]
lemma reductionτ_comm (n : ℕ) :
    (𝔯.q n).app _ ≫ 𝔠.reductionτ 𝔯 K n =
      𝔠.reductionτ 𝔯 K (n + 1) ≫ (𝔠.limY'.transition n).app (𝔠.ρ.cornerC.obj K) := by
  rw [reductionτ, reductionτ, ← (𝔯.q n).naturality_assoc, Category.assoc, 𝔯.recon_comm]
  rfl

/-- The edge `ξ̄_n` commutes with the quotient maps `n + 1 ⟶ n`. -/
@[reassoc]
lemma reductionξ_comm (n : ℕ) :
    (𝔯.q n).app _ ≫ 𝔠.reductionξ 𝔯 K n = 𝔠.reductionξ 𝔯 K (n + 1) ≫ (𝔯.q n).app _ :=
  ((𝔯.q n).naturality _).symm

/-- The edges `α_n` and `δ_n` commute with the quotient maps `n + 1 ⟶ n` (Blueprint
`lemma-weil-pbc-completed-map-reduction`: the squares for `n + 1 → n` commute). -/
lemma reductionα_δ_comm (n : ℕ) :
    (𝔯.q n).app _ ≫ 𝔠.reductionα 𝔯 K n =
        𝔠.reductionα 𝔯 K (n + 1) ≫ (𝔠.limY'.transition n).app (𝔠.ρ.cornerB.obj K) ∧
      (𝔯.q n).app _ ≫ 𝔠.reductionδ 𝔯 K n =
        𝔠.reductionδ 𝔯 K (n + 1) ≫ (𝔠.limY'.transition n).app (𝔠.ρ.cornerD.obj K) := by
  constructor
  · simp only [reductionα, Category.assoc]
    rw [← 𝔠.limY'.map_tower_comm]
    exact reassoc_of% (𝔠.reductionσ_comm 𝔯 K n)
  · simp only [reductionδ, Category.assoc]
    rw [← 𝔠.limY'.map_tower_comm]
    exact reassoc_of% (𝔠.reductionτ_comm 𝔯 K n)

/-- The completed reduction square is natural in `K`: for `φ : K ⟶ K'` (e.g. a tower
compatible endomorphism), the edges `α_n`, `δ_n`, `ξ̄_n` intertwine the induced maps. -/
lemma reduction_naturality {K' : 𝒳} [IsIso (𝔠.ρ.arrowH'.app K')] (φ : K ⟶ K') (n : ℕ) :
    𝔠.reductionα 𝔯 K n ≫ (𝔠.limY'.ev n).map (𝔠.ρ.cornerB.map φ) =
        (𝔯.red n).map ((𝔇.lowerF ⋙ 𝔠.completedPullback).map φ) ≫ 𝔠.reductionα 𝔯 K' n ∧
      𝔠.reductionξ 𝔯 K n ≫ (𝔯.red n).map ((𝔠.completedPullback' ⋙ 𝔇.lowerF').map φ) =
        (𝔯.red n).map ((𝔇.lowerF ⋙ 𝔠.completedPullback).map φ) ≫ 𝔠.reductionξ 𝔯 K' n := by
  constructor
  · have h₁ := (𝔯.recon n).naturality (𝔠.ρ.cornerA.map φ)
    have h₂ := 𝔠.ρ.arrowH.naturality φ
    dsimp at h₁
    simp only [reductionα, reductionσ, Category.assoc, ← Functor.map_comp, ← h₂]
    rw [Functor.map_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    exact h₁.symm
  · simp only [reductionξ, ← Functor.map_comp]
    congr 1
    exact (𝔠.completedExchange.naturality φ).symm

end CompletionDatum

end BaseChangeSquare

end CategoryTheory
