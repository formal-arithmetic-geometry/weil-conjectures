/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Basic

/-! # Isomorphisms of the pair category from transport-compatible representatives

A family of stage isomorphisms `φ n : X.toStage ≅ Y.toStage`, one at every common stage `n`,
which is compatible with the transports `S.tr`, defines a unique isomorphism `X ≅ Y` of the
pair category represented by `φ n` at every common stage.
-/

@[expose] public section

universe w u v

open CategoryTheory

namespace CategoryTheory.StageSystem.PairCategory

variable {I : Type w} [Preorder I] [IsDirectedOrder I] {C : I → Type u}
  [∀ i, Category.{v} (C i)] {S : StageSystem C}

/-- A transport-compatible family of stage isomorphisms is represented by a single isomorphism
of the pair category. Compatibility `hφ` means that for `n ≤ p` the square
```
X_n --φ n--> Y_n
 |            |
 tr           tr
 v            v
X_p --φ p--> Y_p
```
commutes, i.e. `S.tr h (φ n).hom = (φ p).hom`. -/
theorem exists_iso_of_tr {X Y : S.PairCategory}
    (φ : ∀ (n : I) (hX : X.stage ≤ n) (hY : Y.stage ≤ n), X.toStage hX ≅ Y.toStage hY)
    (hφ : ∀ (n p : I) (hX : X.stage ≤ n) (hY : Y.stage ≤ n) (h : n ≤ p),
      S.tr h (φ n hX hY).hom = (φ p (hX.trans h) (hY.trans h)).hom) :
    ∃ e : X ≅ Y, ∀ (n : I) (hX : X.stage ≤ n) (hY : Y.stage ≤ n),
      e.hom = mkHom n hX hY (φ n hX hY).hom := by
  let n₀ := commonStage X.stage Y.stage
  let hX₀ : X.stage ≤ n₀ := le_commonStage_left _ _
  let hY₀ : Y.stage ≤ n₀ := le_commonStage_right _ _
  let e : X ≅ Y :=
    { hom := mkHom n₀ hX₀ hY₀ (φ n₀ hX₀ hY₀).hom
      inv := mkHom n₀ hY₀ hX₀ (φ n₀ hX₀ hY₀).inv
      hom_inv_id := by rw [mkHom_comp_mkHom, Iso.hom_inv_id, ← id_eq_mkHom]
      inv_hom_id := by rw [mkHom_comp_mkHom, Iso.inv_hom_id, ← id_eq_mkHom] }
  refine ⟨e, fun n hX hY ↦ ?_⟩
  obtain ⟨p, h₀, h⟩ := exists_ge_ge n₀ n
  exact (mkHom_eq_mkHom_iff' _ _).2
    ⟨p, h₀, h, (hφ n₀ p hX₀ hY₀ h₀).trans (hφ n p hX hY h).symm⟩

end CategoryTheory.StageSystem.PairCategory
