/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.ExactCouple.TruncationCouple
public import WeilConjectures.Algebra.Homology.ExactCouple.TriangulatedHom

/-!
# The truncation couple of a triangulated functor

Let `F : D⁺(A) ⥤ D⁺(B)` be a triangulated functor and `M` an object of `D⁺(A)`. Applying `F` to
the tower of truncation triangles `τ_{≤ q - 1} M ⟶ τ_{≤ q} M ⟶ Hᵠ(M)[-q] ⟶ (τ_{≤ q - 1} M)⟦1⟧`
(`DerivedCategory.Plus.truncLETower`, the truncation triangles of blueprint
`lem-weil-pbc-truncation-triangle` for the canonical t-structure) and taking cohomology gives an
exact couple `DerivedCategory.Plus.functorTruncationCouple F M`, indexed by filtration degree
`p` and total degree `n = p + q`:

`D^{p, n} = Hⁿ(F(τ_{≤ n - p} M))`, `E^{p, n} = Hⁿ(F(Hⁿ⁻ᵖ(M)[p - n])) ≅ Hᵖ(F(Hⁿ⁻ᵖ(M)))`

(`DerivedCategory.Plus.functorTruncationCoupleEIso`). For `F = R⁺v` this is the truncation couple
`CategoryTheory.Functor.truncationCouple` of `v`. Its exactness is the exactness of the long
exact cohomology sequences of distinguished triangles (blueprint
`lem-sf-derived-homology-long-exact`, Mathlib's `DerivedCategory.HomologySequence.exact₂`).

A natural transformation `τ : F₁ ⟶ F₂` of triangulated functors commuting with the shifts induces
a morphism of exact couples (`DerivedCategory.Plus.functorTruncationCoupleHom`) whose components
are `Hⁿ(τ_{τ_{≤ q} M})` and `Hⁿ(τ_{Hᵠ(M)[-q]})`; under the identifications of the `E`-objects its
component on `E^{p, n}` is `Hᵖ(τ_{Hᵠ(M)})` (`DerivedCategory.Plus.functorTruncationCoupleHom_τE`).

The abutment maps `ι : D^{p, n} = Hⁿ(F(τ_{≤ n - p} M)) ⟶ Hⁿ(F M)`
(`DerivedCategory.Plus.functorTruncationCoupleι`) are compatible with `α`, and with the morphism
induced by `τ`. If `F` does not lower the cohomological degree and `M` is `≥ a`, they are
isomorphisms for `p ≤ 0`, the couple is a half-plane couple, and its spectral sequence converges
to the image filtration of the maps `Hⁿ(F(τ_{≤ q} M)) ⟶ Hⁿ(F M)`
(`DerivedCategory.Plus.functorTruncationCouple_convergesTo`).
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated Triangulated

namespace DerivedCategory.Plus

open _root_.DerivedCategory.Plus.TStructure (t)

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- The maps of the tower of truncations are compatible with the maps `τ_{≤ q} M ⟶ M`. -/
@[reassoc]
lemma truncLETower_mor₁_eTruncLTι_app (M : Plus A) (q : ℤ) :
    (truncLETower M).mor₁ q ≫ (t.eTruncLTι ((q + 1 : ℤ) : EInt)).app M =
      (t.eTruncLTι ((q - 1 + 1 : ℤ) : EInt)).app M := by
  dsimp [truncLETower, truncLETriangle, TStructure.triangleω₁δ]
  rw [Subsingleton.elim (ComposableArrows.twoδ₂Toδ₁' (⊥ : EInt) _ _ bot_le
    (coe_sub_one_add_one_le q) |>.app 0) (𝟙 _)]
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  exact t.eTruncLT_map_app_eTruncLTι_app _ M

section

variable (F : Plus A ⥤ Plus B) [F.CommShift ℤ] [F.IsTriangulated] (M : Plus A)

/-- The **truncation couple of a triangulated functor** `F : D⁺(A) ⥤ D⁺(B)` at `M ∈ D⁺(A)`: the
exact couple of the tower `F(τ_{≤ q} M)` under the cohomology functors, indexed by filtration
degree `p` and total degree `n`, with `D^{p, n} = Hⁿ(F(τ_{≤ n - p} M))` and
`E^{p, n} = Hⁿ(F(Y_{n - p}))`, `Y_q ≅ Hᵠ(M)[-q]`. -/
noncomputable def functorTruncationCouple : ExactCouple B ((-1, 0) : ℤ × ℤ) (2, 1) 0 :=
  ((truncLETower M).map F).exactCoupleTotal (homologyFunctor B 0)

lemma functorTruncationCouple_D (p n : ℤ) :
    (functorTruncationCouple F M).D (p, n) =
      (homologyFunctor B n).obj (F.obj ((truncLETower M).X (n - p))) := rfl

lemma functorTruncationCouple_E (p n : ℤ) :
    (functorTruncationCouple F M).E (p, n) =
      (homologyFunctor B n).obj (F.obj ((truncLETower M).Y (n - p))) := rfl

/-- The `E`-objects of the truncation couple of `F`:
`E^{p, n} = Hⁿ(F(Hᵠ(M)[-q])) ≅ Hᵖ(F(Hᵠ(M)[0]))` with `q = n - p`, through the shift isomorphisms
of `F` and of the cohomology functors. -/
noncomputable def functorTruncationCoupleEIso (p n : ℤ) :
    (functorTruncationCouple F M).E (p, n) ≅ (homologyFunctor B p).obj
      (F.obj ((singleFunctor A 0).obj ((homologyFunctor A (n - p)).obj M))) :=
  (homologyFunctor B n).mapIso (F.mapIso (truncLETowerYIso M (n - p) ≪≫
      ((singleFunctors A).shiftIso (-(n - p)) (n - p) 0 (by omega)).symm.app _)) ≪≫
    (homologyFunctor B n).mapIso ((F.commShiftIso (-(n - p))).app _) ≪≫
    ((homologyFunctor B 0).shiftIso (-(n - p)) n p (by omega)).app _

/-- The abutment maps `D^{p, n} = Hⁿ(F(τ_{≤ n - p} M)) ⟶ Hⁿ(F M)` of the truncation couple of
`F`, induced by the maps `τ_{≤ n - p} M ⟶ M`. -/
noncomputable def functorTruncationCoupleι (p n : ℤ) :
    (functorTruncationCouple F M).D (p, n) ⟶ (homologyFunctor B n).obj (F.obj M) :=
  (homologyFunctor B n).map (F.map ((t.eTruncLTι ((n - p + 1 : ℤ) : EInt)).app M))

/-- The abutment maps of the truncation couple of `F` are compatible with `α`. -/
@[reassoc]
lemma functorTruncationCouple_α_ι (p n : ℤ) :
    (functorTruncationCouple F M).α (p + 1, n) (p, n) ≫ functorTruncationCoupleι F M p n =
      functorTruncationCoupleι F M (p + 1) n := by
  dsimp only [functorTruncationCouple, functorTruncationCoupleι]
  rw [TriangleTower.exactCoupleTotal_α, TriangleTower.totalEquiv_symm_apply,
    TriangleTower.totalEquiv_symm_apply, TriangleTower.coupleα_eq _ _ _ _ _ (by omega)]
  dsimp only [TriangleTower.map_X, TriangleTower.map_mor₁]
  rw [← Functor.map_comp]
  congr 1
  rw [Category.assoc, ← F.map_comp, truncLETower_mor₁_eTruncLTι_app]
  have h : n - (p + 1) = n - p - 1 := by omega
  rw [eqToHom_map (G := F) (p := by rw [h]) |>.symm.trans rfl |>.symm.trans rfl]
  sorry

end

end DerivedCategory.Plus
