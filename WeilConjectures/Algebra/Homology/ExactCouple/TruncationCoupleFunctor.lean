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

/-- The maps `α : D^{p + 1, n} ⟶ D^{p, n}` of the truncation couple of `F` are induced by the
maps `τ_{≤ n - p - 1} M ⟶ τ_{≤ n - p} M`. -/
lemma functorTruncationCouple_α (p n : ℤ) :
    (functorTruncationCouple F M).α (p + 1, n) (p, n) =
      (homologyFunctor B n).map (F.map (eqToHom (by congr 1; omega) ≫
        (truncLETower M).mor₁ (n - p))) := by
  dsimp only [functorTruncationCouple]
  rw [TriangleTower.exactCoupleTotal_α, TriangleTower.totalEquiv_symm_apply,
    TriangleTower.totalEquiv_symm_apply,
    TriangleTower.coupleα_eq _ _ _ _ _ (by dsimp only; omega)]
  dsimp only [TriangleTower.map_X, TriangleTower.map_mor₁]
  rw [eqToHom_map F (by congr 1; dsimp only; omega) |>.symm, ← F.map_comp]
  rfl

/-- The abutment maps of the truncation couple of `F` are compatible with `α`. -/
@[reassoc]
lemma functorTruncationCouple_α_ι (p n : ℤ) :
    (functorTruncationCouple F M).α (p + 1, n) (p, n) ≫ functorTruncationCoupleι F M p n =
      functorTruncationCoupleι F M (p + 1) n := by
  rw [functorTruncationCouple_α]
  dsimp only [functorTruncationCoupleι]
  rw [← Functor.map_comp, ← F.map_comp, Category.assoc, truncLETower_mor₁_eTruncLTι_app]
  congr 2
  rw [show n - p - 1 + 1 = n - (p + 1) + 1 by omega]
  simp

variable {M} in
/-- If `M` is `≥ a`, the objects `D^{p, n}` of the truncation couple of `F` vanish for
`n - p < a`. -/
lemma isZero_functorTruncationCouple_D (a : ℤ) [M.IsGE a] (p n : ℤ) (h : n - p < a) :
    IsZero ((functorTruncationCouple F M).D (p, n)) :=
  Functor.map_isZero _ (F.map_isZero (isZero_truncLETower_X M a _ h))

/-- The objects `E^{p, n}` of the truncation couple of `F` vanish if `M` has no cohomology in
degree `n - p`. -/
lemma isZero_functorTruncationCouple_E (p n : ℤ)
    (h : IsZero ((homologyFunctor A (n - p)).obj M)) :
    IsZero ((functorTruncationCouple F M).E (p, n)) :=
  ((homologyFunctor B p).map_isZero (F.map_isZero
    ((singleFunctor A 0).map_isZero h))).of_iso (functorTruncationCoupleEIso F M p n)

variable (hF : ∀ (X : Plus A) (n : ℤ) [X.IsGE n] (q : ℤ), q < n →
  IsZero ((homologyFunctor B q).obj (F.obj X)))

include hF in
/-- If `F` does not lower the cohomological degree, the abutment map
`Hⁿ(F(τ_{≤ q} M)) ⟶ Hⁿ(F M)` is an isomorphism for `q ≥ n`, i.e. `ι p n` is an isomorphism for
`p ≤ 0`. -/
lemma isIso_functorTruncationCoupleι (p n : ℤ) (hp : p ≤ 0) :
    IsIso (functorTruncationCoupleι F M p n) := by
  have hT := ι.map_distinguished _
    (F.map_distinguished _ (t.triangleLTGE_distinguished (n - p + 1) M))
  exact DerivedCategory.isIso_homologyMap_mor₁ _ hT (n - 1) n (by omega)
    (hF ((t.truncGE (n - p + 1)).obj M) (n - p + 1) (n - 1) (by omega))
    (hF ((t.truncGE (n - p + 1)).obj M) (n - p + 1) n (by omega))

include hF in
/-- If `F` does not lower the cohomological degree and `M` is `≥ a`, the truncation couple of
`F` is a half-plane couple: with `q = n - p`, `D^{p, n} = 0` for `q < a` and `E^{p, n} = 0`
unless `p ≥ 0` and `q ≥ a`. -/
lemma functorTruncationCouple_isHalfPlane (a : ℤ) [M.IsGE a] :
    (functorTruncationCouple F M).IsHalfPlane a where
  isZero_D p n h := isZero_functorTruncationCouple_D F a p n h
  isZero_E p n h := by
    obtain h | h := h
    · exact (hF _ 0 p h).of_iso (functorTruncationCoupleEIso F M p n)
    · exact isZero_functorTruncationCouple_E F M p n (isZero_homology_of_isGE M a _ h)

/-- The **image filtration** of `Hⁿ(F M)` by the images `Fᵖ = im (Hⁿ(F(τ_{≤ n - p} M)) ⟶ Hⁿ(F M))`
of the abutment maps of the truncation couple of `F`. -/
noncomputable abbrev functorTruncationCoupleFiltration (n : ℤ) :
    DecreasingFiltration ((homologyFunctor B n).obj (F.obj M)) :=
  (functorTruncationCouple F M).abutmentFiltration (functorTruncationCoupleι F M)
    (functorTruncationCouple_α_ι F M) n

lemma functorTruncationCoupleFiltration_F (n p : ℤ) :
    (functorTruncationCoupleFiltration F M n).F p =
      imageSubobject ((homologyFunctor B n).map
        (F.map ((t.eTruncLTι ((n - p + 1 : ℤ) : EInt)).app M))) :=
  rfl

include hF in
/-- If `F` does not lower the cohomological degree and `M` is `≥ a`, the image filtration of
`Hⁿ(F M)` is finite and separated: `Fᵖ = Hⁿ(F M)` for `p ≤ 0` and `Fᵖ = 0` for `p > n - a`. -/
lemma isFiniteSeparated_functorTruncationCoupleFiltration (a : ℤ) [M.IsGE a] (n : ℤ) :
    (functorTruncationCoupleFiltration F M n).IsFiniteSeparated := by
  have hbot : (functorTruncationCoupleFiltration F M n).F (n - a + 1) = ⊥ := by
    dsimp only [functorTruncationCoupleFiltration, ExactCouple.abutmentFiltration]
    rw [(isZero_functorTruncationCouple_D F a _ n (by omega)).eq_zero_of_src
      (functorTruncationCoupleι F M _ n), imageSubobject_zero]
  refine ⟨?_, ⟨_, hbot⟩, fun P hP ↦ eq_bot_iff.2 (hbot ▸ hP _)⟩
  have := isIso_functorTruncationCoupleι F M hF 0 n le_rfl
  dsimp only [functorTruncationCoupleFiltration, ExactCouple.abutmentFiltration]
  rw [imageSubobject_mono]
  exact Subobject.mk_eq_top_of_isIso _

include hF in
/-- **Convergence of the truncation couple of `F`.** If `F` does not lower the cohomological
degree and `M` is `≥ a`, the spectral sequence of the truncation couple of `F`, with
`E^{p, n} ≅ Hᵖ(F(Hⁿ⁻ᵖ(M)))`, converges to `Hⁿ(F M)` with its image filtration by the images of
`Hⁿ(F(τ_{≤ q} M)) ⟶ Hⁿ(F M)`. -/
theorem functorTruncationCouple_convergesTo (a : ℤ) [M.IsGE a] :
    (functorTruncationCouple F M).ConvergesTo (functorTruncationCoupleι F M)
      (functorTruncationCoupleFiltration F M) :=
  ExactCouple.convergesTo_abutmentFiltration _ _ _
    (fun n ↦ ⟨0, fun p hp ↦ isIso_functorTruncationCoupleι F M hF p n hp⟩)
    (fun n ↦ ⟨n - a + 1, fun p hp ↦ isZero_functorTruncationCouple_D F a p n (by omega)⟩)

end

section Hom

variable {F₁ F₂ : Plus A ⥤ Plus B} [F₁.CommShift ℤ] [F₁.IsTriangulated] [F₂.CommShift ℤ]
  [F₂.IsTriangulated] (τ : F₁ ⟶ F₂) [NatTrans.CommShift τ ℤ] (M : Plus A)

/-- The morphism of truncation couples induced by a natural transformation `τ : F₁ ⟶ F₂` of
triangulated functors which commutes with the shifts: its components are `Hⁿ(τ_{τ_{≤ q} M})`
and `Hⁿ(τ_{Y_q})` with `q = n - p`. -/
noncomputable def functorTruncationCoupleHom :
    ExactCouple.Hom (functorTruncationCouple F₁ M) (functorTruncationCouple F₂ M) :=
  ((truncLETower M).mapHom τ).exactCoupleTotalHom _

@[simp]
lemma functorTruncationCoupleHom_τD (p n : ℤ) :
    (functorTruncationCoupleHom τ M).τD (p, n) =
      (homologyFunctor B n).map (τ.app ((truncLETower M).X (n - p))) := rfl

@[simp]
lemma functorTruncationCoupleHom_τE (p n : ℤ) :
    (functorTruncationCoupleHom τ M).τE (p, n) =
      (homologyFunctor B n).map (τ.app ((truncLETower M).Y (n - p))) := rfl

omit [F₁.IsTriangulated] [F₂.IsTriangulated] in
lemma homologyFunctor_map_app_comp_shiftIso {G Y : Plus A} (k n m : ℤ) (h : k + n = m)
    (c : G ⟶ Y⟦k⟧) :
    (homologyFunctor B n).map (τ.app G) ≫ (homologyFunctor B n).map (F₂.map c) ≫
        (homologyFunctor B n).map ((F₂.commShiftIso k).hom.app Y) ≫
        ((homologyFunctor B 0).shiftIso k n m h).hom.app (F₂.obj Y) =
      (homologyFunctor B n).map (F₁.map c) ≫
        (homologyFunctor B n).map ((F₁.commShiftIso k).hom.app Y) ≫
        ((homologyFunctor B 0).shiftIso k n m h).hom.app (F₁.obj Y) ≫
        (homologyFunctor B m).map (τ.app Y) := by
  have key : τ.app G ≫ F₂.map c ≫ (F₂.commShiftIso k).hom.app Y =
      F₁.map c ≫ (F₁.commShiftIso k).hom.app Y ≫ (τ.app Y)⟦k⟧' := by
    rw [NatTrans.shift_app_comm, τ.naturality_assoc]
  have h₂ := ((homologyFunctor B 0).shiftIso k n m h).hom.naturality (τ.app Y)
  simp only [Functor.comp_map] at h₂
  erw [← h₂]
  simp only [← Functor.map_comp_assoc, key]

/-- Under the identifications `E^{p, n} ≅ Hᵖ(Fᵢ(Hⁿ⁻ᵖ(M)))`, the component on `E^{p, n}` of the
morphism of truncation couples induced by `τ` is `Hᵖ(τ_{Hⁿ⁻ᵖ(M)})`. -/
@[reassoc]
lemma functorTruncationCoupleHom_τE_comp_eIso_hom (p n : ℤ) :
    (functorTruncationCoupleHom τ M).τE (p, n) ≫ (functorTruncationCoupleEIso F₂ M p n).hom =
      (functorTruncationCoupleEIso F₁ M p n).hom ≫ (homologyFunctor B p).map
        (τ.app ((singleFunctor A 0).obj ((homologyFunctor A (n - p)).obj M))) := by
  simp only [functorTruncationCoupleEIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc, functorTruncationCoupleHom_τE]
  exact homologyFunctor_map_app_comp_shiftIso τ _ n p _ _

/-- The component on `D^{p, n}` of the morphism of truncation couples induced by `τ` is
compatible with the abutment maps, the map on the abutments being `Hⁿ(τ_M)`. -/
@[reassoc]
lemma functorTruncationCoupleHom_τD_ι (p n : ℤ) :
    (functorTruncationCoupleHom τ M).τD (p, n) ≫ functorTruncationCoupleι F₂ M p n =
      functorTruncationCoupleι F₁ M p n ≫ (homologyFunctor B n).map (τ.app M) := by
  simp only [functorTruncationCoupleHom_τD, functorTruncationCoupleι, ← Functor.map_comp,
    τ.naturality]
  rfl

/-- The map `Hⁿ(τ_M)` on the abutments sends the image filtration of `Hⁿ(F₁ M)` into the image
filtration of `Hⁿ(F₂ M)`. -/
lemma imageSubobject_functorTruncationCoupleFiltration_le (n p : ℤ) :
    imageSubobject (((functorTruncationCoupleFiltration F₁ M n).F p).arrow ≫
      (homologyFunctor B n).map (τ.app M)) ≤ (functorTruncationCoupleFiltration F₂ M n).F p := by
  dsimp only [functorTruncationCoupleFiltration, ExactCouple.abutmentFiltration]
  rw [← imageSubobject_comp_eq_of_epi (factorThruImageSubobject _), imageSubobject_arrow_comp_assoc,
    ← functorTruncationCoupleHom_τD_ι]
  exact imageSubobject_comp_le _ _

end Hom

end DerivedCategory.Plus
