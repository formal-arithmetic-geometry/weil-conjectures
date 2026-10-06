/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc

/-!
# Truncations and homology in the bounded below derived category

Let `C` be an abelian category. For the canonical t-structure
`DerivedCategory.Plus.TStructure.t` on `DerivedCategory.Plus C`, we show that the truncation
morphisms induce isomorphisms in homology in the expected range of degrees, and that
`τ_{≥ q} τ_{< q + 1} X` is isomorphic to the single complex on `H^q(X)` in degree `q`.

## Main statements

- `DerivedCategory.Plus.isIso_homologyFunctor_map_truncLTι_app`: `H^n(τ_{<a} X) ≅ H^n(X)`
  for `n < a`.
- `DerivedCategory.Plus.isIso_homologyFunctor_map_truncGEπ_app`: `H^n(X) ≅ H^n(τ_{≥a} X)`
  for `a ≤ n`.
- `DerivedCategory.Plus.nonempty_eTruncGE_eTruncLT_iso_singleFunctor`:
  `τ_{≥ q} τ_{< q + 1} X ≅ H^q(X)[-q]`.

-/

@[expose] public section

open CategoryTheory Category Limits Triangulated Pretriangulated

open DerivedCategory.Plus.TStructure (t)

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

namespace DerivedCategory.Plus

/-- `H^n(τ_{<a} X) ⟶ H^n(X)` is an isomorphism for `n < a`. -/
lemma isIso_homologyFunctor_map_truncLTι_app (X : Plus C) (a n : ℤ) (h : n < a) :
    IsIso ((homologyFunctor C n).map ((t.truncLTι a).app X)) := by
  have hT := t.triangleLTGE_distinguished a X
  have h₁ : Mono ((homologyFunctor C n).map ((t.truncLTι a).app X)) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff _ hT (n - 1) n
      (by lia)).2 (IsZero.eq_of_src (isZero_homology_of_isGE _ a _ (by lia)) _ _)
  have h₂ : Epi ((homologyFunctor C n).map ((t.truncLTι a).app X)) :=
    ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff _ hT n).2
      (IsZero.eq_of_tgt (isZero_homology_of_isGE _ a _ h) _ _)
  exact isIso_of_mono_of_epi _

/-- `H^n(X) ⟶ H^n(τ_{≥a} X)` is an isomorphism for `a ≤ n`. -/
lemma isIso_homologyFunctor_map_truncGEπ_app (X : Plus C) (a n : ℤ) (h : a ≤ n) :
    IsIso ((homologyFunctor C n).map ((t.truncGEπ a).app X)) := by
  have hT := t.triangleLTGE_distinguished a X
  have h₁ : Mono ((homologyFunctor C n).map ((t.truncGEπ a).app X)) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₂_iff _ hT n).2
      (IsZero.eq_of_src (isZero_homology_of_isLE _ (a - 1) _ (by lia)) _ _)
  have h₂ : Epi ((homologyFunctor C n).map ((t.truncGEπ a).app X)) :=
    ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff _ hT n (n + 1) rfl).2
      (IsZero.eq_of_tgt (isZero_homology_of_isLE _ (a - 1) _ (by lia)) _ _)
  exact isIso_of_mono_of_epi _

/-- For `q : ℤ`, the object `τ_{≥ q} τ_{< q + 1} X` (written with the `EInt`-indexed
truncations, as in `t.spectralObject X`) is isomorphic to the single complex
`(singleFunctor C q).obj (H^q X)`. -/
lemma nonempty_eTruncGE_eTruncLT_iso_singleFunctor (X : Plus C) (q : ℤ) :
    Nonempty ((t.eTruncGE.obj (q : EInt)).obj ((t.eTruncLT.obj ((q + 1 : ℤ) : EInt)).obj X) ≅
      (singleFunctor C q).obj ((homologyFunctor C q).obj X)) := by
  let Y := (t.truncGE q).obj ((t.truncLT (q + 1)).obj X)
  obtain ⟨A, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (ι.obj Y) q
  let e' : Y ≅ (singleFunctor C q).obj A := ι.preimageIso e
  have := isIso_homologyFunctor_map_truncGEπ_app ((t.truncLT (q + 1)).obj X) q q le_rfl
  have := isIso_homologyFunctor_map_truncLTι_app X (q + 1) q (by lia)
  exact ⟨e' ≪≫ (singleFunctor C q).mapIso
    (((singleFunctorCompHomologyFunctorIso C q).app A).symm ≪≫
      (homologyFunctor C q).mapIso e'.symm ≪≫
      (asIso ((homologyFunctor C q).map ((t.truncGEπ q).app _))).symm ≪≫
      asIso ((homologyFunctor C q).map ((t.truncLTι (q + 1)).app X)))⟩

end DerivedCategory.Plus
