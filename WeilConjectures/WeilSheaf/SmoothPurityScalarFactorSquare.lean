/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarSquare
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Scalar equivariance through a faithful comparison functor -/

@[expose] public section

namespace CategoryTheory

lemma purity_scalarFactorSquare
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    (F : C ⥤ D) [F.Faithful] [F.Additive]
    (Q : C ⥤ C) (q : D ⥤ D) (τ : F ⋙ q ≅ Q ⋙ F)
    {M N : C} {A B : D} (u : A ≅ F.obj M) (v : B ≅ F.obj N)
    (a : q.obj A ⟶ A) (b : q.obj B ⟶ B)
    (a' : Q.obj M ⟶ M) (b' : Q.obj N ⟶ N)
    (e : A ⟶ B) (e' : M ⟶ N) (c : ℤ)
    (ha : q.map u.hom ≫ τ.hom.app M ≫ F.map a' = a ≫ u.hom)
    (hb : q.map v.hom ≫ τ.hom.app N ≫ F.map b' = b ≫ v.hom)
    (hu : u.hom ≫ F.map e' = e ≫ v.hom)
    (he : q.map e ≫ b = c • (a ≫ e)) :
    c • (a' ≫ e') = Q.map e' ≫ b' := by
  apply F.map_injective
  have hn := τ.hom.naturality e'
  dsimp only [Functor.comp_map] at hn
  have hf : (q.map u.hom ≫ τ.hom.app M) ≫ F.map (Q.map e') =
      q.map e ≫ (q.map v.hom ≫ τ.hom.app N) := by
    rw [Category.assoc, ← hn, ← q.map_comp_assoc, hu, q.map_comp, Category.assoc]
  simpa only [F.map_zsmul, F.map_comp] using
    purity_scalarSquare (q.map u.hom ≫ τ.hom.app M) (q.map v.hom ≫ τ.hom.app N)
      u.hom v.hom a b (F.map a') (F.map b') e (F.map e')
      (q.map e) (F.map (Q.map e')) c
      (by simpa only [Category.assoc] using ha)
      (by simpa only [Category.assoc] using hb) hu hf he

end CategoryTheory
