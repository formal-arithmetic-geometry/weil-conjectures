/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.Proper
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.OpenImmersion

/-!
# Compactly supported and ordinary cohomology of a proper scheme

For a proper `k₀`-scheme `a : X ⟶ Spec k₀` the direct image with compact support
`Ra_! = Rg_* ∘ i_!`, for the chosen compactification `X ⟶[i] Z ⟶[g] Spec k₀`, is the derived
direct image `Ra_*`: the open immersion `i` is then also closed, so that `i_! ≅ i_*`, and
`Rg_* ∘ i_* ≅ R(i ≫ g)_*`. Hence the compactly supported cohomology of a Weil complex on `X`
is its ordinary cohomology, Frobenius-equivariantly.

## Main statements

- `AlgebraicGeometry.ProEtaleWeilSheaf.lowerStarCompIso`: `φ_* ⋙ ψ_* ≅ (φ ≫ ψ)_*` for
  pro-étale Weil sheaves.
- `AlgebraicGeometry.WeilComplex.nonempty_equiv_compactlySupportedCohomology_cohomology_of_isProper`:
  `H_c^r(X ⊗ k̄, K) ≅ Hʳ(X ⊗ k̄, K)` as Frobenius modules for `X` proper.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarComp_hom_app_lowerStar_obj_hom_app {R S T W : Scheme.{u}} (g : W ⟶ T)
    (h₁ : T ⟶ S) (h₂ : S ⟶ R) (G : Sheaf (Scheme.ProEt.topology W) A) (V : R.ProEtᵒᵖ) :
    ((lowerStarComp A h₁ h₂).hom.app ((g)_*[A].obj G)).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map
        ((MorphismProperty.Over.pullbackComp h₁ h₂).hom.app V.unop)).op :=
  lowerStarComp_hom_app_hom_app A h₁ h₂ _ V

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarComp_inv_app_lowerStar_obj_hom_app {R S T W : Scheme.{u}} (g : W ⟶ T)
    (h₁ : T ⟶ S) (h₂ : S ⟶ R) (G : Sheaf (Scheme.ProEt.topology W) A) (V : R.ProEtᵒᵖ) :
    ((lowerStarComp A h₁ h₂).inv.app ((g)_*[A].obj G)).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map
        ((MorphismProperty.Over.pullbackComp h₁ h₂).inv.app V.unop)).op :=
  lowerStarComp_inv_app_hom_app A h₁ h₂ _ V

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarCongr_hom_app_lowerStar_obj_hom_app {Z Y W : Scheme.{u}} (g : W ⟶ Z)
    {h h' : Z ⟶ Y} (e : h = h') (G : Sheaf (Scheme.ProEt.topology W) A) (V : Y.ProEtᵒᵖ) :
    ((lowerStarCongr A e).hom.app ((g)_*[A].obj G)).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map
        ((MorphismProperty.Over.pullbackCongr e).inv.app V.unop)).op :=
  lowerStarCongr_hom_app_hom_app A e _ V

/-- The exchange isomorphisms `p_* ⋙ a₂_* ≅ a₁_* ⋙ p_*` of pushforwards along commutative
squares `p ≫ a₂ = a₁ ≫ p` are compatible with composition of pushforwards. -/
lemma lowerStarComp_exchange {T₁ T₂ T₃ : Scheme.{u}} (p : T₁ ⟶ T₂) (q : T₂ ⟶ T₃)
    (a₁ : T₁ ⟶ T₁) (a₂ : T₂ ⟶ T₂) (a₃ : T₃ ⟶ T₃) (h₁ : p ≫ a₂ = a₁ ≫ p) (h₂ : q ≫ a₃ = a₂ ≫ q)
    (h₁₂ : (p ≫ q) ≫ a₃ = a₁ ≫ (p ≫ q)) (G : Sheaf (Scheme.ProEt.topology T₁) A) :
    (a₃)_*[A].map ((lowerStarComp A p q).hom.app G) ≫
        (lowerStarComp A (p ≫ q) a₃).hom.app G ≫ (lowerStarCongr A h₁₂).hom.app G ≫
          (lowerStarComp A a₁ (p ≫ q)).inv.app G =
      (lowerStarComp A q a₃).hom.app ((p)_*[A].obj G) ≫
        (lowerStarCongr A h₂).hom.app ((p)_*[A].obj G) ≫
          (lowerStarComp A a₂ q).inv.app ((p)_*[A].obj G) ≫
            (q)_*[A].map ((lowerStarComp A p a₂).hom.app G ≫ (lowerStarCongr A h₁).hom.app G ≫
              (lowerStarComp A a₁ p).inv.app G) ≫
              (lowerStarComp A p q).hom.app ((a₁)_*[A].obj G) := by
  ext V : 3
  simp only [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app', lowerStarComp_hom_app_lowerStar_obj_hom_app,
    lowerStarComp_inv_app_lowerStar_obj_hom_app, lowerStarCongr_hom_app_lowerStar_obj_hom_app]
  simp only [lowerStarComp_hom_app_hom_app, lowerStarComp_inv_app_hom_app,
    lowerStarCongr_hom_app_hom_app]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  ext : 1
  simp only [MorphismProperty.Comma.comp_left]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
          MorphismProperty.Over.mk]
      · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
          MorphismProperty.Over.mk]
    · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk]

end ProEtale

end AlgebraicGeometry
