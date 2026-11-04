/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Native.NativeComparisonCompatibleDescent
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-!
# Compatibility of totalized comparisons from their summands

Let `F : C₁ ⥤ C₂`, `F' : D₁ ⥤ D₂`, `N₁ : C₁ ⥤ D₁` and `N₂ : C₂ ⥤ D₂` be additive functors with an
isomorphism `a : N₁ ⋙ F' ≅ F ⋙ N₂`, where `D₁`, `D₂` are monoidal and `F'` is oplax monoidal.
Let `G₁`, `G₂` be bifunctors on `C₁`, `C₂`, and let `r : G₁(M, N) ⋙ F ≅ G₂(F M, F N)` and
`s_i : N_i (G_i(M, N)) ≅ N_i M ⊗ N_i N` be comparisons, with totalizations `tF`, `tN₁`, `tN₂` on
cochain complexes, given summand by summand by `r` and the `s_i`.

If on objects the comparison `N₂ (r) ≫ s₂` agrees with the comparison obtained from `s₁`, the
comonoidal structure `δ` of `F'` and `a`, then the same holds for the totalized comparisons
(`CategoryTheory.totalComparison_compatible_of_sheaf`): both sides are morphisms out of the
total complex `N₂ (F (Tot(P ⊗ T)))`, and they agree on each summand `N₂ (F (P^p ⊗ T^q))`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory

variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D₁] [Preadditive D₂]
  [MonoidalCategory D₁] [MonoidalCategory D₂] [MonoidalPreadditive D₁] [MonoidalPreadditive D₂]
  {F : C₁ ⥤ C₂} [F.Additive] {F' : D₁ ⥤ D₂} [F'.Additive] [F'.OplaxMonoidal]
  {N₁ : C₁ ⥤ D₁} [N₁.Additive] {N₂ : C₂ ⥤ D₂} [N₂.Additive]
  {G₁ : C₁ ⥤ C₁ ⥤ C₁} {G₂ : C₂ ⥤ C₂ ⥤ C₂}
  [G₁.PreservesZeroMorphisms] [∀ X, (G₁.obj X).PreservesZeroMorphisms]
  [G₂.PreservesZeroMorphisms] [∀ X, (G₂.obj X).PreservesZeroMorphisms]
  [∀ K L : CochainComplex C₁ ℤ, HomologicalComplex.HasMapBifunctor K L G₁ (.up ℤ)]
  [∀ K L : CochainComplex C₂ ℤ, HomologicalComplex.HasMapBifunctor K L G₂ (.up ℤ)]
  [∀ K L : CochainComplex D₁ ℤ, HomologicalComplex.HasMapBifunctor K L (curriedTensor D₁) (.up ℤ)]
  [∀ K L : CochainComplex D₂ ℤ, HomologicalComplex.HasMapBifunctor K L (curriedTensor D₂) (.up ℤ)]
  [∀ j : ℤ, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) F]
  [∀ j : ℤ, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) F']
  [∀ j : ℤ, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) N₁]
  [∀ j : ℤ, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) N₂]

/-- **Compatibility of totalized comparisons from their summands.** If the sheaf-level
comparison `N₂ (r) ≫ s₂` is the comparison obtained from `s₁`, the comonoidal structure of `F'`
and `a` (hypothesis `hS`), then the same holds for their totalizations `tF`, `tN₁`, `tN₂`,
given summand by summand by `r`, `s₁`, `s₂` (hypotheses `htF`, `htN₁`, `htN₂`); the totalization
of the comonoidal structure of `F'` is `HomologicalComplex.mapBifunctorComparison`. -/
theorem totalComparison_compatible_of_sheaf (a : N₁ ⋙ F' ≅ F ⋙ N₂)
    (r : Functor.uncurry.obj G₁ ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj G₂)
    (s₁ : Functor.uncurry.obj G₁ ⋙ N₁ ≅ N₁.prod N₁ ⋙ Functor.uncurry.obj (curriedTensor D₁))
    (s₂ : Functor.uncurry.obj G₂ ⋙ N₂ ≅ N₂.prod N₂ ⋙ Functor.uncurry.obj (curriedTensor D₂))
    (tF : Functor.uncurry.obj G₁.map₂CochainComplex ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      (F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj G₂.map₂CochainComplex)
    (tN₁ : Functor.uncurry.obj G₁.map₂CochainComplex ⋙ N₁.mapHomologicalComplex (.up ℤ) ≅
      (N₁.mapHomologicalComplex (.up ℤ)).prod (N₁.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (curriedTensor D₁).map₂CochainComplex)
    (tN₂ : Functor.uncurry.obj G₂.map₂CochainComplex ⋙ N₂.mapHomologicalComplex (.up ℤ) ≅
      (N₂.mapHomologicalComplex (.up ℤ)).prod (N₂.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (curriedTensor D₂).map₂CochainComplex)
    (htF : ∀ (P T : CochainComplex C₁ ℤ) (p q n : ℤ) (h : p + q = n),
      F.map (HomologicalComplex.ιMapBifunctor P T G₁ (.up ℤ) p q n h) ≫
          ((tF.app (P, T)).hom).f n =
        (r.app (P.X p, T.X q)).hom ≫ HomologicalComplex.ιMapBifunctor
          ((F.mapHomologicalComplex (.up ℤ)).obj P) ((F.mapHomologicalComplex (.up ℤ)).obj T)
          G₂ (.up ℤ) p q n h)
    (htN₁ : ∀ (P T : CochainComplex C₁ ℤ) (p q n : ℤ) (h : p + q = n),
      N₁.map (HomologicalComplex.ιMapBifunctor P T G₁ (.up ℤ) p q n h) ≫
          ((tN₁.app (P, T)).hom).f n =
        (s₁.app (P.X p, T.X q)).hom ≫ HomologicalComplex.ιMapBifunctor
          ((N₁.mapHomologicalComplex (.up ℤ)).obj P) ((N₁.mapHomologicalComplex (.up ℤ)).obj T)
          (curriedTensor D₁) (.up ℤ) p q n h)
    (htN₂ : ∀ (P T : CochainComplex C₂ ℤ) (p q n : ℤ) (h : p + q = n),
      N₂.map (HomologicalComplex.ιMapBifunctor P T G₂ (.up ℤ) p q n h) ≫
          ((tN₂.app (P, T)).hom).f n =
        (s₂.app (P.X p, T.X q)).hom ≫ HomologicalComplex.ιMapBifunctor
          ((N₂.mapHomologicalComplex (.up ℤ)).obj P) ((N₂.mapHomologicalComplex (.up ℤ)).obj T)
          (curriedTensor D₂) (.up ℤ) p q n h)
    (hS : ∀ M N : C₁, N₂.map (r.app (M, N)).hom ≫ (s₂.app (F.obj M, F.obj N)).hom =
      a.inv.app ((G₁.obj M).obj N) ≫ F'.map (s₁.app (M, N)).hom ≫
        Functor.OplaxMonoidal.δ F' (N₁.obj M) (N₁.obj N) ≫ (a.hom.app M ⊗ₘ a.hom.app N))
    (P T : CochainComplex C₁ ℤ) :
    (N₂.mapHomologicalComplex (.up ℤ)).map (tF.app (P, T)).hom ≫
        (tN₂.app (((F.mapHomologicalComplex (.up ℤ)).obj P),
          ((F.mapHomologicalComplex (.up ℤ)).obj T))).hom =
      (Functor.mapHomologicalComplexSquareIso a (.up ℤ)).inv.app _ ≫
        (F'.mapHomologicalComplex (.up ℤ)).map (tN₁.app (P, T)).hom ≫
        HomologicalComplex.mapBifunctorComparison (Functor.OplaxMonoidal.δNatTrans F') (.up ℤ)
          ((N₁.mapHomologicalComplex (.up ℤ)).obj P) ((N₁.mapHomologicalComplex (.up ℤ)).obj T) ≫
        (((curriedTensor D₂).map₂CochainComplex.map
          ((Functor.mapHomologicalComplexSquareIso a (.up ℤ)).hom.app P)).app _ ≫
        ((curriedTensor D₂).map₂CochainComplex.obj _).map
          ((Functor.mapHomologicalComplexSquareIso a (.up ℤ)).hom.app T)) := by
  sorry

end CategoryTheory
