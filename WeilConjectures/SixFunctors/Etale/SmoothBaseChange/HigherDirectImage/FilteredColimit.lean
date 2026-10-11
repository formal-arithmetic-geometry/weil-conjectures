/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

/-!
# Higher direct images commute with filtered colimits
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

open Scheme Etale

section FreeSheaf

variable {X Y : Scheme.{u}}

/-- Maps out of `h^* Λ[W]` are maps out of `Λ[W ×_X Y]`: both are sections over `W ×_X Y`. -/
noncomputable def Etale.upperStarFreeSheafHomEquiv (h : Y ⟶ X) (W : X.Etale)
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W) ⟶ G) ≃
      ((Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W) ⟶ G) :=
  (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).homEquiv _ _).trans
    (Etale.freeSheafHomEquiv Λ W _)).trans (Etale.freeSheafHomEquiv Λ _ G).symm

lemma Etale.upperStarFreeSheafHomEquiv_comp (h : Y ⟶ X) (W : X.Etale)
    {G G' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : (h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W) ⟶ G) (g : G ⟶ G') :
    Etale.upperStarFreeSheafHomEquiv Λ h W G' (f ≫ g) =
      Etale.upperStarFreeSheafHomEquiv Λ h W G f ≫ g := by
  apply (Etale.freeSheafHomEquiv Λ _ G').injective
  simp only [Etale.upperStarFreeSheafHomEquiv, Equiv.trans_apply,
    Etale.freeSheafHomEquiv_comp, Adjunction.homEquiv_naturality_right]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- The pullback of a free sheaf is free: `h^* Λ[W] ≅ Λ[W ×_X Y]`, both corepresenting the
functor `G ↦ G(W ×_X Y)`. -/
noncomputable def Etale.upperStarFreeSheafIso (h : Y ⟶ X) (W : X.Etale) :
    (h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W) ≅
      (Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W) :=
  (Coyoneda.fullyFaithful.preimageIso (NatIso.ofComponents
    (fun G ↦ (Etale.upperStarFreeSheafHomEquiv Λ h W G).toIso)
    (fun g ↦ by
      ext f
      exact Etale.upperStarFreeSheafHomEquiv_comp Λ h W f g))).unop.symm

/-- Maps out of `v_! Λ[T]` are maps out of `Λ[T → V → Y]`, for `v : V ⟶ Y` étale. -/
noncomputable def Etale.etaleLowerShriekFreeSheafHomEquiv {V : Scheme.{u}} (v : V ⟶ Y)
    (hv : Etale v) (T : V.Etale) (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj ((Etale.freeSheaf Λ V).obj T) ⟶
      G) ≃ ((Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.map ⊤ hv).obj T) ⟶ G) :=
  (((Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) v hv).homEquiv _ _).trans
    (((Iso.refl _).homCongr
      ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) v hv).app G)).trans
    (Etale.freeSheafHomEquiv Λ T _))).trans (Etale.freeSheafHomEquiv Λ _ G).symm

lemma Etale.etaleLowerShriekFreeSheafHomEquiv_comp {V : Scheme.{u}} (v : V ⟶ Y)
    (hv : Etale v) (T : V.Etale) {G G' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj
      ((Etale.freeSheaf Λ V).obj T) ⟶ G) (g : G ⟶ G') :
    Etale.etaleLowerShriekFreeSheafHomEquiv Λ v hv T G' (f ≫ g) =
      Etale.etaleLowerShriekFreeSheafHomEquiv Λ v hv T G f ≫ g := by
  apply (Etale.freeSheafHomEquiv Λ _ G').injective
  simp only [Etale.etaleLowerShriekFreeSheafHomEquiv, Equiv.trans_apply,
    Etale.freeSheafHomEquiv_comp, Iso.homCongr_apply, Iso.refl_inv,
    Category.id_comp, Adjunction.homEquiv_naturality_right, Category.assoc, Iso.app_hom,
    NatTrans.naturality]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- Extension by zero of a free sheaf along an étale morphism `v : V ⟶ Y` is free:
`v_! Λ[T] ≅ Λ[T → V → Y]`, both corepresenting the functor `G ↦ G(T → V → Y)`. -/
noncomputable def Etale.etaleLowerShriekFreeSheafIso {V : Scheme.{u}} (v : V ⟶ Y) (hv : Etale v)
    (T : V.Etale) :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj ((Etale.freeSheaf Λ V).obj T) ≅
      (Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.map ⊤ hv).obj T) :=
  (Coyoneda.fullyFaithful.preimageIso (NatIso.ofComponents
    (fun G ↦ (Etale.etaleLowerShriekFreeSheafHomEquiv Λ v hv T G).toIso)
    (fun g ↦ by
      ext f
      exact Etale.etaleLowerShriekFreeSheafHomEquiv_comp Λ v hv T f g))).unop.symm

end FreeSheaf
section Restriction

variable {Y V : Scheme.{u}} (v : V ⟶ Y) (hv : Etale v)

instance Etale.additive_etaleLowerShriek :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).Additive :=
  (Etale.etaleLowerShriekUpperStarAdjunction _ v hv).left_adjoint_additive

instance Etale.isLeftAdjoint_etaleLowerShriek :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).IsLeftAdjoint :=
  (Etale.etaleLowerShriekUpperStarAdjunction _ v hv).isLeftAdjoint

instance Etale.preservesFiniteLimits_etaleLowerShriek_instance :
    PreservesFiniteLimits (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv) :=
  Etale.preservesFiniteLimits_etaleLowerShriek Λ v hv

/-- The derived adjunction `v_! ⊣ v^*` on bounded below derived categories, for an étale `v`:
both functors are exact. -/
noncomputable def Etale.derivedEtaleLowerShriekUpperStarAdjunctionPlus :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).mapDerivedCategoryPlus ⊣
      ((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus :=
  ((Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) v hv).derivedPlus).ofNatIsoRight
    (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus _)

/-- The functor `N ↦ Hom(A[0], N[0]⟦q⟧)` on sheaves of `Λ`-modules on `Z_ét`; for `A = Λ` it is
the étale cohomology `N ↦ Hᵠ(Z, N)` with coefficients in `Λ`-modules. -/
noncomputable abbrev Etale.shiftedHomFunctor {Z : Scheme.{u}}
    (A : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ AddCommGrpCat.{u + 1} :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
    preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor _ 0).obj A))

/-- `v^*` commutes with `N ↦ N[0]⟦q⟧`. -/
noncomputable def Etale.upperStarSingleShiftIso (q : ℤ) :
    DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
        ((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ≅
      (v)^*[ModuleCat.{u + 1} Λ] ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q :=
  Functor.isoWhiskerLeft _ (((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.commShiftIso q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0)
      (shiftFunctor _ q) ≪≫ Functor.associator _ _ _

/-- The derived adjunction `v_! ⊣ v^*` on shifted maps out of a sheaf placed in degree `0`:
`Hom((v_! M)[0], N[0]⟦q⟧) ≃ Hom(M[0], (v^* N)[0]⟦q⟧)`. -/
noncomputable def Etale.etaleLowerShriekShiftedHomEquiv
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((Etale.shiftedHomFunctor Λ ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj M) q).obj
      N) ≃+ ((Etale.shiftedHomFunctor Λ M q).obj ((v)^*[ModuleCat.{u + 1} Λ].obj N)) :=
  let i₁ := ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).mapDerivedCategoryPlusSingleFunctor
    0).app M
  let i₂ := (Etale.upperStarSingleShiftIso Λ v hv q).app N
  let adj := Etale.derivedEtaleLowerShriekUpperStarAdjunctionPlus Λ v hv
  AddEquiv.mk'
    { toFun f := adj.homEquiv _ _ (i₁.hom ≫ f) ≫ i₂.hom
      invFun g := i₁.inv ≫ (adj.homEquiv _ _).symm (g ≫ i₂.inv)
      left_inv f := by simp
      right_inv g := by simp }
    (fun a b ↦ by
      simp only [Equiv.coe_fn_mk, Adjunction.homEquiv_unit]
      erw [Preadditive.comp_add, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp])

lemma Etale.etaleLowerShriekShiftedHomEquiv_apply
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (f : (Etale.shiftedHomFunctor Λ ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj M)
      q).obj N) :
    Etale.etaleLowerShriekShiftedHomEquiv Λ v hv M q N f =
      (Etale.derivedEtaleLowerShriekUpperStarAdjunctionPlus Λ v hv).homEquiv _ _
        ((((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).mapDerivedCategoryPlusSingleFunctor
          0).app M).hom ≫ f) ≫ ((Etale.upperStarSingleShiftIso Λ v hv q).app N).hom :=
  rfl

/-- The derived adjunction `v_! ⊣ v^*` on shifted maps out of a sheaf placed in degree `0`,
naturally in the target. -/
noncomputable def Etale.etaleLowerShriekShiftedHomIso
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    Etale.shiftedHomFunctor Λ ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj M) q ≅
      (v)^*[ModuleCat.{u + 1} Λ] ⋙ Etale.shiftedHomFunctor Λ M q :=
  NatIso.ofComponents
    (fun N ↦ (Etale.etaleLowerShriekShiftedHomEquiv Λ v hv M q N).toAddCommGrpIso)
    (fun {N N'} g ↦ by
      ext f
      change Etale.etaleLowerShriekShiftedHomEquiv Λ v hv M q N'
          (f ≫ (shiftFunctor _ q).map ((DerivedCategory.Plus.singleFunctor _ 0).map g)) =
        Etale.etaleLowerShriekShiftedHomEquiv Λ v hv M q N f ≫ (shiftFunctor _ q).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map ((v)^*[ModuleCat.{u + 1} Λ].map g))
      rw [Etale.etaleLowerShriekShiftedHomEquiv_apply, Etale.etaleLowerShriekShiftedHomEquiv_apply,
        ← Category.assoc, Adjunction.homEquiv_naturality_right, Category.assoc, Category.assoc]
      congr 1
      exact (Etale.upperStarSingleShiftIso Λ v hv q).hom.naturality g)

end Restriction

end AlgebraicGeometry
