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

/-- The final object of the small étale site of `Z`, the identity of `Z`. -/
noncomputable abbrev Etale.finalObject (Z : Scheme.{u}) : Z.Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 Z) (inferInstance : Etale (𝟙 Z))
/-- Étale cohomology `Hᵠ(Z, N) = Hom(Λ_Z[0], N[0]⟦q⟧)` of a quasi-compact and quasi-separated
scheme commutes with filtered colimits: the case of the final object of
`AlgebraicGeometry.Etale.preservesColimitsOfShape_cohomology` (blueprint
`lem-weil-pbc-cohomology-filtered-colimit`, a node of `sk-prop-h2`). The abelian version is
`AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`. -/
@[stacks 03Q6]
theorem Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject (Z : Scheme.{u})
    [CompactSpace Z] [QuasiSeparatedSpace Z] (q : ℤ) (J : Type u) [SmallCategory J]
    [IsFiltered J] :
    PreservesColimitsOfShape J
      (Etale.shiftedHomFunctor Λ ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) q) :=
  have : CompactSpace (Etale.finalObject Z).left := ‹CompactSpace Z›
  have : QuasiSeparatedSpace (Etale.finalObject Z).left := ‹QuasiSeparatedSpace Z›
  Etale.preservesColimitsOfShape_cohomology Λ (Etale.finalObject Z) q J

/-- An isomorphism `A ≅ A'` identifies the functors `N ↦ Hom(A[0], N[0]⟦q⟧)` and
`N ↦ Hom(A'[0], N[0]⟦q⟧)`. -/
noncomputable def Etale.shiftedHomFunctorMapIso {Z : Scheme.{u}}
    {A A' : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : A ≅ A') (q : ℤ) :
    Etale.shiftedHomFunctor Λ A q ≅ Etale.shiftedHomFunctor Λ A' q :=
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q)
    (preadditiveCoyoneda.mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso e).symm.op)

section Pullback

variable {X Y : Scheme.{u}} (h : Y ⟶ X)

/-- An étale `Y`-scheme `W`, as an étale scheme over itself extended along its structure
morphism, is `W`. -/
noncomputable def Etale.overMapFinalObjectIso (W : Y.Etale) :
    (MorphismProperty.Over.map ⊤ W.prop).obj (Etale.finalObject W.left) ≅ W :=
  MorphismProperty.Over.isoMk (Iso.refl _) rfl

/-- The functor `N ↦ Hom((h^* Λ[W])[0], N[0]⟦q⟧)` is the cohomology functor of `W ×_X Y`
precomposed with restriction. -/
noncomputable def Etale.shiftedHomFunctorUpperStarFreeSheafIso (W : X.Etale) (q : ℤ) :
    Etale.shiftedHomFunctor Λ ((h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W)) q ≅
      (((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).hom)^*[ModuleCat.{u + 1} Λ] ⋙
        Etale.shiftedHomFunctor Λ
          ((Etale.freeSheaf Λ ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left).obj
            (Etale.finalObject _)) q :=
  Etale.shiftedHomFunctorMapIso Λ (Etale.upperStarFreeSheafIso Λ h W ≪≫
    (Etale.freeSheaf Λ Y).mapIso (Etale.overMapFinalObjectIso _).symm ≪≫
    (Etale.etaleLowerShriekFreeSheafIso Λ _ ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).prop
      (Etale.finalObject _)).symm) q ≪≫
  Etale.etaleLowerShriekShiftedHomIso Λ _ ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).prop
    _ q

/-- For `h` quasi-compact and quasi-separated and `W` affine, the functor
`N ↦ Hom((h^* Λ[W])[0], N[0]⟦q⟧) = Hᵠ(W ×_X Y, N)` commutes with filtered colimits. -/
theorem Etale.preservesColimitsOfShape_shiftedHomFunctor_upperStarFreeSheaf [QuasiCompact h]
    [QuasiSeparated h] (W : X.Etale) [IsAffine W.left] (q : ℤ) (J : Type u) [SmallCategory J]
    [IsFiltered J] :
    PreservesColimitsOfShape J (Etale.shiftedHomFunctor Λ
      ((h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W)) q) := by
  have : IsAffine ((𝟭 Scheme).obj W.left) := ‹IsAffine W.left›
  have : CompactSpace ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left :=
    QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.fst W.hom h)
  have : QuasiSeparatedSpace ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left :=
    quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.fst W.hom h)
  have hN := Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject Λ
    ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left q J
  have : PreservesColimitsOfSize.{u, u}
      ((((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).hom)^*[ModuleCat.{u + 1} Λ]) :=
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) _).leftAdjoint_preservesColimits
  have hN2 : PreservesColimitsOfShape J (Etale.shiftedHomFunctor Λ ((Etale.freeSheaf Λ
      ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left).obj (Etale.finalObject _)) q) :=
    hN
  have hA : PreservesColimitsOfShape J
      ((((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).hom)^*[ModuleCat.{u + 1} Λ]) :=
    inferInstance
  have h3 : PreservesColimitsOfShape J
      ((((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).hom)^*[ModuleCat.{u + 1} Λ] ⋙
        Etale.shiftedHomFunctor Λ ((Etale.freeSheaf Λ
          ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left).obj (Etale.finalObject _)) q) :=
    ⟨fun {K} ↦ ⟨fun {c} hc ↦ ⟨(hN2.preservesColimit (K := K ⋙ _)).preserves
      ((hA.preservesColimit (K := K)).preserves hc).some |>.some⟩⟩⟩
  exact preservesColimitsOfShape_of_natIso
    (Etale.shiftedHomFunctorUpperStarFreeSheafIso Λ h W q).symm

end Pullback

end AlgebraicGeometry
