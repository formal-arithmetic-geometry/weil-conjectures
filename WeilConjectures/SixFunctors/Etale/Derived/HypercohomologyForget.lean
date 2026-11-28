/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionForget
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjectionFlat
import WeilConjectures.AlgebraicGeometry.RawModuleScalarSheafComposition
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-!
# Étale hypercohomology of bounded below complexes and the underlying abelian sheaves

Let `Λ` be a ring and `K` a bounded below complex of étale sheaves of `Λ`-modules on a scheme
`S`. For a scheme `p : Y ⟶ S` over `S`, the hypercohomology `Hᵠ(Y, p^* K)` computed with
`Λ`-coefficients is, as an abelian group, the hypercohomology of the pullback of the underlying
complex of abelian sheaves (`AlgebraicGeometry.Etale.cohomologyUpperStarForgetIso`), compatibly with
the restriction maps along morphisms of schemes over `S`
(`AlgebraicGeometry.Etale.forget_map_restrictOver_comp_cohomologyUpperStarForgetIso_hom`).

## Main definitions

- `AlgebraicGeometry.Etale.cohomologyUpperStarForgetIso`: the isomorphism
  `Hᵠ(Y, p^* K) ≅ Hᵠ(Y, p^* S_S K)` of abelian groups.

## Main results

- `AlgebraicGeometry.Etale.isIso_rightDerivedGlobalSectionsForget_app`: the comparison of
  derived global sections is an isomorphism on bounded below complexes.
- `AlgebraicGeometry.Etale.forget_map_restrictOver_comp_cohomologyUpperStarForgetIso_hom`: the
  comparison is compatible with the restriction maps.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The comparison `RΓ(X, M) ⟶ RΓ(X, S_X M)` of derived global sections is an isomorphism at a
bounded below complex `M`: on a bounded below complex of injective sheaves of `Λ`-modules, the
underlying abelian sheaves are acyclic for global sections. -/
lemma isIso_rightDerivedGlobalSectionsForget_app (X : Scheme.{u})
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (a : ℤ)
    [M.IsGE a] : IsIso ((rightDerivedGlobalSectionsForget Λ X).app M) := by
  obtain ⟨C, _, ⟨e⟩⟩ := M.exists_iso_Q_obj_of_isGE a
  obtain ⟨I, ι, _, hI, _⟩ := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective C a
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  have : IsIso (DerivedCategory.Q.map ι) := inferInstance
  let e' : M ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) :=
    e ≪≫ asIso (DerivedCategory.Q.map ι) ≪≫ ((DerivedCategory.quotientCompQhIso _).app I).symm
  rw [NatTrans.isIso_app_iff_of_iso _ e']
  refine Functor.isIso_rightDerivedFunctorBaseChange_app (globalSectionsForgetIso Λ X) I ?_
  have : CochainComplex.IsStrictlyGE
      (((moduleAbelianForget Λ X).mapHomologicalComplex (.up ℤ)).obj I) a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact (moduleAbelianForget Λ X).map_isZero (I.isZero_of_isStrictlyGE a n hn)
  exact Functor.isIso_rightDerivedFunctorUnit_app_of_isStrictlyGE _
    (((moduleAbelianForget Λ X).mapHomologicalComplex (.up ℤ)).obj I) a
    (fun n k ↦ Scheme.isZero_rightDerived_globalSections_forget_of_injective X Λ (I.X n) k)

/-- The comparison isomorphisms of derived pullbacks `mapDerivedUpperStarForgetIso` are compatible
with the composition isomorphisms `(f ≫ p_Z)^* ≅ p_Z^* ⋙ f^*` of derived pullbacks. -/
lemma mapDerivedUpperStarForgetIso_inv_app_comp {S Y Z : Scheme.{u}} (pY : Y ⟶ S) (pZ : Z ⟶ S)
    (f : Y ⟶ Z) (hf : f ≫ pZ = pY)
    (K : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (moduleAbelianForget Λ Y).mapDerivedCategory.map
        ((Functor.mapDerivedCategoryTriangleIso
          (upperStarComp (ModuleCat.{u + 1} Λ) f pZ pY hf.symm)).inv.app K) ≫
      (mapDerivedUpperStarForgetIso Λ pY).inv.app K =
    (mapDerivedUpperStarForgetIso Λ f).inv.app
        (((pZ)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K) ≫
      ((f)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategory.map
        ((mapDerivedUpperStarForgetIso Λ pZ).inv.app K) ≫
      (Functor.mapDerivedCategoryTriangleIso
        (upperStarComp AddCommGrpCat.{u + 1} f pZ pY hf.symm)).inv.app
          ((moduleAbelianForget Λ S).mapDerivedCategory.obj K) := by
  have H := Functor.mapDerivedCategorySquareIso_hom_app_comp (moduleAbelianUpperStarIso Λ pZ)
    (moduleAbelianUpperStarIso Λ f) (moduleAbelianUpperStarIso Λ pY)
    (upperStarComp AddCommGrpCat.{u + 1} f pZ pY hf.symm)
    (upperStarComp (ModuleCat.{u + 1} Λ) f pZ pY hf.symm)
    (fun X ↦ rawModuleScalar_sheaf_composition Λ f pZ pY hf X) K
  unfold mapDerivedUpperStarForgetIso
  rw [← cancel_epi ((Functor.mapDerivedCategoryTriangleIso
      (upperStarComp AddCommGrpCat.{u + 1} f pZ pY hf.symm)).hom.app
        ((moduleAbelianForget Λ S).mapDerivedCategory.obj K) ≫
      ((f)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso (moduleAbelianUpperStarIso Λ pZ)).hom.app K) ≫
      (Functor.mapDerivedCategorySquareIso (moduleAbelianUpperStarIso Λ f)).hom.app
        (((pZ)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K))]
  simp only [Category.assoc]
  rw [← reassoc_of% H]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  rfl

/-- For a morphism `f : Y ⟶ Z` of schemes over `S` and `K ∈ D(S_ét, Λ)`, the restriction map
`RΓ(Z, K|_Z) ⟶ RΓ(Y, K|_Y)` commutes with the comparison of derived global sections with those of
the underlying complexes of abelian sheaves. -/
lemma rightDerivedGlobalSectionsForget_restrictOver {S Y Z : Scheme.{u}} (pY : Y ⟶ S)
    (pZ : Z ⟶ S) (f : Y ⟶ Z) (hf : f ≫ pZ = pY)
    (K : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategory.map
        (globalSectionsRestriction f (((pZ)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K) ≫
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
            ((Functor.mapDerivedCategoryTriangleIso
              (upperStarComp (ModuleCat.{u + 1} Λ) f pZ pY hf.symm)).inv.app K)) ≫
      (rightDerivedGlobalSectionsForget Λ Y).app
        (((pY)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K) ≫
      (rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
        ((mapDerivedUpperStarForgetIso Λ pY).inv.app K) =
    (rightDerivedGlobalSectionsForget Λ Z).app
        (((pZ)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K) ≫
      (rightDerivedGlobalSections AddCommGrpCat.{u + 1} Z).map
        ((mapDerivedUpperStarForgetIso Λ pZ).inv.app K) ≫
      globalSectionsRestriction f (((pZ)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategory.obj
        ((moduleAbelianForget Λ S).mapDerivedCategory.obj K)) ≫
      (rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
        ((Functor.mapDerivedCategoryTriangleIso
          (upperStarComp AddCommGrpCat.{u + 1} f pZ pY hf.symm)).inv.app
            ((moduleAbelianForget Λ S).mapDerivedCategory.obj K)) := by
  have h₁ := (rightDerivedGlobalSectionsForget Λ Y).naturality
    ((Functor.mapDerivedCategoryTriangleIso
      (upperStarComp (ModuleCat.{u + 1} Λ) f pZ pY hf.symm)).inv.app K)
  have h₂ := globalSectionsRestriction_naturality f ((mapDerivedUpperStarForgetIso Λ pZ).inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at h₁
  rw [Functor.map_comp, Category.assoc, reassoc_of% h₁, ← Functor.map_comp,
    mapDerivedUpperStarForgetIso_inv_app_comp Λ pY pZ f hf K, Functor.map_comp, Functor.map_comp,
    reassoc_of% (globalSectionsRestriction_forget Λ f
      (((pZ)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K)), reassoc_of% h₂]

/-- The isomorphism `Hᵠ(Y, p^* K) ≅ Hᵠ(Y, p^* S_S K)` of abelian groups between the
hypercohomology of the pullback of a bounded below complex `K` of étale sheaves of `Λ`-modules on
`S` and that of the pullback of its underlying complex of abelian sheaves. -/
noncomputable def cohomologyUpperStarForgetIso {S Y : Scheme.{u}} (p : Y ⟶ S)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (q : ℤ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
        ((cohomology (ModuleCat.{u + 1} Λ) Y q).obj
          (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K.obj)) ≅
      (cohomology AddCommGrpCat.{u + 1} Y q).obj
        (((p)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategory.obj
          ((moduleAbelianForget Λ S).mapDerivedCategory.obj K.obj)) :=
  have : IsIso ((rightDerivedGlobalSectionsForget Λ Y).app
      (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K.obj)) := by
    obtain ⟨a, ha⟩ := K.property
    have : K.obj.IsGE a := ha
    have := ((p)^*[ModuleCat.{u + 1} Λ]).isGE_mapDerivedCategory_obj K.obj a
    exact isIso_rightDerivedGlobalSectionsForget_app Λ Y _ a
  (Functor.mapDerivedCategoryHomologyFunctorIso
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) q).app
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj
      (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K.obj)) ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).mapIso
      (asIso ((rightDerivedGlobalSectionsForget Λ Y).app
        (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K.obj))) ≪≫
    (cohomology AddCommGrpCat.{u + 1} Y q).mapIso
      ((mapDerivedUpperStarForgetIso Λ p).symm.app K.obj)

/-- **The comparison of hypercohomology with that of the underlying abelian sheaves is compatible
with the restriction maps**: for a morphism `f : Y ⟶ Z` of schemes over `S`, the restriction map
`Hᵠ(Z, K|_Z) ⟶ Hᵠ(Y, K|_Y)` corresponds to the restriction map of the underlying complexes. -/
lemma forget_map_restrictOver_comp_cohomologyUpperStarForgetIso_hom {S Y Z : Scheme.{u}}
    (pY : Y ⟶ S) (pZ : Z ⟶ S) (f : Y ⟶ Z) (hf : f ≫ pZ = pY)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (q : ℤ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).map
          (globalSectionsRestriction f
              (((pZ)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K.obj) ≫
            (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
              ((Functor.mapDerivedCategoryTriangleIso
                (upperStarComp (ModuleCat.{u + 1} Λ) f pZ pY hf.symm)).inv.app K.obj))) ≫
      (cohomologyUpperStarForgetIso Λ pY K q).hom =
    (cohomologyUpperStarForgetIso Λ pZ K q).hom ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).map
        (globalSectionsRestriction f (((pZ)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategory.obj
            ((moduleAbelianForget Λ S).mapDerivedCategory.obj K.obj)) ≫
          (rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
            ((Functor.mapDerivedCategoryTriangleIso
              (upperStarComp AddCommGrpCat.{u + 1} f pZ pY hf.symm)).inv.app
                ((moduleAbelianForget Λ S).mapDerivedCategory.obj K.obj))) := by
  have h := ((Functor.mapDerivedCategoryHomologyFunctorIso
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) q).hom.naturality
      (globalSectionsRestriction f (((pZ)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K.obj) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).map
          ((Functor.mapDerivedCategoryTriangleIso
            (upperStarComp (ModuleCat.{u + 1} Λ) f pZ pY hf.symm)).inv.app K.obj)))
  dsimp only [Functor.comp_map, Functor.comp_obj] at h
  dsimp only [cohomologyUpperStarForgetIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    Iso.app_hom, Iso.symm_hom]
  rw [reassoc_of% h]
  simp only [cohomology, Functor.comp_map, ← Functor.map_comp, Category.assoc]
  rw [rightDerivedGlobalSectionsForget_restrictOver Λ pY pZ f hf]

end AlgebraicGeometry.Etale
