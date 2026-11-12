/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.AdicFrobenius
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction
public import WeilConjectures.SixFunctors.Etale.Derived.SepClosedCohomology
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# The local Frobenius operators of the constant sheaf

For an automorphism `g` of a scheme `X`, the canonical identifications `Lg^* Λ_X ≅ Λ_X`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`) form a Weil datum on the unit `Λ_X`.
Its iterates are the canonical identifications for the iterates of `g`
(`AlgebraicGeometry.Etale.iterateWeilDatum_leftDerivedUpperStarUnitIso`), and at a point
`x̄ : Spec k ⟶ X` fixed by `(g, h)`, `k` separably closed, its local Frobenius operator is the
identity of the stalk (`AlgebraicGeometry.Etale.localOperator_leftDerivedUpperStarUnitIso`).

The key input is that the transport of derived global sections along an automorphism `h` of
`Spec k` is compatible with the identification `Lh^* Λ ≅ Λ`
(`AlgebraicGeometry.Etale.globalSectionsTransport_hom_app_unit`): on sections over the point it
is the restriction of the constant section `1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

section Triangle

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C E : Type*} [Category* C] [Category* E] [Abelian C] [Abelian E] [HasDerivedCategory C]
  [HasDerivedCategory E] {H : C ⥤ C} {S : C ⥤ E}
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]

/-- Let `e : S ≅ H ⋙ S` for exact functors `H` and `S`, and `η : H X ⟶ X` such that
`e_X ≫ S η = 𝟙`. Then the induced endomorphism of `D(S)(X[0])`, namely
`D(S) X[0] ≅ D(S) D(H) X[0] ≅ D(S) (H X)[0] ⟶ D(S) X[0]`, is the identity. -/
lemma mapDerivedCategoryTriangleIso_hom_app_Q_obj_single_comp (e : S ≅ H ⋙ S) {X : C}
    (η : H.obj X ⟶ X) (hη : e.hom.app X ≫ S.map η = 𝟙 _) :
    (mapDerivedCategoryTriangleIso e).hom.app
        (DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj X)) ≫
      S.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app X ≫
            (HomologicalComplex.single C (.up ℤ) 0).map η)) = 𝟙 _ := by
  have hc : (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        ((HomologicalComplex.single C (.up ℤ) 0).obj X) ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ S)) (.up ℤ)).inv.app _ ≫
      (S.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app X ≫
          (HomologicalComplex.single C (.up ℤ) 0).map η) = 𝟙 _ := by
    ext n
    by_cases hn : n = 0
    · subst hn
      have hn := e.hom.naturality (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom
      simp only [Functor.comp_map] at hn
      simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
        Functor.mapHomologicalComplexCompIso_inv_app_f, Functor.mapHomologicalComplex_map_f,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        HomologicalComplex.single_map_f_self, Functor.map_comp, HomologicalComplex.id_f,
        Iso.refl_inv, NatTrans.id_app, Category.assoc]
      erw [Category.id_comp]
      rw [← reassoc_of% hn,
        ← S.map_comp_assoc (HomologicalComplex.singleObjXSelf _ 0 (H.obj X)).inv, Iso.inv_hom_id,
        S.map_id, Category.id_comp, reassoc_of% hη, ← S.map_comp, Iso.hom_inv_id, S.map_id]
      rfl
    · exact (S.map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)).eq_of_src _ _
  have hfac : (Functor.mapDerivedCategoryCompIso H S).inv.app
        (DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj X)) ≫
      S.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app _) ≫
      S.mapDerivedCategoryFactors.hom.app _ =
      (H ⋙ S).mapDerivedCategoryFactors.hom.app _ ≫ DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ S)) (.up ℤ)).inv.app _) := by
    rw [← Functor.mapDerivedCategoryCompIso_fac H S, Category.assoc, Category.assoc,
      Category.assoc, ← DerivedCategory.Q.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← cancel_mono (S.mapDerivedCategoryFactors.hom.app _), Category.id_comp, Functor.map_comp,
    Category.assoc, Category.assoc, Functor.mapDerivedCategoryFactors_hom_naturality]
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  rw [reassoc_of% hfac, Functor.mapDerivedCategoryNatIso_fac_assoc, ← DerivedCategory.Q.map_comp,
    ← DerivedCategory.Q.map_comp, hc]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

end Triangle

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The identity isomorphism `L(𝟙 X)^* ≅ 𝟭` is, at the unit, the canonical identification
`L(𝟙 X)^* Λ_X ≅ Λ_X`. -/
lemma leftDerivedUpperStarId_hom_app_unit (X : Scheme.{u}) :
    (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app (𝟙_ _) =
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) (𝟙 X)).hom := by
  have h₁ := leftDerivedUpperStarComp_id_left_hom_app (ModuleCat.{u + 1} Λ) (𝟙 X) (𝟙_ _)
  have h₂ := leftDerivedUpperStarComp_hom_app_unit (ModuleCat.{u + 1} Λ) (𝟙 X) (𝟙 X) (𝟙 X)
    (Category.id_comp _).symm
  rw [← leftDerivedUpperStarUnitIso_hom_eq_η] at h₂
  have hn := (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.naturality
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) (𝟙 X)).hom
  have hn' : L((𝟙 X)^*[ModuleCat.{u + 1} Λ]).map
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) (𝟙 X)).hom ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app (𝟙_ _) =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app _ ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) (𝟙 X)).hom := hn
  rw [← cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.id_comp _).symm).hom.app (𝟙_ _) ≫ L((𝟙 X)^*[ModuleCat.{u + 1} Λ]).map
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) (𝟙 X)).hom), Category.assoc, hn',
    reassoc_of% h₁, Category.assoc, h₂]

/-- The iterates of the canonical Weil datum `Lg^* Λ_X ≅ Λ_X` of the unit are the canonical
identifications `L(g^m)^* Λ_X ≅ Λ_X`. -/
lemma iterateWeilDatum_leftDerivedUpperStarUnitIso {X : Scheme.{u}} (g : X ⟶ X) (m : ℕ) :
    iterateWeilDatum Λ g (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g).hom m =
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) (endIterate g m)).hom := by
  induction m with
  | zero => exact leftDerivedUpperStarId_hom_app_unit Λ X
  | succ m ih =>
    have h := leftDerivedUpperStarComp_hom_app_unit (ModuleCat.{u + 1} Λ) g (endIterate g m)
      (endIterate g (m + 1)) rfl
    rw [← leftDerivedUpperStarUnitIso_hom_eq_η, ← leftDerivedUpperStarUnitIso_hom_eq_η,
      ← leftDerivedUpperStarUnitIso_hom_eq_η] at h
    rw [iterateWeilDatum, ih]
    exact h

/-- At a point `x̄` fixed by `(g, h)`, the local Frobenius operator of the canonical Weil datum
`Lg^* Λ_X ≅ Λ_X` is, under the identification `(Λ_X)_x̄ = RΓ(s, Lx̄^* Λ_X) ≅ RΓ(s, Λ_s)`, the
transport of `RΓ(s, Λ_s)` along `h` followed by `Lh^* Λ_s ≅ Λ_s`. -/
lemma localOperator_leftDerivedUpperStarUnitIso_comp {X s : Scheme.{u}} {g : X ⟶ X} {h : s ⟶ s}
    {x : s ⟶ X} (hx : h ≫ x = x ≫ g) [IsIso h] :
    localOperator Λ hx (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g).hom ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s).map
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) x).hom =
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s).map
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) x).hom ≫
        (globalSectionsTransport Λ h).hom.app (𝟙_ _) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s).map
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) h).hom := by
  have h₁ := leftDerivedUpperStarComp_hom_app_unit (ModuleCat.{u + 1} Λ) x g (x ≫ g) rfl
  have h₂ := leftDerivedUpperStarComp_hom_app_unit (ModuleCat.{u + 1} Λ) h x (x ≫ g) hx.symm
  simp only [← leftDerivedUpperStarUnitIso_hom_eq_η] at h₁ h₂
  have hn := (globalSectionsTransport Λ h).hom.naturality
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) x).hom
  rw [reassoc_of% hn, localOperator, stalkPullback]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.assoc,
    Functor.comp_map, ← Functor.map_comp]
  rw [h₁, ← h₂, Iso.inv_hom_id_app_assoc]

/-- The canonical identification `Lg^* Λ_Y ≅ Λ_Z`, read through `Lg^* ≅ D(g^*)`: it is induced
on the complexes `Λ[0]` by the inverse of the unit comparison `Λ_Z ≅ g^* Λ_Y` of the monoidal
functor `g^*`. -/
lemma leftDerivedUpperStarIsoMapDerivedCategory_inv_app_unit_comp {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) :
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g).inv.app (𝟙_ _) ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g).hom =
      ((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.map
          ((DerivedCategory.quotientCompQhIso _).hom.app
            ((HomologicalComplex.single _ (.up ℤ) 0).obj (𝟙_ _))) ≫
        (g)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex (g)^*[ModuleCat.{u + 1} Λ] (.up ℤ)
              0).hom.app (𝟙_ _) ≫ (HomologicalComplex.single _ (.up ℤ) 0).map
            (Functor.Monoidal.εIso (g)^*[ModuleCat.{u + 1} Λ]).inv) ≫
        (DerivedCategory.quotientCompQhIso _).inv.app
          ((HomologicalComplex.single _ (.up ℤ) 0).obj (𝟙_ _)) := by
  simp [leftDerivedUpperStarUnitIso]

section Point

variable {k : Type u} [Field k] [IsSepClosed k]

/-- The unit of the lax monoidal functor `sheafToPresheaf` is natural for the restriction maps of
the unit sheaf, the restriction maps of the constant presheaf being identities. -/
@[reassoc]
lemma ε_sheafToPresheaf_app_comp_map {S : Scheme.{u}} {U V : S.Etaleᵒᵖ} (f : U ⟶ V) :
    (Functor.LaxMonoidal.ε (sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))).app U ≫
        (𝟙_ (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))).obj.map f =
      (Functor.LaxMonoidal.ε (sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))).app V :=
  ((Functor.LaxMonoidal.ε (sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))).naturality
    f).symm.trans (Category.id_comp _)

/-- Over a separably closed field `k`, the sections over the point `Spec k` of the unit sheaf
are the image of the unit `Λ ⟶ Λ_k(pt)` of the lax monoidal functor `sheafToPresheaf`. -/
lemma epi_ε_sheafToPresheaf_app_etalePoint :
    Epi ((Functor.LaxMonoidal.ε (sheafToPresheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))).app (op (etalePoint k))) := by
  have e : Functor.LaxMonoidal.ε (sheafToPresheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) = toSheafify _ _ ≫ (sheafToPresheaf _ _).map
        (Functor.OplaxMonoidal.η (presheafToSheaf (Spec (.of k)).smallEtaleTopology
          (ModuleCat.{u + 1} Λ))) :=
    (sheafificationAdjunction _ _).homEquiv_unit _ _ (Functor.OplaxMonoidal.η (presheafToSheaf _ _))
  rw [e, NatTrans.comp_app]
  refine @epi_comp _ _ _ _ _ _ ?_ _ inferInstance
  rw [ModuleCat.epi_iff_surjective]
  intro s
  obtain ⟨t, ht⟩ := Scheme.id_mem_of_mem_smallEtaleTopology_of_isSepClosed k _
    (Presheaf.imageSieve_mem (Spec (.of k)).smallEtaleTopology (toSheafify _ _) s)
  exact ⟨t, ht.trans (by simp)⟩

/-- **Sheaf-level normalization.** The transport `Γ(pt, Λ) ≅ Γ(pt, h^* Λ)` of sections over the
point of `Spec k` along an automorphism `h`, followed by `h^* Λ ≅ Λ`, is the identity. -/
lemma sectionsPointTransportIso_hom_app_unit_comp (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h] :
    (sectionsPointTransportIso Λ h).hom.app (𝟙_ _) ≫
      ((sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op (etalePoint k))).map (Functor.Monoidal.εIso (h)^*[ModuleCat.{u + 1} Λ]).inv = 𝟙 _ := by
  have hε : (Functor.Monoidal.εIso (h)^*[ModuleCat.{u + 1} Λ]).inv =
      (h)^*[ModuleCat.{u + 1} Λ].map (Functor.LaxMonoidal.ε (h)_*[ModuleCat.{u + 1} Λ]) ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).counit.app _ :=
    Etale.upperStar_η (ModuleCat.{u + 1} Λ) h
  have hι : (upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ) (asIso h).symm).inv.app (𝟙_ _) ≫
      (h)^*[ModuleCat.{u + 1} Λ].map (Functor.LaxMonoidal.ε (h)_*[ModuleCat.{u + 1} Λ]) ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).counit.app (𝟙_ _) =
      ((asIso h).symm.hom)_*[ModuleCat.{u + 1} Λ].map
          (Functor.LaxMonoidal.ε (h)_*[ModuleCat.{u + 1} Λ]) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) (asIso h).hom (asIso h).symm.hom (𝟙 _)
          (by simp)).hom.app (𝟙_ _) ≫ (lowerStarId (ModuleCat.{u + 1} Λ) _).hom.app (𝟙_ _) := by
    have n := (upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ) (asIso h).symm).inv.naturality
      (Functor.LaxMonoidal.ε (h)_*[ModuleCat.{u + 1} Λ])
    have c := Adjunction.leftAdjointUniq_hom_app_counit
      (lowerStarEquivalenceOfIso (ModuleCat.{u + 1} Λ) (asIso h).symm).toAdjunction
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h) (𝟙_ _)
    erw [← reassoc_of% n]
    exact congrArg _ c
  have := epi_ε_sheafToPresheaf_app_etalePoint (k := k) Λ
  rw [hε, sectionsPointTransportIso, sectionsTransportIso_hom_app, Category.assoc,
    ← Functor.map_comp, hι,
    ← cancel_epi ((Functor.LaxMonoidal.ε (sheafToPresheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))).app (op (etalePoint k)))]
  erw [Category.comp_id]
  simp only [Category.assoc]
  rw [ΓNatIsoSheafSections_inv_app_comp_lowerStarCompGlobalSectionsIso_inv_app_assoc,
    ε_sheafToPresheaf_app_comp_map_assoc]
  dsimp only [lowerStarCompSheafSectionsTerminalIso, NatIso.ofComponents_inv_app,
    Functor.mapIso_inv, Iso.symm_inv]
  rw [ε_sheafToPresheaf_app_comp_map_assoc]
  erw [ε_sheafToPresheaf_app_comp_map_assoc]
  have := Etale.isContinuous_overPullback h
  rw [Functor.map_comp]
  erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc
    (MorphismProperty.Over.pullback @Etale ⊤ h) (ModuleCat.{u + 1} Λ)]
  rw [Functor.map_comp]
  have hs {G G' : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : G ⟶ G') :
      ((sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op (etalePoint k))).map f = f.hom.app (op (etalePoint k)) := rfl
  rw [hs, hs, Etale.lowerStarComp_hom_app_hom_app, ε_sheafToPresheaf_app_comp_map_assoc]
  dsimp only [lowerStarId, GrothendieckTopology.lowerStarId]
  simp only [Functor.sheafPushforwardContinuousId'_hom_app_hom_app]
  exact ε_sheafToPresheaf_app_comp_map Λ _

/-- The sheaf-level normalization
`AlgebraicGeometry.Etale.sectionsPointTransportIso_hom_app_unit_comp` in the derived category:
the transport `D(Γ(pt, -)) ≅ D(h^*) ⋙ D(Γ(pt, -))` at the unit, followed by
`D(h^*) Λ ≅ Lh^* Λ ≅ Λ`, is the identity. -/
lemma mapDerivedCategoryTriangleIso_sectionsPointTransportIso_hom_app_unit
    (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h] :
    (Functor.mapDerivedCategoryTriangleIso (sectionsPointTransportIso Λ h)).hom.app (𝟙_ _) ≫
      ((sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op (etalePoint k))).mapDerivedCategory.map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) h).inv.app (𝟙_ _) ≫
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) h).hom) = 𝟙 _ := by
  have G := Functor.mapDerivedCategoryTriangleIso_hom_app_Q_obj_single_comp
    (sectionsPointTransportIso Λ h) _ (sectionsPointTransportIso_hom_app_unit_comp Λ h)
  rw [leftDerivedUpperStarIsoMapDerivedCategory_inv_app_unit_comp]
  simp only [Functor.map_comp, Category.assoc] at G ⊢
  erw [← (Functor.mapDerivedCategoryTriangleIso
    (sectionsPointTransportIso Λ h)).hom.naturality_assoc]
  rw [reassoc_of% G, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]

/-- The transport `RΓ(Spec k, Λ) ≅ RΓ(Spec k, Lh^* Λ)` of derived global sections along an
automorphism `h` of the spectrum of a separably closed field, followed by `Lh^* Λ ≅ Λ`, is the
identity. -/
lemma globalSectionsTransport_hom_app_unit (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h] :
    (globalSectionsTransport Λ h).hom.app (𝟙_ _) ≫
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) _).map
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) h).hom = 𝟙 _ := by
  have H := globalSectionsTransport_hom_app_comp_rightDerivedGlobalSectionsIsoOfIsSepClosed
    (Λ := Λ) h (𝟙_ _)
  rw [← cancel_mono ((rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).hom.app (𝟙_ _)),
    Category.assoc, NatTrans.naturality, reassoc_of% H, Category.id_comp, ← Functor.map_comp,
    mapDerivedCategoryTriangleIso_sectionsPointTransportIso_hom_app_unit, Category.comp_id]

/-- At a point `x̄ : Spec k ⟶ X` fixed by `(g, h)`, `k` separably closed, the local Frobenius
operator of the canonical Weil datum `Lg^* Λ_X ≅ Λ_X` of the unit is the identity of the
stalk. -/
theorem localOperator_leftDerivedUpperStarUnitIso {X : Scheme.{u}} {g : X ⟶ X}
    {h : Spec (.of k) ⟶ Spec (.of k)} {x : Spec (.of k) ⟶ X} (hx : h ≫ x = x ≫ g) [IsIso h] :
    localOperator Λ hx (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g).hom = 𝟙 _ := by
  have H := localOperator_leftDerivedUpperStarUnitIso_comp Λ hx
  rw [globalSectionsTransport_hom_app_unit, Category.comp_id] at H
  rwa [← cancel_mono ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) _).map
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) x).hom), Category.id_comp]

variable (k) in
/-- Over a separably closed field `k`, the derived global sections of the unit are the unit:
`RΓ(Spec k, Λ) ≅ Λ`. -/
noncomputable def rightDerivedGlobalSectionsUnitIsoOfIsSepClosed :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj (𝟙_ _) ≅ 𝟙_ _ :=
  (rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).app _ ≪≫
    (Functor.mapDerivedCategory _).mapIso (DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    (Functor.mapDerivedCategorySingleFunctor _ 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint).symm.app _ ≪≫
        Scheme.globalSectionsUnitIsoOfIsSepClosed k Λ) ≪≫
    DerivedCategory.singleFunctorObjUnitIso _

/-- The geometric stalk of the unit at a point `x̄ : Spec k ⟶ X`, `k` separably closed, is the
unit: `(Λ_X)_x̄ = RΓ(Spec k, Lx̄^* Λ_X) ≅ Λ`. -/
noncomputable def geometricStalkUnitIso {X : Scheme.{u}} (x : Spec (.of k) ⟶ X) :
    (geometricStalk Λ x).obj (𝟙_ _) ≅ 𝟙_ _ :=
  (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) _).mapIso
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) x) ≪≫
    rightDerivedGlobalSectionsUnitIsoOfIsSepClosed Λ k

attribute [local instance] DerivedCategory.braidedCategory'

/-- **The local terms of the unit.** At a point `x̄ : Spec k ⟶ X` fixed by `(g, h)`, `k`
separably closed, the trace of the local Frobenius operator of the canonical Weil datum
`Lg^* Λ_X ≅ Λ_X` on the stalk `(Λ_X)_x̄ = Λ` is `1`. -/
theorem trace_localOperator_leftDerivedUpperStarUnitIso {X : Scheme.{u}} {g : X ⟶ X}
    {h : Spec (.of k) ⟶ Spec (.of k)} {x : Spec (.of k) ⟶ X} (hx : h ≫ x = x ≫ g) [IsIso h]
    [HasRightDual ((geometricStalk Λ x).obj (𝟙_ _))] :
    trace (localOperator Λ hx (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g).hom) =
      𝟙 _ := by
  rw [localOperator_leftDerivedUpperStarUnitIso,
    trace_eq_of_iso (geometricStalkUnitIso Λ x) (𝟙 _) (𝟙 _) (by simp), trace_id_tensorUnit]

end Point

end AlgebraicGeometry.Etale
