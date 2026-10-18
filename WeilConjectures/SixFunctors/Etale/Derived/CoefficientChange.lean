/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.AdicSystem
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBoundedBelow
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-!
# Compact cohomology and geometric stalks commute with restriction of scalars

Let `ρ : Λ →+* Λ'` be a morphism of finite coefficient rings. This file constructs the canonical
coefficient comparisons
`Res ∘ RΓ_c(X, -) ≅ RΓ_c(X, -) ∘ Res`
(`AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsRestrictScalarsIso`) and
`Res ∘ (-)_x̄ ≅ (-)_x̄ ∘ Res`
(`AlgebraicGeometry.Etale.geometricStalkRestrictScalarsIso`) on the unbounded derived categories
of étale sheaves over a separably closed field, and their compatibility with the compact-support
base change and the stalk transport along automorphism pairs, the inputs of the Frobenius
compatibility of `WeilConjectures.SixFunctors.Etale.Derived.AdicFrobenius`. From them it deduces
the coefficient-change statements
`AlgebraicGeometry.Etale.exists_isCoefficientChange_compactlySupportedGlobalSections` and
`AlgebraicGeometry.Etale.exists_isCoefficientChange_geometricStalk` used to build the towers of
`AlgebraicGeometry.Etale.AdicSystem`.

## Remaining inputs

- `isCoefficientChange_compactlySupportedGlobalSectionsRestrictScalarsIso`
  and `isCoefficientChange_geometricStalkRestrictScalarsIso`: the
  canonical comparisons are isomorphisms on derived base changes of `Dᵇctf` complexes (blueprint
  `lem-fix-compact-support-coefficient-change` and `thm-trf-finite-coefficient-map`, nodes of
  the subsections `sk-def-sfb-coefficient-comparisons` and `sk-p-trace-coeff`).
- `derivedRestrictScalarsCompRightDerivedGlobalSectionsIso_hom_app_globalSectionsTransport`
  and `derivedRestrictScalarsCompRightDerivedLowerShriekIso_baseChangeMap`:
  the compatibility of the comparisons with the transport of `RΓ(Spec k, -)` along an
  automorphism and with the compact-support exchange map (the "compatible with pullback" clause of
  `lem-fix-compact-support-coefficient-change`). These are coherence statements for the
  unbounded derived functors involved; they are not proved yet.
-/

@[expose] public section

universe w u

open CategoryTheory Abelian Limits Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

section

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (G : D ⥤ E) [G.Additive]

/-- If `L` is exact and the unit of `RG` is an isomorphism at the image under `L` of every
K-injective complex, then `D(L) ⋙ RG` is a right derived functor of `L ⋙ G`. -/
lemma isRightDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor_of_isIso
    (hG : ∀ (K : CochainComplex C ℤ) [K.IsKInjective], IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))) :
    (L.mapDerivedCategory ⋙ G.rightDerivedFunctor).IsRightDerivedFunctor
      (mapDerivedCategoryCompRightDerivedFunctorUnit L G)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  refine (HomotopyCategory.KInjectives.localizerMorphism_derives
    ((L ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso _ (fun X₁ => ?_)
  obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X₁
  change IsIso ((mapDerivedCategoryCompRightDerivedFunctorUnit L G).app
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))
  have h₂ : IsIso (G.rightDerivedFunctorUnit.app
      ((L.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))) := hG K
  have h₃ : IsIso (G.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))) :=
    inferInstanceAs (IsIso (G.rightDerivedFunctor.mapIso
      (L.mapDerivedCategoryFactorsh.app _).symm).hom)
  rw [mapDerivedCategoryCompRightDerivedFunctorUnit_app]
  infer_instance

/-- **Right derived functors precomposed with an exact functor**: `R(L ⋙ G) ≅ D(L) ⋙ RG` for an
exact functor `L` such that the unit of `RG` is an isomorphism at the image of every K-injective
complex. -/
noncomputable def mapDerivedCategoryCompRightDerivedFunctorIsoOfIsIso
    (hG : ∀ (K : CochainComplex C ℤ) [K.IsKInjective], IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))) :
    (L ⋙ G).rightDerivedFunctor ≅ L.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
  have := isRightDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor_of_isIso L G hG
  rightDerivedUnique (L ⋙ G).rightDerivedFunctor
    (L.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (L ⋙ G).rightDerivedFunctorUnit (mapDerivedCategoryCompRightDerivedFunctorUnit L G)
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

end

section

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory D] [HasDerivedCategory E] [HasKInjectiveResolutions D]
  [IsGrothendieckAbelian.{w} C]
  (L : C ⥤ D) [L.Additive] (G : D ⥤ E) [G.Additive]

/-- To check that the unit of `RG` is an isomorphism at the images under an additive functor `L`
of all K-injective complexes, it suffices to treat K-injective complexes with injective
components. -/
lemma isIso_rightDerivedFunctorUnit_app_map_of_isKInjective
    (hG : ∀ (I : CochainComplex C ℤ) [I.IsKInjective], (∀ n, Injective (I.X n)) →
      IsIso (G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))))
    (K : CochainComplex C ℤ) [K.IsKInjective] :
    IsIso (G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) := by
  let ι : K ⟶ (CochainComplex.kInjectiveResolutionFunctor.{w} C).obj K :=
    (CochainComplex.toKInjectiveResolution.{w} C).app K
  have : QuasiIso ι := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{w} C K).2
  have hι : HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ) ι :=
    (CochainComplex.IsKInjective.quasiIso_iff ι).1 this
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms] at hι
  have h₁ : IsIso ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map ι) := hι
  have h₂ : IsIso ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map ι)) := by
    rw [← Functor.mapHomotopyCategory_map]
    infer_instance
  have h₃ := hG ((CochainComplex.kInjectiveResolutionFunctor.{w} C).obj K) inferInstance
  have h := G.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map ι))
  exact IsIso.of_isIso_fac_right h.symm

end

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section

variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  {r₀ : D₀ ⥤ C₀} {r₁ : D₁ ⥤ C₁} {r₂ : D₂ ⥤ C₂}
  {G₁ : C₀ ⥤ C₁} {G₂ : C₁ ⥤ C₂} {F₁ : D₀ ⥤ D₁} {F₂ : D₁ ⥤ D₂}

/-- The pasting of two commutative squares of functors. -/
noncomputable def pasteTwoSquaresIso (e₁ : r₀ ⋙ G₁ ≅ F₁ ⋙ r₁) (e₂ : r₁ ⋙ G₂ ≅ F₂ ⋙ r₂) :
    r₀ ⋙ G₁ ⋙ G₂ ≅ (F₁ ⋙ F₂) ⋙ r₂ :=
  (Functor.associator r₀ G₁ G₂).symm ≪≫ Functor.isoWhiskerRight e₁ G₂ ≪≫
    Functor.associator F₁ r₁ G₂ ≪≫ Functor.isoWhiskerLeft F₁ e₂ ≪≫
    (Functor.associator F₁ F₂ r₂).symm

lemma pasteTwoSquaresIso_hom_app (e₁ : r₀ ⋙ G₁ ≅ F₁ ⋙ r₁) (e₂ : r₁ ⋙ G₂ ≅ F₂ ⋙ r₂) (X : D₀) :
    (pasteTwoSquaresIso e₁ e₂).hom.app X = G₂.map (e₁.hom.app X) ≫ e₂.hom.app (F₁.obj X) := by
  simp [pasteTwoSquaresIso]

end

section

variable {A A' S S' B B' : Type*} [Category A] [Category A'] [Category S] [Category S']
  [Category B] [Category B'] {RA : A' ⥤ A} {RS : S' ⥤ S} {RB : B' ⥤ B} {Φ : A ⥤ S}
  {Φ' : A' ⥤ S'} {Γ : S ⥤ B} {Γ' : S' ⥤ B'} {gA : A ⥤ A} {gA' : A' ⥤ A'} {hS : S ⥤ S}
  {hS' : S' ⥤ S'}

/-- Abstract form of the compatibility of a pasted coefficient comparison with a transport of
the shape `Γ ⟶ h^* ⋙ Γ` followed by an exchange `Φ ⋙ h^* ⟶ g^* ⋙ Φ`: it follows from the
compatibility of each square with the corresponding transformation. -/
lemma pasteTwoSquaresIso_hom_app_comp_map_of_comm
    (α₁ : RA ⋙ Φ ≅ Φ' ⋙ RS) (α₂ : RS ⋙ Γ ≅ Γ' ⋙ RB) (εg : RA ⋙ gA ≅ gA' ⋙ RA)
    (εh : RS ⋙ hS ≅ hS' ⋙ RS) (Ex : Φ ⋙ hS ⟶ gA ⋙ Φ) (Ex' : Φ' ⋙ hS' ⟶ gA' ⋙ Φ')
    (T : Γ ⟶ hS ⋙ Γ) (T' : Γ' ⟶ hS' ⋙ Γ')
    (hT : ∀ M', α₂.hom.app M' ≫ RB.map (T'.app M') =
      T.app (RS.obj M') ≫ Γ.map (εh.hom.app M') ≫ α₂.hom.app (hS'.obj M'))
    (hE : ∀ K', hS.map (α₁.hom.app K') ≫ εh.hom.app (Φ'.obj K') ≫ RS.map (Ex'.app K') =
      Ex.app (RA.obj K') ≫ Φ.map (εg.hom.app K') ≫ α₁.hom.app (gA'.obj K'))
    (K' : A') :
    (pasteTwoSquaresIso α₁ α₂).hom.app K' ≫ RB.map (T'.app (Φ'.obj K') ≫ Γ'.map (Ex'.app K')) =
      (T.app (Φ.obj (RA.obj K')) ≫ Γ.map (Ex.app (RA.obj K'))) ≫
        Γ.map (Φ.map (εg.hom.app K')) ≫ (pasteTwoSquaresIso α₁ α₂).hom.app (gA'.obj K') := by
  have h₁ := α₂.hom.naturality (Ex'.app K')
  have h₂ := T.naturality (α₁.hom.app K')
  have h₃ := congrArg Γ.map (hE K')
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp] at h₁ h₂ h₃
  rw [pasteTwoSquaresIso_hom_app, pasteTwoSquaresIso_hom_app, Functor.map_comp, Category.assoc,
    reassoc_of% (hT (Φ'.obj K')), ← h₁, reassoc_of% h₂, reassoc_of% h₃]
  simp

end


variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- For a direct image whose classical right derived functors vanish in large degrees, the unit
of `Rf_*` is an isomorphism at the restriction of scalars of every K-injective complex. -/
lemma isIso_rightDerivedFunctorUnit_app_restrictScalars {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : ℕ) (hd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) ℤ) [K.IsKInjective] :
    IsIso (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))) := by
  refine Functor.isIso_rightDerivedFunctorUnit_app_map_of_isKInjective.{u + 1} _ _
    (fun I _ hI ↦ ?_) K
  refine Functor.isIso_rightDerivedFunctorUnit_app_of_rightAcyclic.{u + 1} _ d hd _ fun n ↦ ?_
  have := hI n
  exact rightAcyclic_lowerStar_restrictScalars_obj ρ f (I.X n)

/-- **Restriction of scalars commutes with the unbounded derived direct image** along a morphism
whose higher direct images vanish in large degrees. -/
noncomputable def derivedRestrictScalarsCompRightDerivedLowerStarIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) (d : ℕ)
    (hd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F)) :
    Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ ⋙ R((f)_*[ModuleCat.{u + 1} Λ]) ≅
      R((f)_*[ModuleCat.{u + 1} Λ']) ⋙ Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ :=
  (Functor.mapDerivedCategoryCompRightDerivedFunctorIsoOfIsIso _ _
      (fun K _ ↦ isIso_rightDerivedFunctorUnit_app_restrictScalars ρ f d hd K)).symm ≪≫
    Functor.rightDerivedFunctorNatIso (lowerStarCompRestrictScalarsIso ρ f).symm ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _

/-- Restriction of scalars commutes with the extension by zero along an open immersion: the
conjugate of the identity `Coext ⋙ j^* = j^* ⋙ Coext`. -/
noncomputable def openImmersionLowerShriekRestrictScalarsIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    Sheaf.restrictScalars U.smallEtaleTopology ρ ⋙ (j)_!open[ModuleCat.{u + 1} Λ] ≅
      (j)_!open[ModuleCat.{u + 1} Λ'] ⋙ Sheaf.restrictScalars X.smallEtaleTopology ρ :=
  (conjugateIsoEquiv
    ((openImmersionLowerShriekAdjunction _ j).comp (Sheaf.restrictCoextendScalarsAdj _ ρ))
    ((Sheaf.restrictCoextendScalarsAdj _ ρ).comp
      (openImmersionLowerShriekAdjunction _ j))).symm (Iso.refl _)

/-- Restriction of scalars commutes with the derived extension by zero along an open
immersion. -/
noncomputable def derivedRestrictScalarsCompOpenImmersionLowerShriekIso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    Sheaf.derivedRestrictScalars U.smallEtaleTopology ρ ⋙ D((j)_!open[ModuleCat.{u + 1} Λ]) ≅
      D((j)_!open[ModuleCat.{u + 1} Λ']) ⋙ Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ :=
  Functor.mapDerivedCategorySquareIso (openImmersionLowerShriekRestrictScalarsIso ρ j)

section Point

variable {k : Type u} [Field k] [IsSepClosed k]

/-- Over a separably closed field, restriction of scalars commutes with the derived global
sections on `Spec k`, both being induced by exact functors. -/
noncomputable def derivedRestrictScalarsCompRightDerivedGlobalSectionsIso :
    Sheaf.derivedRestrictScalars (Spec (.of k)).smallEtaleTopology ρ ⋙
        rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k)) ≅
      rightDerivedGlobalSections (ModuleCat.{u + 1} Λ') (Spec (.of k)) ⋙
        ModuleCat.derivedRestrictScalars ρ :=
  Functor.isoWhiskerLeft _ (rightDerivedGlobalSectionsIsoOfIsSepClosed Λ) ≪≫
    Functor.mapDerivedCategorySquareIso
      (G₁ := (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ')).obj
        (op (etalePoint k)))
      (G₂ := ModuleCat.restrictScalars.{u + 1} ρ) (Iso.refl _) ≪≫
    Functor.isoWhiskerRight (rightDerivedGlobalSectionsIsoOfIsSepClosed Λ').symm _


/-- The compatibility of the coefficient comparison of `RΓ(Spec k, -)` with the transport along
an automorphism `h` of `Spec k`. -/
lemma derivedRestrictScalarsCompRightDerivedGlobalSectionsIso_hom_app_globalSectionsTransport
    (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h]
    (M' : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (derivedRestrictScalarsCompRightDerivedGlobalSectionsIso ρ).hom.app M' ≫
        (ModuleCat.derivedRestrictScalars ρ).map ((globalSectionsTransport Λ' h).hom.app M') =
      (globalSectionsTransport Λ h).hom.app
          ((Sheaf.derivedRestrictScalars _ ρ).obj M') ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).map
          ((leftDerivedUpperStarRestrictScalarsIso ρ h).hom.app M') ≫
        (derivedRestrictScalarsCompRightDerivedGlobalSectionsIso ρ).hom.app
          ((L((h)^*[ModuleCat.{u + 1} Λ'])).obj M') :=
  sorry

end Point

section LowerShriek

variable [Finite Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]

/-- The coefficient comparison `Res ∘ Rf_! ≅ Rf_! ∘ Res` for the chosen compactification
`X ⟶[j] Z ⟶[p] Y` over a quasi-compact base: the pasting of the commutations of restriction of
scalars with `Dj_!` and `Rp_*`. -/
noncomputable def derivedRestrictScalarsCompRightDerivedLowerShriekIso :
    Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ ⋙ R(f)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ'] ⋙ Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ :=
  let c := HasCompactification.compactification f
  have := c.isProper
  have := c.isOpenImmersion
  have hd := exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace Λ
    isAddTorsion_of_finite c.g
  pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ c.i)
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ c.g hd.choose hd.choose_spec)

end LowerShriek

/-- The derived pullback composition isomorphisms with an arbitrary composite `g₁₂ = g₁ ≫ g₂`
are compatible with restriction of scalars
(`AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso_comp_hom_app`). -/
lemma leftDerivedUpperStarRestrictScalarsIso_comp_hom_app' {T S R : Scheme.{u}} (g₁ : T ⟶ S)
    (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂)
    (K : DerivedCategory (Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (leftDerivedUpperStarRestrictScalarsIso ρ g₁₂).hom.app K ≫
        (Sheaf.derivedRestrictScalars _ ρ).map
          ((leftDerivedUpperStarComp _ g₁ g₂ g₁₂ hg).hom.app K) =
      (leftDerivedUpperStarComp _ g₁ g₂ g₁₂ hg).hom.app
          ((Sheaf.derivedRestrictScalars _ ρ).obj K) ≫
        (L((g₁)^*[ModuleCat.{u + 1} Λ])).map
          ((leftDerivedUpperStarRestrictScalarsIso ρ g₂).hom.app K) ≫
        (leftDerivedUpperStarRestrictScalarsIso ρ g₁).hom.app
          ((L((g₂)^*[ModuleCat.{u + 1} Λ'])).obj K) := by
  subst hg
  exact leftDerivedUpperStarRestrictScalarsIso_comp_hom_app ρ g₁ g₂ K

/-- Abstract form of the compatibility of the stalk exchange `c₁⁻¹ ≫ c₂ : X ⋙ H ⟶ G ⋙ X` with
coefficient comparisons, from the compatibility of each composition isomorphism. -/
lemma exchange_comm_of_comm_aux {A A' B B' : Type*} [Category A] [Category A'] [Category B]
    [Category B'] (ResA : A' ⥤ A) (ResB : B' ⥤ B) {P X : B ⥤ A} {H : A ⥤ A} {G : B ⥤ B}
    {P' X' : B' ⥤ A'} {H' : A' ⥤ A'} {G' : B' ⥤ B'} (c₁ : P ≅ X ⋙ H) (c₁' : P' ≅ X' ⋙ H')
    (c₂ : P ≅ G ⋙ X) (c₂' : P' ≅ G' ⋙ X') (ιP : ResB ⋙ P ≅ P' ⋙ ResA)
    (ιX : ResB ⋙ X ≅ X' ⋙ ResA) (ιH : ResA ⋙ H ≅ H' ⋙ ResA) (ιG : ResB ⋙ G ≅ G' ⋙ ResB)
    (h₁ : ∀ K, ιP.hom.app K ≫ ResA.map (c₁'.hom.app K) =
      c₁.hom.app (ResB.obj K) ≫ H.map (ιX.hom.app K) ≫ ιH.hom.app (X'.obj K))
    (h₂ : ∀ K, ιP.hom.app K ≫ ResA.map (c₂'.hom.app K) =
      c₂.hom.app (ResB.obj K) ≫ X.map (ιG.hom.app K) ≫ ιX.hom.app (G'.obj K)) (K : B') :
    H.map (ιX.hom.app K) ≫ ιH.hom.app (X'.obj K) ≫ ResA.map ((c₁'.inv ≫ c₂'.hom).app K) =
      (c₁.inv ≫ c₂.hom).app (ResB.obj K) ≫ X.map (ιG.hom.app K) ≫ ιX.hom.app (G'.obj K) := by
  have e₁ : H.map (ιX.hom.app K) ≫ ιH.hom.app (X'.obj K) =
      c₁.inv.app (ResB.obj K) ≫ ιP.hom.app K ≫ ResA.map (c₁'.hom.app K) := by
    rw [h₁ K, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% e₁, NatTrans.comp_app, NatTrans.comp_app, Functor.map_comp,
    ← ResA.map_comp_assoc, Iso.hom_inv_id_app, ResA.map_id, Category.id_comp, h₂ K]
  simp

section Stalk

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} (x : Spec (.of k) ⟶ X)

/-- The coefficient comparison `Res ∘ (-)_x̄ ≅ (-)_x̄ ∘ Res` of geometric stalks over a separably
closed field: the pasting of the commutation of restriction of scalars with `Lx̄^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso`) and with `RΓ(Spec k, -)`. -/
noncomputable def geometricStalkRestrictScalarsIso :
    Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ ⋙ geometricStalk Λ x ≅
      geometricStalk Λ' x ⋙ ModuleCat.derivedRestrictScalars ρ :=
  pasteTwoSquaresIso (leftDerivedUpperStarRestrictScalarsIso ρ x)
    (derivedRestrictScalarsCompRightDerivedGlobalSectionsIso ρ)

omit [IsSepClosed k] in
/-- The components of the stalk transport `AlgebraicGeometry.Etale.stalkPullback`. -/
lemma stalkPullback_app {g : X ⟶ X} {h : Spec (.of k) ⟶ Spec (.of k)} (hx : h ≫ x = x ≫ g)
    [IsIso h] (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (stalkPullback Λ hx).app K =
      (globalSectionsTransport Λ h).hom.app ((L((x)^*[ModuleCat.{u + 1} Λ])).obj K) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).map
          (((leftDerivedUpperStarComp _ h x (x ≫ g) hx.symm).inv ≫
            (leftDerivedUpperStarComp _ x g).hom).app K) := by
  simp [stalkPullback]

/-- The coefficient comparison of geometric stalks is compatible with the stalk transport along
every automorphism pair fixing the point. -/
lemma isStalkPullbackCompatible_geometricStalkRestrictScalarsIso {g : X ⟶ X}
    {h : Spec (.of k) ⟶ Spec (.of k)} (hx : h ≫ x = x ≫ g) [IsIso h] :
    IsStalkPullbackCompatible ρ (geometricStalkRestrictScalarsIso ρ x) hx := by
  intro K'
  rw [stalkPullback_app, stalkPullback_app]
  exact pasteTwoSquaresIso_hom_app_comp_map_of_comm
    (α₁ := leftDerivedUpperStarRestrictScalarsIso ρ x)
    (α₂ := derivedRestrictScalarsCompRightDerivedGlobalSectionsIso ρ)
    (εg := leftDerivedUpperStarRestrictScalarsIso ρ g)
    (εh := leftDerivedUpperStarRestrictScalarsIso ρ h)
    (Ex := (leftDerivedUpperStarComp _ h x (x ≫ g) hx.symm).inv ≫
      (leftDerivedUpperStarComp _ x g).hom)
    (Ex' := (leftDerivedUpperStarComp _ h x (x ≫ g) hx.symm).inv ≫
      (leftDerivedUpperStarComp _ x g).hom)
    (T := (globalSectionsTransport Λ h).hom) (T' := (globalSectionsTransport Λ' h).hom)
    (derivedRestrictScalarsCompRightDerivedGlobalSectionsIso_hom_app_globalSectionsTransport ρ h)
    (exchange_comm_of_comm_aux _ _ _ _ _ _ (leftDerivedUpperStarRestrictScalarsIso ρ (x ≫ g)) _ _ _
      (leftDerivedUpperStarRestrictScalarsIso_comp_hom_app' ρ h x (x ≫ g) hx.symm)
      (leftDerivedUpperStarRestrictScalarsIso_comp_hom_app' ρ x g (x ≫ g) rfl)) K'

/-- Blueprint `thm-trf-finite-coefficient-map` (subsection `sk-p-trace-coeff`), the pullback
isomorphism at a geometric point: for a surjection `ρ : Λ →+* Λ'` of finite rings whose exponent
is invertible on `k`, the canonical coefficient comparison
`K_x̄ ⊗ᴸ_Λ Λ' ⟶ (K ⊗ᴸ_Λ Λ')_x̄` of geometric stalks
(`AlgebraicGeometry.Etale.geometricStalkRestrictScalarsIso`) is an isomorphism for every
`K ∈ Dᵇctf(X, Λ)`. -/
theorem isCoefficientChange_geometricStalkRestrictScalarsIso [Finite Λ] [Finite Λ']
    [HasInvertibleExponent Λ (Spec (.of k))] (hρ : Function.Surjective ρ) :
    IsCoefficientChange ρ (geometricStalk Λ x) (geometricStalk Λ' x)
      (geometricStalkRestrictScalarsIso ρ x) :=
  sorry

end Stalk

variable [Finite Λ] [Finite Λ'] {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
  (aX : X ⟶ Spec (.of k)) [HasCompactification aX]

/-- The coefficient comparison `Res ∘ RΓ_c(X, -) ≅ RΓ_c(X, -) ∘ Res` of compact cohomology over a
separably closed field. -/
noncomputable def compactlySupportedGlobalSectionsRestrictScalarsIso :
    Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ ⋙
        compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ') aX ⋙
        ModuleCat.derivedRestrictScalars ρ :=
  pasteTwoSquaresIso (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ aX)
    (derivedRestrictScalarsCompRightDerivedGlobalSectionsIso ρ)

/-- The compatibility of the coefficient comparison of `Ra_!` with the compact-support exchange
map along an automorphism pair `(g, h)`. -/
lemma derivedRestrictScalarsCompRightDerivedLowerShriekIso_baseChangeMap [QuasiCompact aX]
    {g : X ⟶ X} {h : Spec (.of k) ⟶ Spec (.of k)} (sq : IsPullback g aX aX h)
    (K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (L((h)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ aX).hom.app K') ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ h).hom.app
        ((R(aX)_![ModuleCat.{u + 1} Λ']).obj K') ≫
      (Sheaf.derivedRestrictScalars _ ρ).map
        ((rightDerivedLowerShriekBaseChangeMap Λ' sq).app K') =
    (rightDerivedLowerShriekBaseChangeMap Λ sq).app
        ((Sheaf.derivedRestrictScalars _ ρ).obj K') ≫
      (R(aX)_![ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarRestrictScalarsIso ρ g).hom.app K') ≫
      (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ aX).hom.app
        ((L((g)^*[ModuleCat.{u + 1} Λ'])).obj K') :=
  sorry

omit [IsSepClosed k] in
/-- The components of the compact-support base change `AlgebraicGeometry.Etale.compactPullback`. -/
lemma compactPullback_app {g : X ⟶ X} {h : Spec (.of k) ⟶ Spec (.of k)} [QuasiCompact aX]
    (sq : IsPullback g aX aX h) [IsIso h]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactPullback Λ sq).app K =
      (globalSectionsTransport Λ h).hom.app ((R(aX)_![ModuleCat.{u + 1} Λ]).obj K) ≫
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).map
          ((rightDerivedLowerShriekBaseChangeMap Λ sq).app K) := by
  simp [compactPullback]

/-- The coefficient comparison of compact cohomology is compatible with the compact-support base
change along every automorphism pair. -/
lemma isCompactPullbackCompatible_compactlySupportedGlobalSectionsRestrictScalarsIso
    [QuasiCompact aX] {g : X ⟶ X} {h : Spec (.of k) ⟶ Spec (.of k)}
    (sq : IsPullback g aX aX h) [IsIso h] :
    IsCompactPullbackCompatible ρ (compactlySupportedGlobalSectionsRestrictScalarsIso ρ aX) sq := by
  intro K'
  rw [compactPullback_app, compactPullback_app]
  exact pasteTwoSquaresIso_hom_app_comp_map_of_comm
    (α₁ := derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ aX)
    (α₂ := derivedRestrictScalarsCompRightDerivedGlobalSectionsIso ρ)
    (εg := leftDerivedUpperStarRestrictScalarsIso ρ g)
    (εh := leftDerivedUpperStarRestrictScalarsIso ρ h)
    (Ex := rightDerivedLowerShriekBaseChangeMap Λ sq)
    (Ex' := rightDerivedLowerShriekBaseChangeMap Λ' sq)
    (T := (globalSectionsTransport Λ h).hom) (T' := (globalSectionsTransport Λ' h).hom)
    (derivedRestrictScalarsCompRightDerivedGlobalSectionsIso_hom_app_globalSectionsTransport ρ h)
    (derivedRestrictScalarsCompRightDerivedLowerShriekIso_baseChangeMap ρ aX sq) K'

/-- Blueprint `lem-fix-compact-support-coefficient-change` (subsection
`sk-def-sfb-coefficient-comparisons`): for a surjection `ρ : Λ →+* Λ'` of finite rings whose
exponent is invertible on the separably closed field `k` and a separated finite-type
`a_X : X ⟶ Spec k`, the canonical coefficient comparison
`RΓ_c(X, K) ⊗ᴸ_Λ Λ' ⟶ RΓ_c(X, K ⊗ᴸ_Λ Λ')`
(`AlgebraicGeometry.Etale.compactlySupportedGlobalSectionsRestrictScalarsIso`) is an
isomorphism for every `K ∈ Dᵇctf(X, Λ)`. -/
theorem isCoefficientChange_compactlySupportedGlobalSectionsRestrictScalarsIso [IsSeparated aX]
    [LocallyOfFiniteType aX] [QuasiCompact aX] [HasInvertibleExponent Λ (Spec (.of k))]
    (hρ : Function.Surjective ρ) :
    IsCoefficientChange ρ (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX)
      (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ') aX)
      (compactlySupportedGlobalSectionsRestrictScalarsIso ρ aX) :=
  sorry

variable [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]


/-- Blueprint `lem-fix-compact-support-coefficient-change` (subsection
`sk-def-sfb-coefficient-comparisons`):
compact cohomology commutes with finite-level coefficient reduction, compatibly with pullback.
For a surjection `ρ : Λ →+* Λ'` of finite coefficient rings whose exponent is invertible on the
separably closed field `k` and a separated finite-type `a_X : X ⟶ Spec k`, compact cohomology
commutes with restriction of scalars along `ρ` through a coefficient comparison `α` for which
`RΓ_c(X, K) ⊗ᴸ_Λ Λ' ⟶ RΓ_c(X, K ⊗ᴸ_Λ Λ')` is an isomorphism for every `K ∈ Dᵇctf(X, Λ)`, and `α`
is compatible with the compact-support base change along every pair of automorphisms
(`AlgebraicGeometry.Etale.IsCompactPullbackCompatible`). -/
theorem exists_isCoefficientChange_compactlySupportedGlobalSections
    [HasInvertibleExponent Λ (Spec (.of k))] (hρ : Function.Surjective ρ) :
    ∃ α, IsCoefficientChange ρ (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX)
        (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ') aX) α ∧
      ∀ (g : X ⟶ X) (h : Spec (.of k) ⟶ Spec (.of k)) (sq : IsPullback g aX aX h) [IsIso h],
        IsCompactPullbackCompatible ρ α sq :=
  ⟨compactlySupportedGlobalSectionsRestrictScalarsIso ρ aX,
    isCoefficientChange_compactlySupportedGlobalSectionsRestrictScalarsIso ρ aX hρ,
    fun _ _ sq _ ↦
      isCompactPullbackCompatible_compactlySupportedGlobalSectionsRestrictScalarsIso ρ aX sq⟩

/-- Blueprint `thm-trf-finite-coefficient-map` (subsection `sk-p-trace-coeff`), the pullback
isomorphism at a geometric point: geometric stalks commute with finite-level coefficient
reduction, compatibly with the stalk transports. For a surjection `ρ : Λ →+* Λ'` of finite
coefficient rings whose exponent is invertible on `k` and a geometric point `x̄ : Spec k ⟶ X`,
the geometric stalk commutes with restriction of scalars along `ρ` through a coefficient
comparison `β` for which `K_x̄ ⊗ᴸ_Λ Λ' ⟶ (K ⊗ᴸ_Λ Λ')_x̄` is an isomorphism for every
`K ∈ Dᵇctf(X, Λ)`, and `β` is compatible with the stalk transport at `x̄` along every pair of
automorphisms fixing `x̄` (`AlgebraicGeometry.Etale.IsStalkPullbackCompatible`). -/
theorem exists_isCoefficientChange_geometricStalk
    [HasInvertibleExponent Λ (Spec (.of k))] (hρ : Function.Surjective ρ)
    (x : Spec (.of k) ⟶ X) :
    ∃ β, IsCoefficientChange ρ (geometricStalk Λ x) (geometricStalk Λ' x) β ∧
      ∀ (g : X ⟶ X) (h : Spec (.of k) ⟶ Spec (.of k)) (hx : h ≫ x = x ≫ g) [IsIso h],
        IsStalkPullbackCompatible ρ β hx :=
  ⟨geometricStalkRestrictScalarsIso ρ x,
    isCoefficientChange_geometricStalkRestrictScalarsIso ρ x hρ,
    fun _ _ hx _ ↦ isStalkPullbackCompatible_geometricStalkRestrictScalarsIso ρ x hx⟩

namespace AdicSystem

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} (S : AdicSystem I X)
  [∀ n, Finite (R ⧸ I ^ n)] [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of k))]

include aX in
/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (1), levelwise perfectness and
normalization: each `P_n = RΓ_c(X, L_n)` and each geometric stalk `P_{x̄, n} = (L_n)_x̄` is a
perfect complex of `A_n`-modules, and the transition `ν_n` induces, through an identification of
`RΓ_c(X, -)` (resp. `(-)_x̄`) of a restriction of scalars with the restriction of scalars of
`RΓ_c(X, -)` (resp. `(-)_x̄`), a map `P_{n+1} ⟶ Res P_n` exhibiting `P_n` as
`P_{n+1} ⊗ᴸ_{A_{n+1}} A_n`, i.e. an isomorphism `P_{n+1} ⊗ᴸ_{A_{n+1}} A_n ≅ P_n`. -/
theorem isPerfect_and_exists_isDerivedBaseChange (n : ℕ) :
    ((compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ n)) aX).obj
        (S.obj n)).IsPerfect ∧
      (∃ e : (compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX).obj
          ((_root_.DerivedCategory.levelTransitionRestrictScalars _ I n.le_succ).obj (S.obj n)) ≅
          (ModuleCat.derivedRestrictScalars
            (Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ))).obj
            ((compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ n)) aX).obj
              (S.obj n)),
        ModuleCat.IsDerivedBaseChange
          ((compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX).map
            (S.map n) ≫ e.hom)) ∧
      ∀ x : Spec (.of k) ⟶ X,
        ((geometricStalk (R ⧸ I ^ n) x).obj (S.obj n)).IsPerfect ∧
        ∃ e : (geometricStalk (R ⧸ I ^ (n + 1)) x).obj
            ((_root_.DerivedCategory.levelTransitionRestrictScalars _ I n.le_succ).obj
              (S.obj n)) ≅
            (ModuleCat.derivedRestrictScalars
              (Ideal.Quotient.factor (Ideal.pow_le_pow_right n.le_succ))).obj
              ((geometricStalk (R ⧸ I ^ n) x).obj (S.obj n)),
          ModuleCat.IsDerivedBaseChange
            ((geometricStalk (R ⧸ I ^ (n + 1)) x).map (S.map n) ≫ e.hom) := by
  have hsurj : Function.Surjective
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) n.le_succ)) :=
    Ideal.Quotient.factor_surjective _
  refine ⟨isPerfect_compactlySupportedGlobalSections _ aX _ (S.boundedConstructibleFiniteTor n),
    ?_, fun x ↦ ⟨isPerfect_geometricStalk _ x _ (S.boundedConstructibleFiniteTor n), ?_⟩⟩
  · obtain ⟨α, hα, -⟩ := exists_isCoefficientChange_compactlySupportedGlobalSections _ aX hsurj
    exact ⟨α.app _, hα _ (S.boundedConstructibleFiniteTor (n + 1)) (S.isDerivedBaseChange n)⟩
  · obtain ⟨β, hβ, -⟩ := exists_isCoefficientChange_geometricStalk _ hsurj x
    exact ⟨β.app _, hβ _ (S.boundedConstructibleFiniteTor (n + 1)) (S.isDerivedBaseChange n)⟩

include aX in
/-- The coefficient identifications from which
`AlgebraicGeometry.Etale.AdicSystem.compactSupportTower` is built exist, compatibly with the
compact-support base change along every pair of automorphisms
(`AlgebraicGeometry.Etale.exists_isCoefficientChange_compactlySupportedGlobalSections`). -/
lemma exists_compactSupportTower :
    ∃ (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX ⋙
        ModuleCat.derivedRestrictScalars (I.powSuccFactor n)),
      (∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (α n)) ∧
      ∀ (n : ℕ) (g : X ⟶ X) (h : Spec (.of k) ⟶ Spec (.of k)) (sq : IsPullback g aX aX h)
        [IsIso h], IsCompactPullbackCompatible (I.powSuccFactor n) (α n) sq := by
  choose α hα hα' using fun n : ℕ ↦ exists_isCoefficientChange_compactlySupportedGlobalSections
    (I.powSuccFactor n) aX (Ideal.Quotient.factor_surjective _)
  exact ⟨α, hα, hα'⟩

/-- The coefficient identifications from which `AlgebraicGeometry.Etale.AdicSystem.stalkTower`
is built exist, compatibly with the stalk transports
(`AlgebraicGeometry.Etale.exists_isCoefficientChange_geometricStalk`). -/
lemma exists_stalkTower (x : Spec (.of k) ⟶ X) :
    ∃ (β : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        geometricStalk (R ⧸ I ^ (n + 1 + 1)) x ≅
      geometricStalk (R ⧸ I ^ (n + 1)) x ⋙ ModuleCat.derivedRestrictScalars (I.powSuccFactor n)),
      (∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (β n)) ∧
      ∀ (n : ℕ) (g : X ⟶ X) (h : Spec (.of k) ⟶ Spec (.of k)) (hx : h ≫ x = x ≫ g)
        [IsIso h], IsStalkPullbackCompatible (I.powSuccFactor n) (β n) hx := by
  choose β hβ hβ' using fun n : ℕ ↦ exists_isCoefficientChange_geometricStalk
    (I.powSuccFactor n) (Ideal.Quotient.factor_surjective _) x
  exact ⟨β, hβ, hβ'⟩

end AdicSystem

end AlgebraicGeometry.Etale
