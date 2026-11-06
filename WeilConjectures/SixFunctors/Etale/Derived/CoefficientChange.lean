/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.AdicSystem
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.SixFunctors.Etale.LowerStarGeometricPoint

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

- `isCoefficientChange_compactlySupportedGlobalSectionsRestrictScalarsIso`: the canonical
  comparison is an isomorphism on derived base changes of `Dᵇctf` complexes (blueprint
  `lem-fix-compact-support-coefficient-change`, subsection `sk-def-sfb-coefficient-comparisons`).
  The geometric-stalk analogue is proved in
  `WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeStalk`.
- `derivedRestrictScalarsCompRightDerivedLowerShriekIso_baseChangeMap`:
  the compatibility of the comparisons with the compact-support exchange map (the "compatible with
  pullback" clause of `lem-fix-compact-support-coefficient-change`). This is a coherence statement
  for the unbounded derived functors involved; it is proved in
  `WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange`.
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

namespace CategoryTheory

/-- The comparison between the constant sheaf adjunctions for two terminal objects `T` and `T'`
is the restriction map along `T' ⟶ T`. -/
lemma rightAdjointUniq_constantSheafAdj_hom_app {C : Type*} [Category C]
    (J : GrothendieckTopology C) (A : Type*) [Category A] [HasWeakSheafify J A]
    {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') (F : Sheaf J A) :
    ((constantSheafAdj J A hT).rightAdjointUniq (constantSheafAdj J A hT')).hom.app F =
      F.obj.map (hT.from T').op := by
  have key : toSheafify J ((Functor.const Cᵒᵖ).obj (F.obj.obj (op T))) ≫
      ((presheafToSheaf J A).map ((constantPresheafAdj A hT).counit.app F.obj) ≫
        (sheafificationAdjunction J A).counit.app F).hom =
      (constantPresheafAdj A hT).counit.app F.obj := by
    have := ((sheafificationAdjunction J A).homEquiv _ _).apply_symm_apply
      ((constantPresheafAdj A hT).counit.app F.obj)
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_unit] at this
    exact this
  rw [Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app]
  suffices h : (toSheafify J ((Functor.const Cᵒᵖ).obj (F.obj.obj (op T)))).app (op T') ≫
      ((sheafSections J A).obj (op T')).map
        ((presheafToSheaf J A).map ((constantPresheafAdj A hT).counit.app F.obj) ≫
          (sheafificationAdjunction J A).counit.app F) = F.obj.map (hT.from T').op by
    simpa [constantSheafAdj] using h
  exact NatTrans.congr_app key (op T')

/-- The components of the adjointified unit `Equivalence.adjointifyη η ε`. -/
lemma Equivalence.adjointifyη_hom_app {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {G : D ⥤ C} (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) (X : C) :
    (Equivalence.adjointifyη η ε).hom.app X =
      η.hom.app X ≫ G.map (ε.inv.app (F.obj X)) ≫ G.map (F.map (η.inv.app X)) := by
  simp [Equivalence.adjointifyη, Trans.trans]

/-- The components of the unit of `Equivalence.mk F G η ε`. -/
lemma Equivalence.mk_unit_app {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) (X : C) :
    (Equivalence.mk F G η ε).unit.app X =
      η.hom.app X ≫ G.map (ε.inv.app (F.obj X)) ≫ G.map (F.map (η.inv.app X)) :=
  Equivalence.adjointifyη_hom_app η ε X

/-- On a site with a terminal object, the comparison between the identifications of the global
sections with the sections over two terminal objects `T` and `T'` is the restriction map. -/
@[reassoc]
lemma Sheaf.ΓNatIsoSheafSections_inv_app_comp_hom_app {C : Type*} [Category C]
    (J : GrothendieckTopology C) (A : Type*) [Category A] [HasWeakSheafify J A] [HasTerminal C]
    {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') (F : Sheaf J A) :
    (Sheaf.ΓNatIsoSheafSections J A hT).inv.app F ≫
        (Sheaf.ΓNatIsoSheafSections J A hT').hom.app F =
      F.obj.map (hT.from T').op := by
  rw [Sheaf.ΓNatIsoSheafSections, Sheaf.ΓNatIsoSheafSections, Adjunction.rightAdjointUniq_inv_app,
    Adjunction.rightAdjointUniq_trans_app, rightAdjointUniq_constantSheafAdj_hom_app]

end CategoryTheory

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

section DerivedExact

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]

omit [HasKInjectiveResolutions D] in
/-- For exact functors, the isomorphism `RF ≅ RG` induced by `e : F ≅ G` corresponds to the
isomorphism `D(F) ≅ D(G)` under the identifications `RF ≅ D(F)` and `RG ≅ D(G)`. -/
@[reassoc]
lemma rightDerivedFunctorNatIso_hom_app_comp_isoMapDerivedCategory_hom_app {F G : C ⥤ D}
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) (K : DerivedCategory C) :
    (Functor.rightDerivedFunctorNatIso e).hom.app K ≫
        G.rightDerivedFunctorIsoMapDerivedCategory.hom.app K =
      F.rightDerivedFunctorIsoMapDerivedCategory.hom.app K ≫
        (Functor.mapDerivedCategoryNatIso e).hom.app K := by
  suffices H : (Functor.rightDerivedFunctorNatIso e).hom ≫
      G.rightDerivedFunctorIsoMapDerivedCategory.hom =
      F.rightDerivedFunctorIsoMapDerivedCategory.hom ≫
        (Functor.mapDerivedCategoryNatIso e).hom from NatTrans.congr_app H K
  refine Functor.rightDerived_ext F.rightDerivedFunctor F.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _ _ _ ?_
  ext X
  have hF := NatTrans.congr_app F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac X
  have hG := NatTrans.congr_app G.rightDerivedFunctorIsoMapDerivedCategory_hom_fac X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hF hG ⊢
  rw [reassoc_of% hF,
    Functor.mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_hom_app]
  simp only [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]
  rw [Functor.rightDerivedNatTrans_app_assoc, hG]
  simp

end DerivedExact

section Transport

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E] [HasDerivedCategory C]
  [HasDerivedCategory E] {H F : C ⥤ C} {Γ S : C ⥤ E}
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [Γ.Additive] [PreservesFiniteLimits Γ] [PreservesFiniteColimits Γ]
  [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]

/-- The isomorphism `S ≅ H ⋙ S` obtained from `ι : H ≅ F`, `γ : F ⋙ Γ ≅ Γ` and `e : Γ ≅ S`:
`S ≅ Γ ≅ F ⋙ Γ ≅ F ⋙ S ≅ H ⋙ S`. -/
noncomputable def sectionsTransportIso (ι : H ≅ F) (γ : F ⋙ Γ ≅ Γ) (e : Γ ≅ S) : S ≅ H ⋙ S :=
  e.symm ≪≫ γ.symm ≪≫ Functor.isoWhiskerLeft F e ≪≫ Functor.isoWhiskerRight ι.symm S

end Transport

section TransportApp

variable {C E : Type*} [Category C] [Category E] {H F : C ⥤ C} {Γ S : C ⥤ E}

/-- The components of `AlgebraicGeometry.Etale.sectionsTransportIso`. -/
lemma sectionsTransportIso_hom_app (ι : H ≅ F) (γ : F ⋙ Γ ≅ Γ) (e : Γ ≅ S) (X : C) :
    (sectionsTransportIso ι γ e).hom.app X =
      (e.inv.app X ≫ γ.inv.app X ≫ e.hom.app (F.obj X)) ≫ S.map (ι.inv.app X) := by
  simp [sectionsTransportIso]

end TransportApp

/-- Restriction of scalars commutes with the unit of the pushforward equivalence along an
isomorphism of schemes. -/
lemma restrictScalars_map_lowerStarEquivalenceOfIso_unit_app {X Y : Scheme.{u}} (e : X ≅ Y)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (Sheaf.restrictScalars _ ρ).map
        ((lowerStarEquivalenceOfIso (ModuleCat.{u + 1} Λ') e).unit.app F) =
      (lowerStarEquivalenceOfIso (ModuleCat.{u + 1} Λ) e).unit.app
        ((Sheaf.restrictScalars _ ρ).obj F) := by
  ext V x
  rfl

/-- The comparison of `upperStarInvIsoLowerStarHom` with restriction of scalars. -/
lemma upperStarRestrictScalarsIso_hom_app_comp_upperStarInvIsoLowerStarHom {X Y : Scheme.{u}}
    (e : X ≅ Y) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (upperStarRestrictScalarsIso ρ e.inv).hom.app F ≫
        (Sheaf.restrictScalars _ ρ).map
          ((upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ') e).hom.app F) =
      (upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ) e).hom.app
          ((Sheaf.restrictScalars _ ρ).obj F) := by
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) e.inv).homEquiv _ _).injective
  have h₁ := Adjunction.unit_leftAdjointUniq_hom_app
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') e.inv)
    (lowerStarEquivalenceOfIso (ModuleCat.{u + 1} Λ') e).toAdjunction F
  have h₂ := Adjunction.unit_leftAdjointUniq_hom_app
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) e.inv)
    (lowerStarEquivalenceOfIso (ModuleCat.{u + 1} Λ) e).toAdjunction
    ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj F)
  have h₃ := restrictScalars_map_unit_app ρ e.inv F
  have h₄ : (Sheaf.restrictScalars X.smallEtaleTopology ρ).map
      ((lowerStarEquivalenceOfIso (ModuleCat.{u + 1} Λ') e).toAdjunction.unit.app F) =
      (lowerStarEquivalenceOfIso (ModuleCat.{u + 1} Λ) e).toAdjunction.unit.app
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj F) :=
    restrictScalars_map_lowerStarEquivalenceOfIso_unit_app ρ e F
  calc _ = (Sheaf.restrictScalars X.smallEtaleTopology ρ).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') e.inv).unit.app F ≫
          (e.inv)_*[ModuleCat.{u + 1} Λ'].map
            ((upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ') e).hom.app F)) := by
        rw [Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp, h₃]
        exact (Category.assoc _ _ _).symm
    _ = _ := by
        rw [upperStarInvIsoLowerStarHom]
        refine (congrArg (Sheaf.restrictScalars X.smallEtaleTopology ρ).map h₁).trans ?_
        refine h₄.trans (h₂.symm.trans ?_)
        exact (Adjunction.homEquiv_unit _ _ _ _).symm

/-- The inverse form of
`AlgebraicGeometry.Etale.upperStarRestrictScalarsIso_hom_app_comp_upperStarInvIsoLowerStarHom`. -/
lemma restrictScalars_map_upperStarInvIsoLowerStarHom_inv_app {X Y : Scheme.{u}}
    (e : X ≅ Y) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (Sheaf.restrictScalars Y.smallEtaleTopology ρ).map
        ((upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ') e).inv.app F) =
      (upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ) e).inv.app
          ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj F) ≫
        (upperStarRestrictScalarsIso ρ e.inv).hom.app F := by
  have hB := upperStarRestrictScalarsIso_hom_app_comp_upperStarInvIsoLowerStarHom ρ e F
  calc _ = (upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ) e).inv.app
          ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj F) ≫
        ((upperStarRestrictScalarsIso ρ e.inv).hom.app F ≫
          (Sheaf.restrictScalars Y.smallEtaleTopology ρ).map
            ((upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ') e).hom.app F)) ≫
        (Sheaf.restrictScalars Y.smallEtaleTopology ρ).map
          ((upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ') e).inv.app F) := by
        rw [hB]
        exact (Iso.inv_hom_id_app_assoc (upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ) e)
          ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj F)
          ((Sheaf.restrictScalars Y.smallEtaleTopology ρ).map
            ((upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ') e).inv.app F))).symm
    _ = _ := by
        rw [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
          CategoryTheory.Functor.map_id]
        exact congrArg (fun x ↦ (upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ) e).inv.app
          ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj F) ≫ x)
          (Category.comp_id ((upperStarRestrictScalarsIso ρ e.inv).hom.app F))


/-- The sections over the point of the transport along a pushforward. -/
@[reassoc]
lemma ΓNatIsoSheafSections_inv_app_comp_lowerStarCompGlobalSectionsIso_inv_app
    (g : Spec (.of k) ⟶ Spec (.of k))
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint).inv.app F ≫
        (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) g).inv.app F ≫
        (Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint).hom.app
          ((g)_*[ModuleCat.{u + 1} Λ].obj F) =
      F.obj.map (isTerminalEtalePoint.from (⊤_ _)).op ≫
        (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} Λ) g).inv.app F ≫
        ((g)_*[ModuleCat.{u + 1} Λ].obj F).obj.map (terminalIsTerminal.from (etalePoint k)).op := by
  simp only [lowerStarCompGlobalSectionsIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.assoc,
    Sheaf.ΓNatIsoSheafSections_inv_app_comp_hom_app_assoc,
    Sheaf.ΓNatIsoSheafSections_inv_app_comp_hom_app]

/-- Restriction of scalars commutes with the identification
`Γ(pt, F) ≅ Γ(pt, g_* F)` of sections over the point. -/
lemma restrictScalars_map_sectionsTransportAux (g : Spec (.of k) ⟶ Spec (.of k))
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (ModuleCat.restrictScalars ρ).map
        ((Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint).inv.app F ≫
          (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ') g).inv.app F ≫
          (Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint).hom.app
            ((g)_*[ModuleCat.{u + 1} Λ'].obj F)) =
      (Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint).inv.app
          ((Sheaf.restrictScalars _ ρ).obj F) ≫
        (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) g).inv.app
          ((Sheaf.restrictScalars _ ρ).obj F) ≫
        (Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint).hom.app
          ((g)_*[ModuleCat.{u + 1} Λ].obj ((Sheaf.restrictScalars _ ρ).obj F)) := by
  rw [ΓNatIsoSheafSections_inv_app_comp_lowerStarCompGlobalSectionsIso_inv_app,
    ΓNatIsoSheafSections_inv_app_comp_lowerStarCompGlobalSectionsIso_inv_app,
    Functor.map_comp, Functor.map_comp]
  rfl

/-- Restriction of scalars commutes with the sheaf-level transport of sections over the point
along an automorphism `e` of `Spec k`. -/
lemma restrictScalars_map_sectionsTransportIso_hom_app (e : Spec (.of k) ≅ Spec (.of k))
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (ModuleCat.restrictScalars ρ).map ((sectionsTransportIso
        (upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ') e)
        (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ') e.hom)
        (Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint)).hom.app F) =
      (sectionsTransportIso (upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ) e)
          (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) e.hom)
          (Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint)).hom.app
          ((Sheaf.restrictScalars _ ρ).obj F) ≫
        ((sheafSections _ _).obj (op (etalePoint k))).map
          ((upperStarRestrictScalarsIso ρ e.inv).hom.app F) := by
  have hB := restrictScalars_map_upperStarInvIsoLowerStarHom_inv_app ρ e F
  have hS : (ModuleCat.restrictScalars ρ).map
      (((sheafSections _ _).obj (op (etalePoint k))).map
        ((upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ') e).inv.app F)) =
      ((sheafSections _ _).obj (op (etalePoint k))).map
        ((upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ) e).inv.app
          ((Sheaf.restrictScalars _ ρ).obj F)) ≫
      ((sheafSections _ _).obj (op (etalePoint k))).map
          ((upperStarRestrictScalarsIso ρ e.inv).hom.app F) := by
    rw [← Functor.map_comp, ← hB]
    rfl
  have hΓ := restrictScalars_map_sectionsTransportAux ρ e.hom F
  rw [sectionsTransportIso_hom_app, sectionsTransportIso_hom_app, Functor.map_comp, hΓ, hS]
  exact (Category.assoc _ _ _).symm

variable (Λ) in
/-- The sheaf-level transport `Γ(pt, F) ≅ Γ(pt, h^* F)` along an automorphism `h` of `Spec k`. -/
noncomputable def sectionsPointTransportIso (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h] :
    (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (op (etalePoint k)) ≅
      (h)^*[ModuleCat.{u + 1} Λ] ⋙
        (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op (etalePoint k)) :=
  sectionsTransportIso (upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} Λ) (asIso h).symm)
    (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) (asIso h).symm.hom)
    (Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint)

/-- The sheaf-level transport `AlgebraicGeometry.Etale.sectionsPointTransportIso` is compatible
with the identification `Res ⋙ Γ(pt, -) = Γ(pt, -) ⋙ Res`. -/
lemma sectionsPointTransportIso_comm (h : Spec (.of k) ⟶ Spec (.of k)) [IsIso h]
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (Iso.refl (Sheaf.restrictScalars (Spec (.of k)).smallEtaleTopology ρ ⋙
        (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op (etalePoint k))) :
        Sheaf.restrictScalars (Spec (.of k)).smallEtaleTopology ρ ⋙
          (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (op (etalePoint k)) ≅
        (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ')).obj
            (op (etalePoint k)) ⋙ ModuleCat.restrictScalars.{u + 1} ρ).hom.app F ≫
      (ModuleCat.restrictScalars ρ).map ((sectionsPointTransportIso Λ' h).hom.app F) =
    (sectionsPointTransportIso Λ h).hom.app ((Sheaf.restrictScalars _ ρ).obj F) ≫
      ((sheafSections _ _).obj (op (etalePoint k))).map
        ((upperStarRestrictScalarsIso ρ h).hom.app F) ≫
      (Iso.refl (Sheaf.restrictScalars (Spec (.of k)).smallEtaleTopology ρ ⋙
        (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (op (etalePoint k))) :
        Sheaf.restrictScalars (Spec (.of k)).smallEtaleTopology ρ ⋙
          (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (op (etalePoint k)) ≅
        (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ')).obj
            (op (etalePoint k)) ⋙ ModuleCat.restrictScalars.{u + 1} ρ).hom.app
        ((h)^*[ModuleCat.{u + 1} Λ'].obj F) := by
  rw [Iso.refl_hom, NatTrans.id_app, NatTrans.id_app]
  refine (Category.id_comp _).trans
    ((restrictScalars_map_sectionsTransportIso_hom_app ρ (asIso h).symm F).trans ?_)
  exact congrArg (_ ≫ ·) (Category.comp_id _).symm

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The components of
`AlgebraicGeometry.Etale.derivedRestrictScalarsCompRightDerivedGlobalSectionsIso`. -/
lemma derivedRestrictScalarsCompRightDerivedGlobalSectionsIso_hom_app
    (M' : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (derivedRestrictScalarsCompRightDerivedGlobalSectionsIso ρ).hom.app M' =
      (rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).hom.app
          ((Sheaf.derivedRestrictScalars _ ρ).obj M') ≫
        (Functor.mapDerivedCategorySquareIso
          (F₁ := Sheaf.restrictScalars (Spec (.of k)).smallEtaleTopology ρ)
          (F₂ := (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (op (etalePoint k)))
          (G₁ := (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ')).obj
            (op (etalePoint k)))
          (G₂ := ModuleCat.restrictScalars.{u + 1} ρ) (Iso.refl _)).hom.app M' ≫
        (ModuleCat.derivedRestrictScalars ρ).map
          ((rightDerivedGlobalSectionsIsoOfIsSepClosed Λ').inv.app M') := by
  simp [derivedRestrictScalarsCompRightDerivedGlobalSectionsIso]


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


end AlgebraicGeometry.Etale
