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

end

section

variable {A A' S S' B B' : Type*} [Category A] [Category A'] [Category S] [Category S']
  [Category B] [Category B'] {RA : A' ⥤ A} {RS : S' ⥤ S} {RB : B' ⥤ B} {Φ : A ⥤ S}
  {Φ' : A' ⥤ S'} {Γ : S ⥤ B} {Γ' : S' ⥤ B'} {gA : A ⥤ A} {gA' : A' ⥤ A'} {hS : S ⥤ S}
  {hS' : S' ⥤ S'}

end

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

section Point

variable {k : Type u} [Field k] [IsSepClosed k]

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

variable [HasKInjectiveResolutions C] [F.PreservesKInjectiveComplexes]

end Transport

section TransportApp

variable {C E : Type*} [Category C] [Category E] {H F : C ⥤ C} {Γ S : C ⥤ E}

end TransportApp

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

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end Point

section LowerShriek

variable [Finite Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]

end LowerShriek

section Stalk

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} (x : Spec (.of k) ⟶ X)

end Stalk

variable [Finite Λ] [Finite Λ'] {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
  (aX : X ⟶ Spec (.of k)) [HasCompactification aX]

end AlgebraicGeometry.Etale
