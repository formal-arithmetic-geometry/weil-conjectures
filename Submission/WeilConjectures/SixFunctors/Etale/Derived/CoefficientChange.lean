/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.Etale.Derived.AdicSystem
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Submission.WeilConjectures.SixFunctors.Etale.LowerStarGeometricPoint

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

end

section

variable {A A' S S' B B' : Type*} [Category A] [Category A'] [Category S] [Category S']
  [Category B] [Category B'] {RA : A' ⥤ A} {RS : S' ⥤ S} {RB : B' ⥤ B} {Φ : A ⥤ S}
  {Φ' : A' ⥤ S'} {Γ : S ⥤ B} {Γ' : S' ⥤ B'} {gA : A ⥤ A} {gA' : A' ⥤ A'} {hS : S ⥤ S}
  {hS' : S' ⥤ S'}

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

end DerivedExact

section Transport

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E] [HasDerivedCategory C]
  [HasDerivedCategory E] {H F : C ⥤ C} {Γ S : C ⥤ E}
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [Γ.Additive] [PreservesFiniteLimits Γ] [PreservesFiniteColimits Γ]
  [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]

end Transport

section TransportApp

variable {C E : Type*} [Category C] [Category E] {H F : C ⥤ C} {Γ S : C ⥤ E}

end TransportApp


attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits


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
