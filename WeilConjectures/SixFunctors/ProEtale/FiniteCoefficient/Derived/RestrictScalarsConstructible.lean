/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.ConstructibleSheaf.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleSerre
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension

/-!
# Restriction of scalars of pro-étale complexes: direct images and constructibility

Let `φ : Λ →+* Λ'` be a morphism of commutative rings. Restriction of scalars
`Res : D(X_proét, Λ') ⥤ D(X_proét, Λ)` (`CategoryTheory.Sheaf.derivedRestrictScalars`)

- commutes with the derived direct image `Rf_*` on bounded below objects
  (`AlgebraicGeometry.ProEtale.derivedRestrictScalarsRightDerivedLowerStarIso`): an injective
  sheaf of `Λ'`-modules is `f_*`-acyclic as a sheaf of `Λ`-modules, being a direct summand of
  a coextension of scalars `Hom_Λ(Λ', I)` of an injective sheaf `I`
  (`CategoryTheory.Sheaf.rightAcyclic_restrictScalars_obj_of_injective`, for any site);
- commutes with the comparison `ν^*` (`AlgebraicGeometry.ProEtale.comparisonUpperStarRestrictScalarsIso`);
- for `φ = Λ → Λ ⧸ J` with `Λ ⧸ J` finite, preserves and reflects bounded constructibility
  (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible_derivedRestrictScalars_obj_iff`)
  and membership in `D_c^[a, b]`
  (`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleIn_derivedRestrictScalars_obj_iff`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory.Sheaf

section

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

/-- Restriction of scalars of sheaves of modules is faithful: it is computed sectionwise. -/
instance faithful_restrictScalars : (restrictScalars J φ).Faithful where
  map_injective {_ _} a b h := by
    ext U : 3
    exact (ModuleCat.restrictScalars.{u + 1} φ).map_injective
      (congr_app (congrArg (fun a ↦ a.hom) h) U)

/-- The restriction of scalars of the coextension `Hom_Λ(Λ', I)` of a sheaf `I` of `Λ`-modules is
the sheaf `Hom_Λ(Λ', I)` of homomorphisms out of the `Λ`-module `Λ'`. -/
noncomputable def restrictScalarsObjCoextendScalarsObjIso (I : Sheaf J (ModuleCat.{u + 1} Λ)) :
    (restrictScalars J φ).obj
        ((sheafCompose J (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ)).obj I) ≅
      (homSheaf J ((ModuleCat.restrictScalars.{u + 1} φ).obj (ModuleCat.of Λ' Λ'))).obj I where
  hom := (sheafCompose_map _
    (AlgebraicGeometry.Etale.coextendScalarsCompRestrictScalarsIso φ).hom).app I
  inv := (sheafCompose_map _
    (AlgebraicGeometry.Etale.coextendScalarsCompRestrictScalarsIso φ).inv).app I
  hom_inv_id := by
    ext U : 3
    exact congr_app (AlgebraicGeometry.Etale.coextendScalarsCompRestrictScalarsIso φ).hom_inv_id _
  inv_hom_id := by
    ext U : 3
    exact congr_app (AlgebraicGeometry.Etale.coextendScalarsCompRestrictScalarsIso φ).inv_hom_id _

/-- **Injective sheaves of `Λ'`-modules are acyclic as sheaves of `Λ`-modules** for every left
exact functor `Φ` sending sectionwise surjective morphisms to epimorphisms. Embedding the
restriction of an injective sheaf `I'` into an injective sheaf `I` of `Λ`-modules, `I'` is a
direct summand of the coextension `Hom_Λ(Λ', I)`, whose restriction of scalars is the
`Φ`-acyclic sheaf `Hom_Λ(Λ', I)` (`CategoryTheory.Sheaf.rightAcyclic_homSheaf_obj`). -/
theorem rightAcyclic_restrictScalars_obj_of_injective {D : Type*} [Category* D] [Abelian D]
    (Φ : Sheaf J (ModuleCat.{u + 1} Λ) ⥤ D) [Φ.Additive] [PreservesFiniteLimits Φ]
    (hΦ : ∀ {A B : Sheaf J (ModuleCat.{u + 1} Λ)} (p : A ⟶ B),
      (∀ U, Function.Surjective (p.hom.app U)) → Epi (Φ.map p))
    (I' : Sheaf J (ModuleCat.{u + 1} Λ')) [Injective I'] :
    Φ.rightAcyclic ((restrictScalars J φ).obj I') := by
  let res := restrictScalars J φ
  let adj := restrictCoextendScalarsAdj J φ
  let I := Injective.under (res.obj I')
  -- `I'` is a direct summand of `Hom_Λ(Λ', I)`
  let j : I' ⟶ (sheafCompose J (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ)).obj I :=
    adj.homEquiv _ _ (Injective.ι (res.obj I'))
  have h : res.map j ≫ adj.counit.app I = Injective.ι (res.obj I') :=
    (adj.homEquiv_counit (g := j)).symm.trans ((adj.homEquiv _ _).symm_apply_apply _)
  have : Mono (res.map j) := mono_of_mono_fac h
  have : Mono j := res.mono_of_mono_map this
  let r := Injective.factorThru (𝟙 I') j
  have hjr : res.map j ≫ res.map r = 𝟙 _ := by
    rw [← res.map_comp, Injective.comp_factorThru, res.map_id]
  have hI : Φ.rightAcyclic (res.obj
      ((sheafCompose J (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ)).obj I)) :=
    Φ.rightAcyclic.prop_of_iso (restrictScalarsObjCoextendScalarsObjIso J φ I).symm
      (rightAcyclic_homSheaf_obj Φ hΦ I (fun U ↦ baer_obj_of_injective.{u + 1} I U.unop) _)
  intro q
  rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id, ← hjr,
    CategoryTheory.Functor.map_comp,
    (hI q).eq_of_tgt ((Φ.rightDerived (q + 1)).map (res.map j)) 0, Limits.zero_comp]

end

end CategoryTheory.Sheaf

namespace CategoryTheory.Linear

/-- In a linear category, a scalar killing an object kills every isomorphic object. -/
lemma smul_id_eq_zero_of_iso {R : Type*} [Semiring R] {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]
    [Linear R 𝒞] {X Y : 𝒞} (e : X ≅ Y) {r : R} (h : r • 𝟙 X = 0) : r • 𝟙 Y = 0 := by
  calc r • 𝟙 Y = e.inv ≫ (r • 𝟙 X) ≫ e.hom := by simp
    _ = 0 := by simp [h]

end CategoryTheory.Linear

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

section LowerStar

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The direct image of pro-étale sheaves of `Λ`-modules sends morphisms which are surjective on
sections to epimorphisms: it is computed sectionwise. -/
lemma epi_lowerStar_map_of_surjective
    {A B : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} (p : A ⟶ B)
    (hp : ∀ U, Function.Surjective (p.hom.app U)) :
    Epi ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).map p) := by
  have : Sheaf.IsLocallySurjective ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).map p) :=
    Presheaf.isLocallySurjective_of_surjective _ _ fun U ↦ hp _
  exact Sheaf.epi_of_isLocallySurjective _

/-- **Injective pro-étale sheaves of `Λ'`-modules are `f_*`-acyclic as sheaves of
`Λ`-modules.** -/
theorem rightAcyclic_lowerStar_restrictScalars_obj
    (I : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ')) [Injective I] :
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightAcyclic
      ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj I) :=
  Sheaf.rightAcyclic_restrictScalars_obj_of_injective _ φ _
    (epi_lowerStar_map_of_surjective f) I

/-- The comparison `Res(R⁺f_* K) ⟶ R⁺f_*(Res K)` between restriction of scalars along `φ` and
the derived direct image of pro-étale sheaves on `D⁺`: the base change morphism of the
identification `f_* ∘ Res = Res ∘ f_*`. It is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_rightDerivedPlusLowerStarRestrictScalars`). -/
noncomputable def rightDerivedPlusLowerStarRestrictScalars :
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ') f).rightDerivedFunctorPlus ⋙
        (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryPlus ⟶
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryPlus ⋙
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange (lowerStarCompSheafComposeRestrictScalarsIso φ f).hom

/-- **Restriction of scalars commutes with the derived direct image on `D⁺`**, since it sends
injective pro-étale sheaves of `Λ'`-modules to `f_*`-acyclic sheaves of `Λ`-modules. -/
instance isIso_rightDerivedPlusLowerStarRestrictScalars :
    IsIso (rightDerivedPlusLowerStarRestrictScalars φ f) :=
  Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic _
    fun I _ ↦ rightAcyclic_lowerStar_restrictScalars_obj φ f I

/-- **Restriction of scalars commutes with the derived direct image** of bounded below
pro-étale complexes: `Res(Rf_* K) ≅ Rf_*(Res K)` for `K` bounded below. -/
noncomputable def derivedRestrictScalarsRightDerivedLowerStarIso
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ')))
    (hK : DerivedCategory.TStructure.t.plus K) :
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).obj
        ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ') f)).obj K) ≅
      (R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj
        ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj K) :=
  (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).mapIso
      ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ') f).rightDerivedFunctorPlusCompatibility.app
        ⟨K, hK⟩).symm ≪≫
    DerivedCategory.Plus.ι.mapIso
      (asIso ((rightDerivedPlusLowerStarRestrictScalars φ f).app ⟨K, hK⟩)) ≪≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlusCompatibility.app _

end LowerStar

section Comparison

variable (X : Scheme.{u})

/-- Restriction of scalars commutes with the comparison `ν^*`: `ν^* (Res F) ≅ Res (ν^* F)`. It
is the conjugate of the identity `ν_* ∘ Coext = Coext ∘ ν_*`, both functors being computed
sectionwise. -/
noncomputable def comparisonUpperStarRestrictScalarsIso :
    Sheaf.restrictScalars X.smallEtaleTopology φ ⋙ ν^*(X)[ModuleCat.{u + 1} Λ] ≅
      ν^*(X)[ModuleCat.{u + 1} Λ'] ⋙ Sheaf.restrictScalars (Scheme.ProEt.topology X) φ :=
  (conjugateIsoEquiv
    ((comparisonAdjunction _ X).comp (Sheaf.restrictCoextendScalarsAdj _ φ))
    ((Sheaf.restrictCoextendScalarsAdj _ φ).comp (comparisonAdjunction _ X))).symm
    (Iso.refl _)

/-- The derived comparison `D(ν^*)` commutes with restriction of scalars. -/
noncomputable def comparisonUpperStarMapDerivedCategoryRestrictScalarsIso :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategory ⋙
        D(ν^*(X)[ModuleCat.{u + 1} Λ]) ≅
      D(ν^*(X)[ModuleCat.{u + 1} Λ']) ⋙ Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ :=
  Functor.mapDerivedCategorySquareIso (comparisonUpperStarRestrictScalarsIso φ X)

end Comparison

section Constructible

variable {T : Scheme.{u}} (J : Ideal Λ)

/-- A scalar of `J` kills the restriction of scalars of a sheaf of `Λ ⧸ J`-modules. -/
lemma smul_id_restrictScalars_obj_eq_zero
    (H : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Λ ⧸ J))) {r : Λ} (hr : r ∈ J) :
    r • 𝟙 ((Sheaf.restrictScalars (Scheme.ProEt.topology T) (Ideal.Quotient.mk J)).obj H) =
      0 := by
  ext U x
  exact (congrArg (· • x) (Ideal.Quotient.eq_zero_iff_mem.2 hr)).trans (zero_smul _ x)

/-- `ν_*` commutes with the multiplication by a scalar. -/
lemma comparisonLowerStar_map_smul_id
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)) (r : Λ) :
    (ν_*(T)[ModuleCat.{u + 1} Λ]).map (r • 𝟙 F) = r • 𝟙 _ :=
  rfl

/-- **Constructibility descends along restriction of scalars to `Λ`.** For `Λ ⧸ J` finite, a
pro-étale sheaf `H` of `Λ ⧸ J`-modules whose restriction of scalars is `ν^* G` for a
constructible étale sheaf `G` of `Λ`-modules is constructible: `G` is killed by `J`, as `ν^*` is
fully faithful, so `G` is the restriction of scalars of a constructible sheaf `G'` of
`Λ ⧸ J`-modules, and `ν^* G' ≅ H` since restriction of scalars is fully faithful. -/
lemma constructibleSheaf_of_restrictScalars [Finite (Λ ⧸ J)]
    (H : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Λ ⧸ J)))
    (hH : constructibleSheaf Λ T
      ((Sheaf.restrictScalars (Scheme.ProEt.topology T) (Ideal.Quotient.mk J)).obj H)) :
    constructibleSheaf (Λ ⧸ J) T H := by
  obtain ⟨G, hG, ⟨e⟩⟩ := hH
  have : IsConstructibleSheaf G := hG
  have := isIso_comparisonAdjunction_unit (ModuleCat.{u + 1} Λ) T
  have hJ (r : Λ) (hr : r ∈ J) : r • 𝟙 G = 0 := by
    refine Linear.smul_id_eq_zero_of_iso
      (asIso ((comparisonAdjunction (ModuleCat.{u + 1} Λ) T).unit.app G)).symm ?_
    rw [← comparisonLowerStar_map_smul_id,
      Linear.smul_id_eq_zero_of_iso e.symm (smul_id_restrictScalars_obj_eq_zero J H hr),
      Functor.map_zero]
  let eG := Sheaf.restrictScalarsCoextendScalarsIso G hJ
  have : IsConstructibleSheaf ((Sheaf.restrictScalars T.smallEtaleTopology
      (Ideal.Quotient.mk J)).obj ((Sheaf.coextendScalars T.smallEtaleTopology J).obj G)) :=
    IsConstructibleSheaf.of_iso eG.symm
  refine ⟨(Sheaf.coextendScalars T.smallEtaleTopology J).obj G,
    (isConstructibleSheaf_restrictScalars_iff J _).1 this, ⟨?_⟩⟩
  have := Sheaf.restrictScalars_full (Scheme.ProEt.topology T) (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective
  exact (Functor.FullyFaithful.ofFullyFaithful _).preimageIso
    ((comparisonUpperStarRestrictScalarsIso (Ideal.Quotient.mk J) T).symm.app _ ≪≫
      (ν^*(T)[ModuleCat.{u + 1} Λ]).mapIso eG ≪≫ e)

/-- Restriction of scalars along `Λ → Λ ⧸ J` preserves bounded constructibility of pro-étale
complexes, for `Λ ⧸ J` finite: it commutes with `D(ν^*)`, and the restriction of scalars of a
bounded étale complex with constructible homology sheaves is again such a complex. -/
lemma DerivedCategory.boundedConstructible_derivedRestrictScalars_obj [Finite (Λ ⧸ J)]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Λ ⧸ J)))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (Λ ⧸ J)) T K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T
      ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) (Ideal.Quotient.mk J)).obj K) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hK
  refine ⟨(Sheaf.restrictScalars T.smallEtaleTopology (Ideal.Quotient.mk J)).mapDerivedCategory.obj
    K', ⟨Functor.bounded_mapDerivedCategory_obj _ hK'.1, fun n ↦ ?_⟩,
    ⟨(comparisonUpperStarMapDerivedCategoryRestrictScalarsIso (Ideal.Quotient.mk J) T).app K' ≪≫
      (Sheaf.derivedRestrictScalars _ _).mapIso e⟩⟩
  have : IsConstructibleSheaf ((Sheaf.restrictScalars T.smallEtaleTopology
      (Ideal.Quotient.mk J)).obj
        ((_root_.DerivedCategory.homologyFunctor (Sheaf T.smallEtaleTopology _) n).obj K')) :=
    (isConstructibleSheaf_restrictScalars_iff J _).2 (hK'.2 n)
  exact IsConstructibleSheaf.of_iso
    (((Sheaf.restrictScalars _ _).mapDerivedCategoryHomologyFunctorIso n).app K')

/-- **Bounded constructibility descends along restriction of scalars** to `Λ`, for `Λ ⧸ J`
finite: over the finite ring `Λ ⧸ J` it suffices that the homology sheaves are constructible
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible_iff_homologyProperty`), which
follows from `AlgebraicGeometry.ProEtale.constructibleSheaf_of_restrictScalars`. -/
lemma DerivedCategory.boundedConstructible_of_derivedRestrictScalars_obj [Finite (Λ ⧸ J)]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Λ ⧸ J)))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T
      ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) (Ideal.Quotient.mk J)).obj K)) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (Λ ⧸ J)) T K := by
  rw [DerivedCategory.boundedConstructible_iff_homologyProperty]
  refine ⟨Functor.bounded_of_bounded_mapDerivedCategory_obj _ hK.bounded, fun n ↦ ?_⟩
  exact constructibleSheaf_of_restrictScalars J _ ((constructibleSheaf Λ T).prop_of_iso
    (((Sheaf.restrictScalars _ _).mapDerivedCategoryHomologyFunctorIso n).app K).symm
    (hK.homologyProperty n))

/-- For `Λ ⧸ J` finite, a pro-étale complex of `Λ ⧸ J`-modules is bounded constructible if and
only if its restriction of scalars to `Λ` is. -/
lemma DerivedCategory.boundedConstructible_derivedRestrictScalars_obj_iff [Finite (Λ ⧸ J)]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Λ ⧸ J)))) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T
        ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) (Ideal.Quotient.mk J)).obj K) ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (Λ ⧸ J)) T K :=
  ⟨boundedConstructible_of_derivedRestrictScalars_obj J,
    boundedConstructible_derivedRestrictScalars_obj J⟩

/-- Restriction of scalars along `Λ → Λ ⧸ J` preserves `D_c^[a, b]`, for `Λ ⧸ J` finite. -/
lemma DerivedCategory.constructibleIn_derivedRestrictScalars_obj [Finite (Λ ⧸ J)] {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Λ ⧸ J)))}
    (hK : DerivedCategory.constructibleIn (ModuleCat.{u + 1} (Λ ⧸ J)) T a b K) :
    DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) T a b
      ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) (Ideal.Quotient.mk J)).obj K) :=
  ⟨boundedConstructible_derivedRestrictScalars_obj J hK.1,
    Functor.homologyConcentratedIn_mapDerivedCategory_obj _ hK.2⟩

/-- Membership in `D_c^[a, b]` descends along restriction of scalars to `Λ`, for `Λ ⧸ J`
finite: restriction of scalars is exact and faithful, so it reflects the vanishing of
homology sheaves. -/
lemma DerivedCategory.constructibleIn_of_derivedRestrictScalars_obj [Finite (Λ ⧸ J)] {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Λ ⧸ J)))}
    (hK : DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) T a b
      ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) (Ideal.Quotient.mk J)).obj K)) :
    DerivedCategory.constructibleIn (ModuleCat.{u + 1} (Λ ⧸ J)) T a b K :=
  ⟨boundedConstructible_of_derivedRestrictScalars_obj J hK.1,
    Functor.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj _ hK.2⟩

/-- For `Λ ⧸ J` finite, a pro-étale complex of `Λ ⧸ J`-modules lies in `D_c^[a, b]` if and only
if its restriction of scalars to `Λ` does. -/
lemma DerivedCategory.constructibleIn_derivedRestrictScalars_obj_iff [Finite (Λ ⧸ J)] (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Λ ⧸ J)))) :
    DerivedCategory.constructibleIn (ModuleCat.{u + 1} Λ) T a b
        ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) (Ideal.Quotient.mk J)).obj K) ↔
      DerivedCategory.constructibleIn (ModuleCat.{u + 1} (Λ ⧸ J)) T a b K :=
  ⟨constructibleIn_of_derivedRestrictScalars_obj J, constructibleIn_derivedRestrictScalars_obj J⟩

end Constructible

end AlgebraicGeometry.ProEtale
