/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.GenericModel
public import WeilConjectures.ConstructibleSheaf.FiniteDerived
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve.NoetherianInduction
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve.Sigma
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.TargetLocal
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Constant coefficients on projective families of curves: reduction to smooth families

Let `f : X ⟶ S` be projective with `S` of finite type over a field and geometric fibres of
dimension at most one, and let `ℓ` be a prime invertible on `S`. This file proves that the higher
direct images `Rᵠf_* 𝔽_ℓ` are constructible provided that this holds for smooth projective
families of curves (`thm-fin-projective-smooth-curve-finiteness`), following the proof of
`thm-fin-projective-curve-constant`
(`AlgebraicGeometry.Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_zmod_of_smooth`):

- over an integral base, after restriction to a nonempty open and a finite surjective base change
  `p : S' ⟶ S`, the generic curve model `lem-fin-generic-curve-model` compares the reduced family
  `T = (X_{S'})_red` with a finite disjoint union of smooth projective curve families and finite
  étale families, through a finite modification (`lem-finrepair-constant-finite-comparison`);
  proper base change identifies `p^* Rᵠf_* 𝔽_ℓ` with the direct images for `X_{S'} ⟶ S'`, and
  `Rᵠf_* 𝔽_ℓ` embeds into the constructible sheaf `p_* p^* Rᵠf_* 𝔽_ℓ`
  (`AlgebraicGeometry.Etale.exists_isConstructibleSheaf_upperStar_homology_zmod_of_isIntegral`);
- Noetherian induction over integral subschemes
  (`AlgebraicGeometry.Scheme.isConstructibleSheaf_of_forall_isIntegral`) passes from this
  dense-open assertion to all of `S`, proper base change identifying the restrictions of the
  direct images with the direct images of the restricted families.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory

section BaseChange

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- **Proper base change for higher direct images.** For a cartesian square with `f` proper, the
pullback along `g` of `Rᵠf_* F` is `Rᵠf'_*(g'^* F)`
(`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology`), the coefficient
ring being finite. -/
noncomputable def upperStarHomologyRightDerivedLowerStarIsoOfIsProper {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    [IsProper f] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (g)^*[ModuleCat.{u + 1} Λ].obj ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F))) ≅
    (homologyFunctor _ q).obj ((R((f')_*[ModuleCat.{u + 1} Λ])).obj
      ((singleFunctor _ 0).obj ((g')^*[ModuleCat.{u + 1} Λ].obj F))) :=
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  have := Etale.isIso_baseChange_of_isProper_of_torsionHomology Λ sq K
    (Etale.DerivedCategory.Plus.moduleTorsionHomology_of_isTorsion Λ X isAddTorsion_of_finite K)
  (g)^*[ModuleCat.{u + 1} Λ].mapIso ((homologyFunctor _ q).mapIso
      (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app K).symm) ≪≫
    ((g)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlusHomologyFunctorIso q).app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (asIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (((f')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.mapIso
        (((g')^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlusSingleFunctor 0).app F)) ≪≫
    (homologyFunctor _ q).mapIso
      (((f')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app _)

/-- **Proper base change for constant coefficients.** For a cartesian square with `f` proper,
the pullback along `g` of `Rᵠf_* M` is `Rᵠf'_* M`, for the constant sheaves `M`. -/
noncomputable def upperStarHomologyRightDerivedLowerStarConstantIsoOfIsProper
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) [IsProper f] (M : ModuleCat.{u + 1} Λ) (q : ℤ) :
    (g)^*[ModuleCat.{u + 1} Λ].obj ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) ≅
    (homologyFunctor _ q).obj ((R((f')_*[ModuleCat.{u + 1} Λ])).obj
      ((singleFunctor _ 0).obj ((constantSheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        M))) :=
  upperStarHomologyRightDerivedLowerStarIsoOfIsProper sq _ q ≪≫
    (homologyFunctor _ q).mapIso ((R((f')_*[ModuleCat.{u + 1} Λ])).mapIso
      ((singleFunctor _ 0).mapIso ((upperStarConstantSheafIso _ g').app M)))

end BaseChange

section Thickening

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Direct images are insensitive to thickenings.** For a surjective closed immersion
`t : T ⟶ P` and `g : P ⟶ S`, `Rᵠg_* F ≅ Rᵠ(t ≫ g)_*(t^* F)`: the pullback `t^*` is an equivalence
(`AlgebraicGeometry.Etale.isEquivalence_upperStar_of_thickening`), so `F ≅ t_* t^* F`, and `t_*`
is exact. -/
noncomputable def homologyRightDerivedLowerStarThickeningIso {T P S : Scheme.{u}} (t : T ⟶ P)
    [IsClosedImmersion t] (ht : Function.Surjective t.base) (g : P ⟶ S)
    (F : Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (homologyFunctor _ q).obj ((R((g)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F))
      ≅ (homologyFunctor _ q).obj ((R((t ≫ g)_*[ModuleCat.{u + 1} Λ])).obj
        ((singleFunctor _ 0).obj ((t)^*[ModuleCat.{u + 1} Λ].obj F))) :=
  have := isEquivalence_upperStar_of_thickening (ModuleCat.{u + 1} Λ) t ht
  have : IsIso (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).unit :=
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).unit_isIso_of_L_fully_faithful
  have : IsFinite t := ((IsClosedImmersion.iff_isFinite_and_mono t).1 inferInstance).1
  (homologyFunctor _ q).mapIso ((R((g)_*[ModuleCat.{u + 1} Λ])).mapIso ((singleFunctor _ 0).mapIso
      (asIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).unit.app F)))) ≪≫
    (homologyFunctor _ q).mapIso (rightDerivedLowerStarSingleLowerStarIso t g _)

end Thickening
section Finite

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- **Constant coefficients along a finite morphism.** For a finite morphism `π : Y ⟶ S` with
`S` Noetherian and a finite `Λ`-module `M`, every `Rᵠπ_* M` is constructible: it is `π_* M` for
`q = 0`, constructible by `lem-fin-finite-morphism`, and zero otherwise. -/
lemma isConstructibleSheaf_homology_rightDerivedLowerStar_constantSheaf_of_isFinite
    {Y S : Scheme.{u}} [IsNoetherian S] (π : Y ⟶ S) [IsFinite π] (M : ModuleCat.{u + 1} Λ)
    [Finite M] (q : ℤ) :
    IsConstructibleSheaf ((homologyFunctor _ q).obj ((R((π)_*[ModuleCat.{u + 1} Λ])).obj
      ((singleFunctor _ 0).obj ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        M)))) := by
  let F := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  by_cases hq : q = 0
  · subst hq
    have : IsConstructibleSheaf F :=
      (isFiniteLocallyConstantSheaf_constantSheaf M).isConstructibleSheaf
    have : IsConstructibleSheaf ((𝟭 _).obj ((π)_*[ModuleCat.{u + 1} Λ].obj F)) :=
      Scheme.IsConstructibleSheaf.lowerStar_of_isFinite π F
    exact IsConstructibleSheaf.of_iso ((homologyFunctor _ 0).mapIso
      ((rightDerivedFunctorLowerStarIsoMapDerivedCategory _ π).app _ ≪≫
        (((π)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app F) ≪≫
      (singleFunctorCompHomologyFunctorIso _ 0).app _).symm
  · exact IsConstructibleSheaf.of_isZero
      (isZero_homology_rightDerivedLowerStar_singleFunctor_of_isFinite π F q hq)

end Finite

variable {k : Type u} [Field k]

/-- **The integral case of `thm-fin-projective-curve-constant`.** Let `W` be integral of finite
type over `k`, `f : X ⟶ W` projective with geometric fibres of dimension at most one, and `ℓ` a
prime invertible on `W`. Suppose that the higher direct images of `𝔽_ℓ` along smooth projective
families of curves over Noetherian bases are constructible. Then the restrictions of the
`Rᵠf_* 𝔽_ℓ` to some nonempty open subscheme of `W` are constructible.

Over the open `U` of the generic curve model (`lem-fin-generic-curve-model`), with its finite
surjection `p : S' ⟶ U`, the direct images along the members `Yₐ ⟶ S'` of the model are
constructible (smooth curve families by hypothesis, finite étale ones by
`lem-fin-finite-morphism`), hence so are those along `∐ Yₐ ⟶ S'`, hence those along the reduced
family `T ⟶ S'` by the finite comparison `lem-finrepair-constant-finite-comparison`, hence those
along `X_U ×_U S' ⟶ S'` (the thickening `T ⟶ X_U ×_U S'` does not change étale cohomology). By
proper base change these are the `p^* Rᵠf_* 𝔽_ℓ`, and `Rᵠf_* 𝔽_ℓ` embeds into the constructible
sheaf `p_* p^* Rᵠf_* 𝔽_ℓ`. -/
theorem exists_isConstructibleSheaf_upperStar_homology_zmod_of_isIntegral (ℓ : ℕ) [Fact ℓ.Prime]
    (hsmooth : ∀ {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
      {n : Type u} [Finite n] (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i], i ≫ ℙ(n; S) ↘ S = f →
      ∀ [HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S] (r : ℤ),
      IsConstructibleSheaf ((homologyFunctor _ r).obj
        ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
          ((singleFunctor _ 0).obj
            ((constantSheaf X.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
              (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))))))
    {X W : Scheme.{u}} [IsIntegral W] (aW : W ⟶ Spec (.of k)) [LocallyOfFiniteType aW]
    [QuasiCompact aW] (f : X ⟶ W) {n : Type u} [Finite n] (i : X ⟶ ℙ(n; W))
    [IsClosedImmersion i] (hi : i ≫ ℙ(n; W) ↘ W = f)
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ W),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ 1)
    [HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) W] :
    ∃ U : W.Opens, (U : Set W).Nonempty ∧ ∀ q : ℤ, IsConstructibleSheaf
      ((U.ι)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj ((homologyFunctor _ q).obj
        ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
          ((singleFunctor _ 0).obj
            ((constantSheaf X.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
              (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))))))) := by
  obtain ⟨U, hU, S', _, p, _, _, T, t, _, _, _, ι, _, Y, ν, _, _, D, d, _, hd, hν, hY⟩ :=
    exists_isFinite_sigmaDesc_genericCurveModel aW f i hi hf
  refine ⟨U, Set.nonempty_iff_ne_empty.2 fun h ↦ hU (TopologicalSpace.Opens.ext (by simpa using h)),
    fun q ↦ ?_⟩
  let Λ := ULift.{u + 1} (ZMod ℓ)
  let M : ModuleCat.{u + 1} Λ := ModuleCat.of Λ Λ
  have : Finite M := inferInstanceAs (Finite Λ)
  -- finiteness properties of the bases
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian aW
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace aW
  have : IsNoetherian W := {}
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian U.ι
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace U.ι
  have : IsNoetherian U := {}
  let aS' : S' ⟶ Spec (.of k) := p ≫ U.ι ≫ aW
  have : IsLocallyNoetherian S' := LocallyOfFiniteType.isLocallyNoetherian aS'
  have : CompactSpace S' := QuasiCompact.compactSpace_of_compactSpace aS'
  have : IsNoetherian S' := {}
  have : HasInvertibleExponent Λ S' := HasInvertibleExponent.of_hom (p ≫ U.ι)
  have : IsProper f := by
    rw [← hi]
    infer_instance
  -- the restricted family and its base change along `p`
  let fU := f ∣_ U
  let g := pullback.snd fU p
  let h := t ≫ g
  have : IsProper h := inferInstance
  -- the direct images along `T ⟶ S'` are constructible
  have hT : ∀ q : ℤ, IsConstructibleSheaf ((homologyFunctor _ q).obj
      ((R((h)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
    let V : T.Opens := ⟨(Set.range d.base)ᶜ, d.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have hdV : Set.range V.ι.base = (Set.range d.base)ᶜ := by
      rw [Scheme.Opens.range_ι]
      rfl
    have hνV : IsIso (pullback.snd ν V.ι) := by
      have : IsIso ((pullbackRestrictIsoRestrict ν V).inv ≫ pullback.snd ν V.ι) := hν
      exact IsIso.of_isIso_comp_left (pullbackRestrictIsoRestrict ν V).inv _
    have : IsFinite (d ≫ h) := hd
    refine (constructible_and_isIso_rightDerivedLowerStarUnitComparison aS' h ν d V.ι hdV hνV M
      fun q ↦ ?_).1
    refine isConstructibleSheaf_homology_rightDerivedLowerStar_sigma Y (ν ≫ h) _ q fun a ↦ ?_
    let e : (Sigma.ι Y a)^*[ModuleCat.{u + 1} Λ].obj ((ν)^*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ≅
        (constantSheaf (Y a).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M :=
      (Sigma.ι Y a)^*[ModuleCat.{u + 1} Λ].mapIso ((upperStarConstantSheafIso _ ν).app M) ≪≫
        (upperStarConstantSheafIso _ (Sigma.ι Y a)).app M
    have hc : IsConstructibleSheaf ((homologyFunctor _ q).obj
        ((R((Sigma.ι Y a ≫ ν ≫ h)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
          ((constantSheaf (Y a).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
      rcases hY a with ⟨⟨m, _, jm, _, hjm⟩, _⟩ | ⟨_, _⟩
      · exact hsmooth (Sigma.ι Y a ≫ ν ≫ h) jm hjm q
      · exact isConstructibleSheaf_homology_rightDerivedLowerStar_constantSheaf_of_isFinite
          (Sigma.ι Y a ≫ ν ≫ h) M q
    exact IsConstructibleSheaf.of_iso ((homologyFunctor _ q).mapIso
      ((R((Sigma.ι Y a ≫ ν ≫ h)_*[ModuleCat.{u + 1} Λ])).mapIso
        ((singleFunctor _ 0).mapIso e.symm)))
  -- hence those along `X_U ×_U S' ⟶ S'`
  have hg : IsConstructibleSheaf ((homologyFunctor _ q).obj
      ((R((g)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf (pullback fU p).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
    have := hT q
    exact IsConstructibleSheaf.of_iso ((homologyFunctor _ q).mapIso
      ((R((h)_*[ModuleCat.{u + 1} Λ])).mapIso ((singleFunctor _ 0).mapIso
        ((upperStarConstantSheafIso _ t).app M).symm)) ≪≫
      (homologyRightDerivedLowerStarThickeningIso t (Surjective.surj) g _ q).symm)
  -- by proper base change, `p^* Rᵠf_{U*} 𝔽_ℓ` is constructible, hence so is `Rᵠf_{U*} 𝔽_ℓ`
  let E := (homologyFunctor _ q).obj ((R((fU)_*[ModuleCat.{u + 1} Λ])).obj
    ((singleFunctor _ 0).obj ((constantSheaf (f ⁻¹ᵁ U).toScheme.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj M)))
  have hE : IsConstructibleSheaf E := by
    have : IsConstructibleSheaf ((p)^*[ModuleCat.{u + 1} Λ].obj E) := IsConstructibleSheaf.of_iso
      (upperStarHomologyRightDerivedLowerStarConstantIsoOfIsProper
        (IsPullback.of_hasPullback fU p) M q).symm
    have : IsConstructibleSheaf (((p)^*[ModuleCat.{u + 1} Λ] ⋙
        (p)_*[ModuleCat.{u + 1} Λ]).obj E) :=
      Scheme.IsConstructibleSheaf.lowerStar_of_isFinite p _
    have := Etale.mono_unit_app_of_surjective Λ p p.surjective E
    exact Scheme.IsConstructibleSheaf.of_mono
      ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app E)
  exact IsConstructibleSheaf.of_iso ((upperStarHomologyRightDerivedLowerStarIso
    (isPullback_morphismRestrict f U).flip _ q ≪≫ (homologyFunctor _ q).mapIso
      ((R((fU)_*[ModuleCat.{u + 1} Λ])).mapIso ((singleFunctor _ 0).mapIso
        ((upperStarConstantSheafIso _ (f ⁻¹ᵁ U).ι).app M)))).symm)

/-- **Reduction of `thm-fin-projective-curve-constant` to smooth families of curves.** Let
`f : X ⟶ S` be projective with `S` of finite type over a field `k`, all of whose geometric fibres
have dimension at most one, and let `ℓ` be a prime invertible on `S`. If the higher direct images
of `𝔽_ℓ` along smooth projective families of curves over Noetherian bases are constructible, then
every `Rᵠf_* 𝔽_ℓ` is constructible.

By Noetherian induction over integral subschemes
(`AlgebraicGeometry.Scheme.isConstructibleSheaf_of_forall_isIntegral`) it suffices to find, for
every immersion `w : W ⟶ S` of an integral scheme, a nonempty open of `W` over which the pullback
of `Rᵠf_* 𝔽_ℓ` is constructible. By proper base change that pullback is the direct image along
the projective family `X ×_S W ⟶ W`, whose geometric fibres are geometric fibres of `f`, and the
integral case
`AlgebraicGeometry.Etale.exists_isConstructibleSheaf_upperStar_homology_zmod_of_isIntegral`
applies. -/
theorem isConstructibleSheaf_homology_rightDerivedLowerStar_zmod_of_smooth (ℓ : ℕ)
    [Fact ℓ.Prime]
    (hsmooth : ∀ {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
      {n : Type u} [Finite n] (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i], i ≫ ℙ(n; S) ↘ S = f →
      ∀ [HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S] (r : ℤ),
      IsConstructibleSheaf ((homologyFunctor _ r).obj
        ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
          ((singleFunctor _ 0).obj
            ((constantSheaf X.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
              (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))))))
    {X S : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (f : X ⟶ S) {n : Type u} [Finite n] (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i]
    (hi : i ≫ ℙ(n; S) ↘ S = f)
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ 1)
    [HasInvertibleExponent (ULift.{u + 1} (ZMod ℓ)) S] (q : ℤ) :
    IsConstructibleSheaf ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
        ((singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))))) := by
  let Λ := ULift.{u + 1} (ZMod ℓ)
  let M : ModuleCat.{u + 1} Λ := ModuleCat.of Λ Λ
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian aS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace aS
  have : IsNoetherian S := {}
  have : IsProper f := by
    rw [← hi]
    infer_instance
  refine Scheme.isConstructibleSheaf_of_forall_isIntegral _ fun W w _ _ ↦ ?_
  have : TopologicalSpace.NoetherianSpace W := w.isEmbedding.isInducing.noetherianSpace
  -- the restricted family over `W`
  let fW := pullback.snd f w
  have hw : pullback.snd f w ≫ w = (pullback.fst f w ≫ i) ≫ ℙ(n; S) ↘ S := by
    rw [Category.assoc, hi, pullback.condition]
  let iW : pullback f w ⟶ ℙ(n; W) := ProjectiveSpace.liftBaseChange _ _ hw
  have hφ := ProjectiveSpace.isPullback_liftBaseChange _
    (show IsPullback (pullback.fst f w) (pullback.snd f w) (i ≫ ℙ(n; S) ↘ S) w by
      rw [hi]
      exact IsPullback.of_hasPullback f w) hw
  have : IsClosedImmersion iW := MorphismProperty.of_isPullback hφ inferInstance
  have hfW : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ W),
      topologicalKrullDim (pullback fW s : Scheme.{u}) ≤ 1 := fun Ω _ _ s ↦ by
    rw [← IsHomeomorph.topologicalKrullDim_eq _
      (pullbackLeftPullbackSndIso f w s).inv.homeomorph.isHomeomorph]
    exact hf Ω (s ≫ w)
  have : HasInvertibleExponent Λ W := HasInvertibleExponent.of_hom w
  obtain ⟨U, hU, hc⟩ := exists_isConstructibleSheaf_upperStar_homology_zmod_of_isIntegral ℓ
    hsmooth (w ≫ aS) fW iW (ProjectiveSpace.liftBaseChange_over _ _ hw) hfW
  refine ⟨U, hU, ?_⟩
  have := hc q
  exact IsConstructibleSheaf.of_iso ((U.ι)^*[ModuleCat.{u + 1} Λ].mapIso
      (upperStarHomologyRightDerivedLowerStarConstantIsoOfIsProper
        (IsPullback.of_hasPullback f w) M q).symm ≪≫
    ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) U.ι w).app _).symm)

end Etale

end AlgebraicGeometry
