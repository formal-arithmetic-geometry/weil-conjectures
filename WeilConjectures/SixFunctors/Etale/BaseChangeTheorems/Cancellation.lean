/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective

/-!
# Composition, cancellation and target locality of the base change property

For a coefficient ring `Λ` which is torsion as an additive group, the base change property
`AlgebraicGeometry.Etale.HasTorsionBaseChange` of proper morphisms

- is stable under composition (`AlgebraicGeometry.Etale.HasTorsionBaseChange.comp`);
- cancels along proper surjections: if `f` is proper and surjective and `f` and `f ≫ h` have the
  property, then so does `h` (`AlgebraicGeometry.Etale.HasTorsionBaseChange.of_comp`).

Composition is the vertical pasting law of the derived base change map. Cancellation is proved
on the side of injective acyclicity: an injective sheaf `I` on `Y` is a direct summand of
`f_* J` for an injective `J` on `X` (`AlgebraicGeometry.Etale.mono_homEquiv_of_surjective`), and
the higher direct images of the base change of `f_* J` along `h` vanish because
`R(h'f')_* = Rh'_* ∘ Rf'_*` and both `Rf'_*` and `R(h'f')_*` kill the higher cohomology of the
base change of `J`.

Finally, for an arbitrary coefficient ring the base change property is local on the target
(`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_affineOpens`).

## References

- Stacks Project, Lemma 59.91.7, <https://stacks.math.columbia.edu/tag/0A4C>
- Stacks Project, Lemma 59.91.8, <https://stacks.math.columbia.edu/tag/0A4D>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- The right derived functor of a left exact functor `F` sends an `F`-acyclic object `M`
placed in degree `0` to `F.obj M` placed in degree `0`: the single complex `M[0]` is a bounded
below complex of `F`-acyclic objects, on which the unit of the right derived functor is an
isomorphism (`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`). -/
noncomputable def rightDerivedFunctorPlusObjSingleFunctorIsoOfRightAcyclic (M : C)
    (hM : F.rightAcyclic M) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj M) ≅
      (DerivedCategory.Plus.singleFunctor D 0).obj (F.obj M) :=
  let K : CochainComplex.Plus C := ⟨(CochainComplex.singleFunctor C 0).obj M, ⟨0, inferInstance⟩⟩
  have : IsIso (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj K)) :=
    F.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic K fun n ↦ by
      by_cases hn : n = 0
      · subst hn
        exact F.rightAcyclic.prop_of_iso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).symm hM
      · exact F.rightAcyclic.prop_of_isZero
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M n hn)
  (asIso (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj K))).symm ≪≫
    mapHomotopyCategoryPlusSingleFunctorQhObjIso F 0 M

end CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Composition stability of the base change property.** For a torsion coefficient ring `Λ`,
if `f : X ⟶ Y` and `h : Y ⟶ Z` satisfy the base change property, so does `f ≫ h`. For a
torsion ring the property is `AlgebraicGeometry.Etale.IsBaseChangeIso`, which is stable under
composition by the vertical pasting law of the derived base change map.
(blueprint: `prop-weil-pbc-composition-stability`, `lemma-weil-pbc-composition`) -/
@[stacks 0A4D]
theorem Etale.HasTorsionBaseChange.comp (hΛ : IsAddTorsion Λ) {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} (hf : Etale.HasTorsionBaseChange Λ f)
    (hh : Etale.HasTorsionBaseChange Λ h) : Etale.HasTorsionBaseChange Λ (f ≫ h) :=
  have := Etale.isBaseChangeIso_of_hasTorsionBaseChange Λ hΛ hf
  have := Etale.isBaseChangeIso_of_hasTorsionBaseChange Λ hΛ hh
  have := Etale.IsBaseChangeIso.comp (ModuleCat.{u + 1} Λ) f h
  Etale.hasTorsionBaseChange_of_isBaseChangeIso Λ (f ≫ h)

/-- **Composition stability of injective acyclicity.** For a torsion coefficient ring `Λ` and
proper morphisms `f : X ⟶ Y`, `h : Y ⟶ Z` with injective acyclicity, `f ≫ h` has injective
acyclicity. (blueprint: `prop-weil-pbc-composition-stability`, `lemma-weil-pbc-composition`) -/
theorem Etale.HasInjectiveAcyclicity.comp (hΛ : IsAddTorsion Λ) {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} [IsProper f] [IsProper h] (hf : Etale.HasInjectiveAcyclicity Λ f)
    (hh : Etale.HasInjectiveAcyclicity Λ h) : Etale.HasInjectiveAcyclicity Λ (f ≫ h) :=
  (Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity Λ hΛ (f ≫ h)).1
    (Etale.HasTorsionBaseChange.comp Λ hΛ
      ((Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity Λ hΛ f).2 hf)
      ((Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity Λ hΛ h).2 hh))

/-- **The retract supplied by a surjection.** Let `f : X ⟶ Y` be surjective, let `I` be a sheaf
on `Y` and `ι : f^* I ⟶ J` a monomorphism. Then the adjoint map `I ⟶ f_* J` is a monomorphism:
at a geometric point `ȳ` of `Y`, choose a geometric point `x̄` of `X` above it; the stalk map
`I_ȳ ⟶ (f_* J)_ȳ` followed by the restriction to `J_x̄` is the injection
`I_ȳ = (f^* I)_x̄ ⟶ J_x̄`. Geometric stalks are conservative. If `I` is injective, the
monomorphism splits, so `I` is a direct summand of `f_* J`.
(blueprint: `lem-weil-pbc-retract-supplied`) -/
theorem Etale.mono_homEquiv_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    {I : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ι : (f)^*[ModuleCat.{u + 1} Λ].obj I ⟶ J) [Mono ι] :
    Mono ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _ ι) := by
  have := Etale.mono_unit_app_of_surjective Λ f f.surjective I
  rw [Adjunction.homEquiv_unit]
  infer_instance

/-- **Vanishing descends to a retract.** If `I` is a retract of `M` and the higher direct images
of `M` along `h` vanish in degree `q`, then so do those of `I`: the higher direct image functors
are additive, so `Rᵠh_* I` is a retract of `Rᵠh_* M = 0`.
(blueprint: `lem-weil-pbc-vanishing-descends-retract`) -/
theorem Etale.isZero_homology_rightDerivedFunctorPlus_of_retract {X Y : Scheme.{u}}
    (h : X ⟶ Y) {I M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (s : I ⟶ M)
    (r : M ⟶ I) (hsr : s ≫ r = 𝟙 I) (q : ℤ)
    (hM : IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
      (R+((h)_*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj M)))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
      (R+((h)_*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj I))) := by
  let G := DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0 ⋙ R+((h)_*[ModuleCat.{u + 1} Λ]) ⋙
    DerivedCategory.Plus.homologyFunctor (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q
  have : IsSplitMono (G.map s) := .mk' ⟨G.map r, by rw [← G.map_comp, hsr, G.map_id]⟩
  exact IsZero.of_mono (G.map s) hM

/-- **Cancellation of injective acyclicity along a proper surjection.** For a torsion
coefficient ring `Λ`, let `f : X ⟶ Y` be proper and surjective and `h : Y ⟶ Z` proper. If `f`
and `f ≫ h` have injective acyclicity, so does `h`.

Let `I` be an injective sheaf on `Y`; embed `f^* I` into an injective `J` on `X`. By
`AlgebraicGeometry.Etale.mono_homEquiv_of_surjective` the sheaf `I` is a direct summand of
`f_* J`. After a base change `Z' ⟶ Z`, the underived proper exchange identifies the base change
of `f_* J` with `f'_*` of the base change of `J`, whose higher direct images along `h'`
vanish since `Rh'_* ∘ Rf'_* = R(h'f')_*`, `IA(f)` and `IA(f ≫ h)`. The vanishing descends to the
direct summand. (blueprint: `lemma-weil-pbc-cancellation`) -/
@[stacks 0A4C]
theorem Etale.HasInjectiveAcyclicity.of_comp (hΛ : IsAddTorsion Λ) {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} [IsProper f] [Surjective f] [IsProper h]
    (hf : Etale.HasInjectiveAcyclicity Λ f) (hfh : Etale.HasInjectiveAcyclicity Λ (f ≫ h)) :
    Etale.HasInjectiveAcyclicity Λ h := by
  intro Z' Y' c h' b sq I _ _ q hq
  let ι := Injective.ι ((f)^*[ModuleCat.{u + 1} Λ].obj I)
  let J := Injective.under ((f)^*[ModuleCat.{u + 1} Λ].obj I)
  let s := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _ ι
  have := Etale.mono_homEquiv_of_surjective Λ f ι
  have hsr : s ≫ Injective.factorThru (𝟙 I) s = 𝟙 I := Injective.comp_factorThru _ _
  have sq₁ : IsPullback (pullback.fst f b) (pullback.snd f b) f b := IsPullback.of_hasPullback f b
  have : IsTorsionSheaf J := .of_isTorsion hΛ J
  have hJ := hf.rightAcyclic Λ sq₁ J
  refine Etale.isZero_homology_rightDerivedFunctorPlus_of_retract Λ h'
    ((b)^*[ModuleCat.{u + 1} Λ].map s)
    ((b)^*[ModuleCat.{u + 1} Λ].map (Injective.factorThru (𝟙 I) s))
    (by rw [← Functor.map_comp, hsr, CategoryTheory.Functor.map_id]) q ?_
  have : IsIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq₁.toCommSq).app J) := by
    have := Etale.isIso_baseChangeMap_of_isProper Λ sq₁
    infer_instance
  refine IsZero.of_iso (hfh (sq₁.paste_vert sq) J inferInstance inferInstance q hq) ?_
  exact (DerivedCategory.Plus.homologyFunctor _ q).mapIso
    ((R+((h')_*[ModuleCat.{u + 1} Λ])).mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
        (asIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq₁.toCommSq).app J))) ≪≫
      (R+((h')_*[ModuleCat.{u + 1} Λ])).mapIso
        (Functor.rightDerivedFunctorPlusObjSingleFunctorIsoOfRightAcyclic _ _ hJ).symm ≪≫
      (Functor.rightDerivedFunctorPlusCompIso' _ _
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (pullback.snd f b) h')).app _)

/-- **Cancellation of the base change property along a proper surjection.** For a torsion
coefficient ring `Λ`, let `f : X ⟶ Y` be proper and surjective and `h : Y ⟶ Z` proper. If `f`
and `f ≫ h` satisfy the base change property, so does `h`. This is
`AlgebraicGeometry.Etale.HasInjectiveAcyclicity.of_comp` transported along the equivalence of
the base change property and injective acyclicity.
(blueprint: `lemma-weil-pbc-cancellation`) -/
@[stacks 0A4C]
theorem Etale.HasTorsionBaseChange.of_comp (hΛ : IsAddTorsion Λ) {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {h : Y ⟶ Z} [IsProper f] [Surjective f] [IsProper h]
    (hf : Etale.HasTorsionBaseChange Λ f) (hfh : Etale.HasTorsionBaseChange Λ (f ≫ h)) :
    Etale.HasTorsionBaseChange Λ h :=
  (Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity Λ hΛ h).2
    (Etale.HasInjectiveAcyclicity.of_comp Λ hΛ
      ((Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity Λ hΛ f).1 hf)
      ((Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity Λ hΛ (f ≫ h)).1 hfh))

/-- **Target locality of the base change property.** A morphism `f : X ⟶ Y` satisfies the base
change property as soon as its restrictions `f ∣_ U : f ⁻¹ᵁ U ⟶ U` over all affine opens `U`
of `Y` do: the derived base change map of a cartesian square over `Y` is an isomorphism as soon
as its pullbacks over the members of the open cover of the base change by the preimages of
the `U` are (`AlgebraicGeometry.Etale.isIso_baseChange_app_of_etale_cover`).
(blueprint: `lemma-weil-pbc-target-locality`) -/
theorem Etale.hasTorsionBaseChange_of_affineOpens {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ U : Y.affineOpens, Etale.HasTorsionBaseChange Λ (f ∣_ (U : Y.Opens))) :
    Etale.HasTorsionBaseChange Λ f := by
  intro Y' X' g f' g' sq K hK
  rw [← Etale.baseChange_eq_derivedBaseChangeMapPlus]
  refine Etale.isIso_baseChange_app_of_etale_cover Λ (ι := Y.affineOpens)
    (fun U ↦ (g ⁻¹ᵁ (U : Y.Opens)).ι) (fun x ↦ ?_) (fun U ↦ g ∣_ (U : Y.Opens))
    (fun U ↦ (U : Y.Opens).ι) (fun U ↦ morphismRestrict_ι g U)
    (fun U ↦ (f ⁻¹ᵁ (U : Y.Opens)).ι) (fun U ↦ f ∣_ (U : Y.Opens))
    (fun U ↦ (isPullback_morphismRestrict f U).flip)
    (fun U ↦ pullback.fst (f ∣_ (U : Y.Opens)) (g ∣_ (U : Y.Opens)))
    (fun U ↦ pullback.snd (f ∣_ (U : Y.Opens)) (g ∣_ (U : Y.Opens)))
    (fun U ↦ IsPullback.of_hasPullback _ _) sq K fun U ↦ ?_
  · obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (g.base x)) isOpen_univ
    exact ⟨⟨U, hU⟩, ⟨x, hx⟩, rfl⟩
  · rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
    refine h U (IsPullback.of_hasPullback _ _) _ fun n ↦ ?_
    exact @Scheme.IsTorsionSheaf.of_epi _ _ _ _ _
      ((((f ⁻¹ᵁ (U : Y.Opens)).ι)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryPlusHomologyFunctorIso
        n).hom.app K) inferInstance (@isTorsionSheaf_upperStar _ _ _ _ _ _ (hK n))

end AlgebraicGeometry
