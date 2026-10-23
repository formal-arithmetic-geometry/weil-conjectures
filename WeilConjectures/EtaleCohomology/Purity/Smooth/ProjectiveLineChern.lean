/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineCompactification
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsOpenImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!
# The first Chern class of `𝒪(1)` on the projective line, and the cohomology of `ℙ¹`

**Excision.** Let `e : U ⟶ X` be an open immersion and `i : Z ⟶ X` a closed immersion whose
image lies in `U`. Then restricting classes with supports in `Z` along `e` is a bijection
(`AlgebraicGeometry.Etale.bijective_restrictSupportedClass_of_isOpenImmersion`): for `B`
supported on `Z`, the unit `B ⟶ Re_* Le^* B` is an isomorphism, as one checks on `U` and on its
closed complement.

**The class of the point at infinity.** On `ℙ¹_S` the section `∞` is the zero locus `V(z)` of the
coordinate `z` of the chart at infinity `𝔸¹_S ⟶ ℙ¹_S`. By excision, the Kummer boundary
`∂κ(z)` defines a class `cl(∞) ∈ H²_∞(ℙ¹_S, Λ(1))`
(`AlgebraicGeometry.Etale.projectiveLineInfinityClass`), the Kummer class of the divisor `∞`
(`lem-pur-divisor-class`). Forgetting supports gives the Kummer first Chern class
`c₁(𝒪(1)) = c₁(𝒪(∞)) ∈ H²(ℙ¹_S, Λ(1))`
(`AlgebraicGeometry.Etale.projectiveLineChernClass`).

**The cohomology of `ℙ¹`.** The unit `Λ_S ⟶ Rq_* Λ` and `c₁(𝒪(1))` decompose
`Rq_* Λ_{ℙ¹_S} ≅ Λ_S ⊕ Λ_S(-1)[-2]` (`thm-amb-p1-decomposition`, recorded without proof:
`AlgebraicGeometry.Etale.isIso_biprod_desc_projectiveLine`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section Excision

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X U Z Z' : Scheme.{u}} (e : U ⟶ X)
  [IsOpenImmersion e] (i : Z ⟶ X) (i' : Z' ⟶ U) [IsClosedImmersion i] [IsClosedImmersion i']
  (g : Z' ⟶ Z) (hg : IsPullback g i' i e) (hZ : Set.range i.base ⊆ Set.range e.base)

include hg hZ in
/-- For `B = Ri_! N` supported on a closed `Z` contained in the open `U`, the unit
`B ⟶ Re_* Le^* B` of `Le^* ⊣ Re_*` is an isomorphism. On `U` it is inverse to the counit, which
is invertible for the open immersion `e`; on the closed complement of `U` both sides vanish:
`Le^* B` is supported on `Z' = Z ∩ U`, so `Re_* Le^* B ≅ Ri_* Rg_* Ri'^! Le^* B`. -/
theorem isIso_unit_app_rightDerivedLowerShriek_of_isOpenImmersion
    (N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) e).unit.app
      ((R(i)_![ModuleCat.{u + 1} Λ]).obj N)) := by
  set A := ModuleCat.{u + 1} Λ
  set B := (R(i)_![A]).obj N
  set F := e.opensRange.closedComplement
  have hij : Set.range F.base = (Set.range e.base)ᶜ := e.opensRange.range_closedComplement
  have hP := (jointlyReflectIsomorphisms_mapDerivedCategoryUpperStar' A e F hij).pairFunctor_of_iso
    (leftDerivedUpperStarIsoMapDerivedCategory A e).symm
    (leftDerivedUpperStarIsoMapDerivedCategory A F).symm
  refine hP.isIso_of_pairFunctor _ ?_ ?_
  · -- on `U`, `Le^* η` is inverse to the counit
    have h := (derivedUpperStarLowerStarAdjunction A e).left_triangle_components B
    have : IsIso ((L((e)^*[A])).map ((derivedUpperStarLowerStarAdjunction A e).unit.app B) ≫
        (derivedUpperStarLowerStarAdjunction A e).counit.app ((L((e)^*[A])).obj B)) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ ((derivedUpperStarLowerStarAdjunction A e).counit.app _)
  · -- on the closed complement both sides vanish
    have hdisj : Disjoint (Set.range F.base) (Set.range i.base) := by
      rw [hij]
      exact Disjoint.mono_right hZ disjoint_compl_left
    have h₁ : IsZero ((L((F)^*[A])).obj B) :=
      isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint A i N F hdisj
    -- `Le^* B ≅ Ri'_! M` with `M = Ri'^! Le^* B`
    have hsupp := isZero_leftDerivedUpperStar_openComplement_obj Λ e i i' g hg N
    have := isIso_counit_app_of_isZero Λ i' _ hsupp
    set M := (R(i')^![A]).obj ((L((e)^*[A])).obj B)
    let θ : (R((e)_*[A])).obj ((L((e)^*[A])).obj B) ≅
        (R((i)_*[A])).obj ((R((g)_*[A])).obj M) :=
      (R((e)_*[A])).mapIso
          (asIso ((rightDerivedUpperShriekAdjunction A i').counit.app _)).symm ≪≫
        (R((e)_*[A])).mapIso ((rightDerivedLowerShriekIsoRightDerivedLowerStar A i').app M) ≪≫
        (rightDerivedLowerStarComp A i' e).app M ≪≫
        (rightDerivedLowerStarCongr A hg.w.symm).app M ≪≫
        ((rightDerivedLowerStarComp A g i).app M).symm
    have h₂ : IsZero ((L((F)^*[A])).obj ((R((e)_*[A])).obj ((L((e)^*[A])).obj B))) :=
      (isZero_leftDerivedUpperStar_rightDerivedLowerShriek_of_disjoint A i
        ((R((g)_*[A])).obj M) F hdisj).of_iso
        ((L((F)^*[A])).mapIso (θ ≪≫
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar A i).app _).symm))
    exact isIso_of_source_target_iso_zero _ h₁.isoZero h₂.isoZero

include hg hZ in
/-- **Excision.** For an open immersion `e : U ⟶ X` and a closed `Z ⊆ U`, restriction of classes
with supports in `Z` along `e` is a bijection. -/
theorem bijective_restrictSupportedClass_of_isOpenImmersion
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' L' : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (σ : K' ≅ (L((e)^*[ModuleCat.{u + 1} Λ])).obj K)
    (τ : (L((e)^*[ModuleCat.{u + 1} Λ])).obj L ≅ L') :
    Function.Bijective (restrictSupportedClass (ModuleCat.{u + 1} Λ) e i i' g hg σ.hom τ) := by
  set A := ModuleCat.{u + 1} Λ
  set adj := derivedUpperStarLowerStarAdjunction A e
  set B := (R(i)_![A]).obj ((R(i)^![A]).obj L)
  have := isIso_unit_app_rightDerivedLowerShriek_of_isOpenImmersion Λ e i i' g hg hZ
    ((R(i)^![A]).obj L)
  have := isIso_supportedRestriction_of_isOpenImmersion A e i i' g hg L L' τ
  have hL : ∀ γ : K ⟶ B, (L((e)^*[A])).map γ = (adj.homEquiv _ _).symm (γ ≫ adj.unit.app B) :=
    fun γ ↦ by
      rw [Equiv.eq_symm_apply, Adjunction.homEquiv_unit]
      exact (adj.unit.naturality γ).symm
  have : restrictSupportedClass A e i i' g hg σ.hom τ =
      (fun f ↦ σ.hom ≫ f ≫ supportedRestriction A e i i' g hg L L' τ) ∘
        (adj.homEquiv _ _).symm ∘ (fun γ : K ⟶ B ↦ γ ≫ adj.unit.app B) := by
    funext γ
    simp only [restrictSupportedClass, Function.comp_apply, hL]
    rfl
  rw [this]
  refine Function.Bijective.comp ?_ ((adj.homEquiv _ _).symm.bijective.comp
    ⟨fun _ _ h ↦ (cancel_mono _).1 h, fun f ↦ ⟨f ≫ inv (adj.unit.app B), by simp⟩⟩)
  exact ⟨fun _ _ h ↦ by rwa [cancel_epi, cancel_mono] at h, fun f ↦ ⟨σ.inv ≫ f ≫
    inv (supportedRestriction A e i i' g hg L L' τ), by simp⟩⟩

end Excision

/-- The unit `Λ_Y ⟶ Rf_* Λ_X` of the derived adjunction `Lf^* ⊣ Rf_*` at the constant
complex. -/
noncomputable def constantComplexUnit (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    constantComplex Λ Y ⟶ (R((f)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app _ ≫
    (R((f)_*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ f).hom

instance (Λ : Type (u + 1)) [CommRing Λ] (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    HasInvertibleExponent Λ (ProjectiveLine S) :=
  .of_hom (ProjectiveLine S ↘ S)

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ] (S : Scheme.{u})
  [HasInvertibleExponent Λ S]

/-- The coordinate `z` of the chart at infinity `𝔸¹_S ⟶ ℙ¹_S`. -/
noncomputable abbrev infinityCoord : Γ(𝔸(PUnit.{u + 1}; S), ⊤) :=
  AffineSpace.coord S PUnit.unit

/-- The zero locus `V(z) ⊆ 𝔸¹_S` of the coordinate at infinity is `S`. -/
noncomputable def infinityZeroLocusIso :
    S ≅ (𝔸(PUnit.{u + 1}; S)).zeroLocusSubscheme {infinityCoord S} :=
  AffineSpace.zeroSectionIsoZeroLocusSubscheme PUnit.{u + 1} S Set.range_unique

/-- `V(z)` is the preimage of `∞` in the chart at infinity. -/
lemma isPullback_infinityZeroLocus :
    IsPullback (infinityZeroLocusIso S).inv
      ((𝔸(PUnit.{u + 1}; S)).zeroLocusSubschemeι {infinityCoord S})
      (ProjectiveLine.infinity S) (ProjectiveLine.infinityChart S) := by
  refine IsPullback.of_horiz_isIso_mono ⟨?_⟩
  rw [ProjectiveLine.infinity, ← Category.assoc]
  congr 1
  rw [← cancel_epi (infinityZeroLocusIso S).hom, Iso.hom_inv_id_assoc]
  exact (AffineSpace.zeroSectionIsoZeroLocusSubscheme_hom_zeroLocusSubschemeι _ _ _).symm

/-- The class of the point at infinity `cl(∞) ∈ H²_∞(ℙ¹_S, Λ(1))`: the unique class with
supports in `∞` whose restriction to the chart at infinity is the Kummer boundary `∂κ(z)` of its
coordinate (by excision,
`AlgebraicGeometry.Etale.bijective_restrictSupportedClass_of_isOpenImmersion`).
It is the Kummer class of the divisor `∞` (`lem-pur-divisor-class`). -/
noncomputable def projectiveLineInfinityClass :
    constantComplex Λ (ProjectiveLine S) ⟶
      (R(ProjectiveLine.infinity S)_![ModuleCat.{u + 1} Λ]).obj
        ((R(ProjectiveLine.infinity S)^![ModuleCat.{u + 1} Λ]).obj
          ((tateObject Λ (ProjectiveLine S) 1)⟦2 * (1 : ℤ)⟧)) :=
  (Equiv.ofBijective _ (bijective_restrictSupportedClass_of_isOpenImmersion Λ
    (ProjectiveLine.infinityChart S) (ProjectiveLine.infinity S) _ _
    (isPullback_infinityZeroLocus S) (by
      rintro _ ⟨s, rfl⟩
      exact ⟨_, rfl⟩)
    (leftDerivedUpperStarConstantComplexIso Λ (ProjectiveLine.infinityChart S)).symm
    (leftDerivedUpperStarTateShiftIso Λ (ProjectiveLine.infinityChart S) 1))).symm
    (shiftSupportedClass (ModuleCat.{u + 1} Λ) _ 2 (kummerBoundary Λ (infinityCoord S)))

/-- The isomorphism `Λ_X(0)[0] ≅ Λ_X`. -/
noncomputable def tateObjectShiftZeroIso (X : Scheme.{u}) [HasInvertibleExponent Λ X] :
    (tateObject Λ X (1 + -1))⟦2 * (1 + -1 : ℤ)⟧ ≅ constantComplex Λ X :=
  (shiftFunctorZero' _ (2 * (1 + -1 : ℤ)) (by norm_num)).app _ ≪≫
    eqToIso (by simp [tateObject]) ≪≫ HasTateTwist.twistObjectZeroIso X

/-- The Kummer first Chern class `c₁(𝒪(1)) ∈ H²(ℙ¹_S, Λ(1)) = Hom(Λ, Λ(1)[2])`: the class of the
point at infinity with supports forgotten, `c₁(𝒪(1)) = c₁(𝒪(∞))` (`lem-pur-divisor-class`). -/
noncomputable def projectiveLineChernClass :
    constantComplex Λ (ProjectiveLine S) ⟶ (tateObject Λ (ProjectiveLine S) 1)⟦2 * (1 : ℤ)⟧ :=
  projectiveLineInfinityClass Λ S ≫
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (ProjectiveLine.infinity S)).counit.app
      _

/-- The first Chern class of `𝒪(1)` twisted by `(-1)[-2]`, as a morphism
`Λ_S(-1)[-2] ⟶ Rq_* Λ_{ℙ¹_S}`: the adjoint of
`Lq^*(Λ_S(-1)[-2]) ≅ Λ(-1)[-2] ≅ Λ ⊗ Λ(-1)[-2] ⟶ Λ(1)[2] ⊗ Λ(-1)[-2] ≅ Λ`. -/
noncomputable def projectiveLineChernMap :
    (tateObject Λ S (-1))⟦2 * (-1 : ℤ)⟧ ⟶
      (R((ProjectiveLine S ↘ S)_*[ModuleCat.{u + 1} Λ])).obj
        (constantComplex Λ (ProjectiveLine S)) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (ProjectiveLine S ↘ S)).homEquiv _ _
    ((leftDerivedUpperStarTateShiftIso Λ (ProjectiveLine S ↘ S) (-1)).hom ≫
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) (ProjectiveLine S) _).inv ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) (ProjectiveLine S)).map
        (projectiveLineChernClass Λ S)).app _ ≫
      (shiftTateObjectAddIso Λ (ProjectiveLine S) 1 (-1)).hom ≫
      (tateObjectShiftZeroIso Λ (ProjectiveLine S)).hom)

/-- Blueprint `thm-amb-p1-decomposition`: The projective-line calculation before purity

Let `q : ℙ¹_S ⟶ S` be the projective line over a scheme on which the exponent of `Λ` is
invertible, and `h` the Kummer first Chern class of `𝒪(1)`
(`AlgebraicGeometry.Etale.projectiveLineChernMap`). Then

`(1, h) : Λ_S ⊕ Λ_S(-1)[-2] ⟶ Rq_* Λ_{ℙ¹_S}`

is an isomorphism, the first component being the unit of `Lq^* ⊣ Rq_*`.

This is a node of the blueprint subsection `sk-lem-geo-p1-cohomology` (where `S` is noetherian),
recorded here without proof. -/
theorem isIso_biprod_desc_projectiveLine [HasKummerClass.IsNormalized Λ] :
    IsIso (biprod.desc (constantComplexUnit Λ (ProjectiveLine S ↘ S))
      (projectiveLineChernMap Λ S)) :=
  sorry

end AlgebraicGeometry.Etale
