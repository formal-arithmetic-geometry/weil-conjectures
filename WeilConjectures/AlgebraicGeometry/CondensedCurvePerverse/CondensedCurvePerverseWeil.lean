/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverse.CondensedCurvePerverseStatement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Pullback.PullbackConstantModelConstructible
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCreatesLimits

/-! # The forgetful functor on perverse Weil sheaves with condensed coefficients

Let `C` be a quasi-compact quasi-separated scheme and `g : C ≅ C` an automorphism, in the
intended application the Frobenius of `C = C₀ ×_{k₀} k`. Pullback along `g` is an exact
autoequivalence of the module sheaves on `C`, which preserves punctual sheaves, the absence of
punctual subsheaves and constructibility. Hence its derived functor restricts to an
autoequivalence of the perverse heart `CondensedCurvePerverse.heart`, and the perverse Weil
sheaves `CondensedCurvePerverse.WeilHeart` are the algebras over this autoequivalence. The
forgetful functor to perverse sheaves on `C` therefore creates finite limits and colimits: kernels
and cokernels of perverse Weil sheaves are computed in perverse sheaves on `C`, so the functor is
exact and reflects exactness (blueprint `lemma-perverse-weil-sheaves`, part 2).

## Main declarations

- `AlgebraicGeometry.ProEtale.CondensedRing.upperStarEquivalence`: pullback along an isomorphism
  of schemes is an equivalence of module sheaves.
- `AlgebraicGeometry.ProEtale.CondensedCurvePerverse.heart_mapDerivedCategory_upperStar`: the
  derived pullback along an automorphism preserves the perverse heart.
- `AlgebraicGeometry.ProEtale.CondensedCurvePerverse.nonempty_createsFiniteLimits_forget`: the
  forgetful functor from perverse Weil sheaves to perverse sheaves creates finite limits and
  colimits.

## Implementation notes

The constructibility of a pullback is the coefficient hypothesis
`AlgebraicGeometry.ProEtale.ConstantModelPullbackStatement`, which holds for the coefficients
`E` and `ℚ̄_ℓ` of the blueprint (`AlgebraicGeometry.ProEtale.pullback_constantModelConstructible`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- If `F₁ ⋙ G₁ ≅ F₂ ⋙ G₂` and `F₂ X = 0`, then `G₁ (F₁ X) = 0`. It is stated for the
composites, so that no unfolding of `Functor.comp` is needed in the kernel. -/
private theorem isZero_obj_obj_of_iso {A B B' D : Type*} [Category A] [Category B] [Category B']
    [Category D] [HasZeroMorphisms B'] [HasZeroMorphisms D] {F₁ : A ⥤ B} {G₁ : B ⥤ D}
    {F₂ : A ⥤ B'} {G₂ : B' ⥤ D} [G₂.PreservesZeroMorphisms] (E : F₁ ⋙ G₁ ≅ F₂ ⋙ G₂) {X : A}
    (h : IsZero (F₂.obj X)) : IsZero (G₁.obj (F₁.obj X)) :=
  (G₂.map_isZero h).of_iso (E.app X)

namespace CondensedRing

/-- For `f ≫ g = 𝟙`, the pullbacks compose to the identity: `g^* ⋙ f^* ≅ (f ≫ g)^* ≅ 𝟭`. -/
def upperStarCompUpperStarIsoOfComp {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (h : f ≫ g = 𝟙 X) : upperStar Λ g ⋙ upperStar Λ f ≅ 𝟭 _ :=
  (upperStarComp Λ f g).symm ≪≫ eqToIso (by rw [h]) ≪≫ upperStarId Λ X

/-- Pullback along an isomorphism `e : C' ≅ C` of schemes is an equivalence of module sheaves,
with quasi-inverse the pullback along `e⁻¹`. -/
def upperStarEquivalence {C C' : Scheme.{u}} (e : C' ≅ C) :
    CondensedCurvePerverse.Modules Λ C ≌ CondensedCurvePerverse.Modules Λ C' :=
  CategoryTheory.Equivalence.mk (upperStar Λ e.hom) (upperStar Λ e.inv)
    (upperStarCompUpperStarIsoOfComp Λ e.inv e.hom e.inv_hom_id).symm
    (upperStarCompUpperStarIsoOfComp Λ e.hom e.inv e.hom_inv_id)

instance {C C' : Scheme.{u}} (f : C' ⟶ C) [IsIso f] : (upperStar Λ f).IsEquivalence :=
  (upperStarEquivalence Λ (asIso f)).isEquivalence_functor

end CondensedRing

namespace CondensedCurvePerverse

variable {Λ}

theorem IsPunctual.of_iso {C : Scheme.{u}} {F F' : Modules Λ C} (e : F ≅ F')
    (hF : IsPunctual Λ C F) : IsPunctual Λ C F' := by
  have := (constantModelConstructibleFiniteTor_wellDefined Λ C).1
  obtain ⟨hc, U, hU, hcl, hz⟩ := hF
  exact ⟨ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ C) e hc, U, hU, hcl,
    hz.of_iso ((CondensedRing.upperStar Λ U.ι).mapIso e).symm⟩

theorem HasNoPunctualSubsheaf.of_iso {C : Scheme.{u}} {F F' : Modules Λ C} (e : F ≅ F')
    (hF : HasNoPunctualSubsheaf Λ C F) : HasNoPunctualSubsheaf Λ C F' :=
  fun G i _ hG ↦ hF G (i ≫ e.inv) inferInstance hG

variable (hΛ : ConstantModelPullbackStatement Λ)
include hΛ

/-- The pullback of a punctual sheaf along an automorphism `f` of `C` is punctual: it vanishes
off the preimage of the finite set of closed points off which the sheaf vanishes. -/
theorem isPunctual_upperStar {C : Scheme.{u}} [CompactSpace C] [QuasiSeparatedSpace C]
    (f : C ⟶ C) [IsIso f] {F : Modules Λ C} (hF : IsPunctual Λ C F) :
    IsPunctual Λ C ((CondensedRing.upperStar Λ f).obj F) := by
  obtain ⟨hc, U, hU, hcl, hz⟩ := hF
  have hinj : Function.Injective f.base := f.isOpenEmbedding.injective
  let V : C.Opens := f ⁻¹ᵁ U
  refine ⟨(hΛ f F hc).1, V, ?_, fun x hx ↦ ?_, ?_⟩
  · exact hU.preimage hinj.injOn
  · have : f.base ⁻¹' {f.base x} = {x} := by
      ext y
      simpa using hinj.eq_iff
    rw [← this]
    exact (hcl (f.base x) hx).preimage f.base.hom.continuous
  · -- `V.ι ≫ f` factors as `f|_V ≫ U.ι`
    let g : V.toScheme ⟶ U.toScheme := f.resLE U V le_rfl
    let E : CondensedRing.upperStar Λ f ⋙ CondensedRing.upperStar Λ V.ι ≅
        CondensedRing.upperStar Λ U.ι ⋙ CondensedRing.upperStar Λ g :=
      (CondensedRing.upperStarComp Λ V.ι f).symm ≪≫
        eqToIso (by rw [Scheme.Hom.resLE_comp_ι]) ≪≫ CondensedRing.upperStarComp Λ g U.ι
    exact isZero_obj_obj_of_iso E hz

/-- The pullback of a sheaf without nonzero punctual subsheaf along an automorphism `f` of `C`
has no nonzero punctual subsheaf: a punctual subsheaf `G ⊆ f^*F` gives the punctual subsheaf
`(f⁻¹)^*G ⊆ (f⁻¹)^*f^*F ≅ F`. -/
theorem hasNoPunctualSubsheaf_upperStar {C : Scheme.{u}} [CompactSpace C]
    [QuasiSeparatedSpace C] (f : C ⟶ C) [IsIso f] {F : Modules Λ C}
    (hF : HasNoPunctualSubsheaf Λ C F) :
    HasNoPunctualSubsheaf Λ C ((CondensedRing.upperStar Λ f).obj F) := by
  intro G i _ hG
  let η := CondensedRing.upperStarCompUpperStarIsoOfComp Λ (inv f) f (IsIso.inv_hom_id f)
  let ε := CondensedRing.upperStarCompUpperStarIsoOfComp Λ f (inv f) (IsIso.hom_inv_id f)
  have hz : IsZero ((CondensedRing.upperStar Λ (inv f)).obj G) :=
    hF _ ((CondensedRing.upperStar Λ (inv f)).map i ≫ η.hom.app F) inferInstance
      (isPunctual_upperStar hΛ (inv f) hG)
  exact ((CondensedRing.upperStar Λ f).map_isZero hz).of_iso (ε.app G).symm

/-- **Frobenius pullback is perverse t-exact**: the derived pullback along an automorphism `f`
of `C` preserves the perverse heart. It commutes with the cohomology sheaves, and the pullback
of sheaves preserves constructibility, punctual sheaves and the absence of punctual subsheaves.
(blueprint: `lemma-perverse-weil-sheaves`) -/
theorem heart_mapDerivedCategory_upperStar {C : Scheme.{u}} [CompactSpace C]
    [QuasiSeparatedSpace C] (f : C ⟶ C) [IsIso f] {K : DerivedCategory (Modules Λ C)}
    (hK : heart Λ C K) :
    heart Λ C ((CondensedRing.upperStar Λ f).mapDerivedCategory.obj K) := by
  have := (constantModelConstructibleFiniteTor_wellDefined Λ C).1
  let eH (n : ℤ) := ((CondensedRing.upperStar Λ f).mapDerivedCategoryHomologyFunctorIso n).app K
  obtain ⟨⟨hb, hcK⟩, ⟨hu1, hu2⟩, ⟨hl1, hl2⟩⟩ := hK
  refine ⟨⟨(CondensedRing.upperStar Λ f).bounded_mapDerivedCategory_obj hb, fun n ↦ ?_⟩,
    ⟨fun a ha ↦ ?_, ?_⟩, ⟨fun a ha ↦ ?_, ?_⟩⟩
  · exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ C) (eH n)
      (hΛ f _ (hcK n)).1
  · exact ((CondensedRing.upperStar Λ f).map_isZero (hu1 a ha)).of_iso (eH a).symm
  · exact (isPunctual_upperStar hΛ f hu2).of_iso (eH 0)
  · exact ((CondensedRing.upperStar Λ f).map_isZero (hl1 a ha)).of_iso (eH a).symm
  · exact (hasNoPunctualSubsheaf_upperStar hΛ f hl2).of_iso (eH (0 - 1))

open CategoryTheory.Endofunctor in
/-- **The forgetful functor on perverse Weil sheaves**: for an automorphism `g` of `C`, the
functor forgetting the Weil structure, from perverse Weil sheaves to perverse sheaves on `C`,
creates finite limits and finite colimits. Hence it is exact and reflects exactness: kernels and
cokernels of perverse Weil sheaves are those of the underlying perverse sheaves, with the induced
Weil structures. The derived pullback along `g` restricts to an autoequivalence of the perverse
heart (`AlgebraicGeometry.ProEtale.CondensedCurvePerverse.heart_mapDerivedCategory_upperStar`),
whose algebras are the perverse Weil sheaves.
(blueprint: `lemma-perverse-weil-sheaves--2`) -/
theorem nonempty_createsFiniteLimits_forget {C : Scheme.{u}} [CompactSpace C]
    [QuasiSeparatedSpace C] (g : C ≅ C) :
    Nonempty (CreatesFiniteLimits (forget Λ g)) ∧
      Nonempty (CreatesFiniteColimits (forget Λ g)) := by
  let Φ := (CondensedRing.upperStar Λ g.hom).mapDerivedCategory
  have hΦ (K : DerivedCategory (Modules Λ C)) (hK : heart Λ C K) : heart Λ C (Φ.obj K) :=
    heart_mapDerivedCategory_upperStar hΛ g.hom hK
  have : (IsoAlgebra.restrict Φ (heart Λ C) hΦ).IsEquivalence := by
    refine { essSurj := ⟨fun L ↦ ⟨⟨(CondensedRing.upperStar Λ g.inv).mapDerivedCategory.obj L.obj,
      heart_mapDerivedCategory_upperStar hΛ g.inv L.property⟩, ⟨ObjectProperty.isoMk _ ?_⟩⟩⟩ }
    exact (Functor.mapDerivedCategoryCompIso _ _).app L.obj ≪≫
      (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarCompUpperStarIsoOfComp Λ g.hom
        g.inv g.hom_inv_id)).app L.obj ≪≫ (Functor.mapDerivedCategoryIdIso _).app L.obj
  exact IsoAlgebra.nonempty_createsFiniteLimits_forgetFullSubcategory Φ (heart Λ C) hΦ

end CondensedCurvePerverse

end AlgebraicGeometry.ProEtale
