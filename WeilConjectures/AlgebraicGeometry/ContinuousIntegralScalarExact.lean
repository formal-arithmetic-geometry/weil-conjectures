/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsSequentialColimit
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapMulLeft

/-! # Exactness of integral scalar localization

The private presheaf-level telescope (`localizationSequence`, `localizationCocone`, …) is still
used by the telescope files through `import all`; exactness itself is proved with the base
`Mod.smulSequence` API.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

private noncomputable abbrev coefficientPresheaf (R : Type) [TopologicalSpace R]
    [Ring R] [IsTopologicalRing R] : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1} :=
  Profinite.continuousMapRingPresheaf R ⋙ forget₂ RingCat Ab

private noncomputable abbrev integralPresheafMap :
    coefficientPresheaf.{u} (continuousIntegers ℓ E) ⟶ coefficientPresheaf E :=
  Functor.whiskerRight
    (Profinite.continuousMapRingPresheafMap (continuousIntegers ℓ E).subtype
      continuous_subtype_val) (forget₂ RingCat Ab)

private noncomputable def localizationLegHom (n : ℕ) :
    coefficientPresheaf.{u} (continuousIntegers ℓ E) ⟶ coefficientPresheaf E where
  app S := AddCommGrpCat.ofHom
    { toFun x := ULift.up
        (⟨fun s ↦ (x.down s : E) / (ℓ : E) ^ n,
          (continuous_subtype_val.comp x.down.continuous).div_const _⟩ : C(S.unop, E))
      map_zero' := by apply ULift.ext; ext; simp
      map_add' x y := by
        apply ULift.ext
        ext s
        change ((x.down s : E) + (y.down s : E)) / (ℓ : E) ^ n =
          (x.down s : E) / (ℓ : E) ^ n + (y.down s : E) / (ℓ : E) ^ n
        exact add_div _ _ _ }
  naturality _ _ _ := rfl

private noncomputable def localizationLeg (n : ℕ) :
    Mod.regular (coefficientPresheaf.{u} (continuousIntegers ℓ E)) ⟶
      (Mod.comap (integralPresheafMap ℓ E)).obj (Mod.regular (coefficientPresheaf E)) :=
  Mod.homMk (localizationLegHom ℓ E n) (by
    ext S : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro a b
    apply ULift.ext
    ext x
    change ((a.down x : E) * (b.down x : E)) / (ℓ : E) ^ n =
      (a.down x : E) * ((b.down x : E) / (ℓ : E) ^ n)
    exact mul_div_assoc _ _ _)

private noncomputable abbrev localizationSequence :
    ℕ ⥤ Mod (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1})
      (coefficientPresheaf (continuousIntegers ℓ E)) :=
  Functor.ofSequence (fun _ ↦ ℓ • 𝟙 (Mod.regular
    (coefficientPresheaf (continuousIntegers ℓ E))))

private lemma ell_ne_zero : (ℓ : E) ≠ 0 := by
  have h : (ℓ : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  simpa only [map_natCast, map_zero] using (algebraMap ℚ_[ℓ] E).injective.ne h

private noncomputable def localizationCocone : Cocone (localizationSequence.{u} ℓ E) where
  pt := (Mod.comap (integralPresheafMap ℓ E)).obj (Mod.regular (coefficientPresheaf E))
  «ι» := NatTrans.ofSequence (localizationLeg ℓ E) (by
    intro n
    simp only [localizationSequence, Functor.ofSequence_map_homOfLE_succ,
      Functor.const_obj_map]
    apply Mod.hom_ext
    ext S x
    apply ULift.ext
    ext s
    change (continuousIntegers ℓ E).subtype (ℓ • x.down s) / (ℓ : E) ^ (n + 1) =
      (x.down s : E) / (ℓ : E) ^ n
    rw [map_nsmul, nsmul_eq_mul, pow_succ]
    field_simp [ell_ne_zero ℓ E]
    rfl)

private noncomputable def localizationCoconeIsColimit :
    IsColimit (localizationCocone.{u} ℓ E) := by
  let := Functor.functorCategoryMonoidalClosed Profinite.{u}ᵒᵖ Ab.{u + 1}
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget Ab.{u + 1})
  have : ReflectsColimitsOfShape ℕ (forget Ab.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  have : ReflectsColimitsOfShape ℕ
      (Mod.forget (D := Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1})
        (coefficientPresheaf (continuousIntegers ℓ E))) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (Mod.forget (D := Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1})
    (coefficientPresheaf (continuousIntegers ℓ E)))
  refine evaluationJointlyReflectsColimits _ fun S ↦
    isColimitOfReflects (forget Ab.{u + 1}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    let φ := (continuousIntegers ℓ E).subtype.compLeftContinuous S.unop continuous_subtype_val
    let := φ.toAlgebra
    have hloc := continuousIntegralFunctions_isLocalization ℓ E S.unop
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj
      (ContinuousMap.const S.unop (ℓ : continuousIntegers ℓ E)) x.down
    refine ⟨n, ULift.up a, ?_⟩
    apply ULift.ext
    ext s
    change x.down s = (a s : E) / (ℓ : E) ^ n
    have ha' := congrArg (fun f : C(S.unop, E) ↦ f s) ha
    change x.down s * (ℓ : E) ^ n = (a s : E) at ha'
    exact (eq_div_iff (pow_ne_zero n (ell_ne_zero ℓ E))).2 ha'
  · intro n x y h
    have hxy : x = y := by
      apply ULift.ext
      apply ContinuousMap.ext
      intro s
      apply Subtype.ext
      have h' := congrArg (fun f : ULift.{u + 1} C(S.unop, E) ↦ f.down s) h
      change (x.down s : E) / (ℓ : E) ^ n = (y.down s : E) / (ℓ : E) ^ n at h'
      exact (div_left_inj' (pow_ne_zero n (ell_ne_zero ℓ E))).mp h'
    subst y
    exact ⟨n, 𝟙 n, rfl⟩

private noncomputable def mappedRegularIso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) [L.LaxMonoidal] (R : C) [MonObj R] :
    (L.mapMod R).obj (Mod.regular R) ≅ Mod.regular (L.obj R) :=
  Mod.isoMk (Iso.refl _) (by simp [Mod.act])

private noncomputable def restrictedRegularIso
    {C : Type*} [Category C] [MonoidalCategory C]
    {A B B' : C} [MonObj A] [MonObj B] [MonObj B']
    (φ : A ⟶ B) (φ' : A ⟶ B') [IsMonHom φ] [IsMonHom φ']
    (e : B ≅ B') [IsMonHom e.hom] (w : φ ≫ e.hom = φ') :
    (Mod.comap φ).obj (Mod.regular B) ≅ (Mod.comap φ').obj (Mod.regular B') :=
  Mod.isoMk e (by
    change (φ ▷ B ≫ μ[B]) ≫ e.hom = A ◁ e.hom ≫ φ' ▷ B' ≫ μ[B']
    rw [Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def, Category.assoc,
      ← comp_whiskerRight_assoc, w, whisker_exchange_assoc])

private noncomputable def pointCoefficientIso (R : Type) [TopologicalSpace R]
    [Ring R] [IsTopologicalRing R] :
    (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (coefficientPresheaf R) ≅ Profinite.continuousMapRingObj R :=
  Sheaf.sheafifyRingPresheafIso (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheaf R)

private noncomputable abbrev schemeCoefficientFunctor (X : Scheme.{u}) :=
  presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙ upperStarFromPoint X

private noncomputable def schemeCoefficientIso (X : Scheme.{u})
    (R : Type) [TopologicalSpace R] [Ring R] [IsTopologicalRing R] :
    (schemeCoefficientFunctor X).obj (coefficientPresheaf R) ≅
      condensedRingObj (Profinite.continuousMapRingObj R) X :=
  (upperStarFromPoint X).mapIso (pointCoefficientIso R)

private theorem schemeCoefficientIso_naturality (X : Scheme.{u}) :
    (schemeCoefficientFunctor X).map (integralPresheafMap ℓ E) ≫
        (schemeCoefficientIso X E).hom =
      (schemeCoefficientIso X (continuousIntegers ℓ E)).hom ≫
        coefficientMap (integralScalarMap ℓ E) X := by
  change (upperStarFromPoint X).map
      ((presheafToSheaf _ Ab).map (integralPresheafMap ℓ E)) ≫
        (upperStarFromPoint X).map (pointCoefficientIso E).hom =
    (upperStarFromPoint X).map (pointCoefficientIso (continuousIntegers ℓ E)).hom ≫
      (upperStarFromPoint X).map (integralScalarMap ℓ E)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [integralScalarMap, Sheaf.sheafCompose_map_eq]
  simp only [pointCoefficientIso, Iso.hom_inv_id_assoc]
  rfl

/-- The map `c_k = ℓ⁻ᵏ φ : 𝒪̲_E ⟶ E̲`, where `φ` is the inclusion `integralScalarMap`.
Source: Bhatt--Scholze, Lemma 6.8.2
(auxiliary; not a blueprint node). -/
noncomputable def integralScalarMapInvPow (k : ℕ) :
    integralCoeff.{u} ℓ E ⟶ Profinite.continuousMapRingObj E :=
  integralScalarMap ℓ E ≫ Profinite.continuousMapRingObjMulLeft E ((ℓ : E)⁻¹ ^ k)

lemma integralScalarMapInvPow_zero :
    integralScalarMapInvPow.{u} ℓ E 0 = integralScalarMap ℓ E := by
  rw [integralScalarMapInvPow, pow_zero, Profinite.continuousMapRingObjMulLeft_one,
    Category.comp_id]

lemma nsmul_integralScalarMapInvPow_succ (k : ℕ) :
    ℓ • integralScalarMapInvPow.{u} ℓ E (k + 1) = integralScalarMapInvPow ℓ E k := by
  rw [integralScalarMapInvPow, integralScalarMapInvPow, ← Preadditive.comp_nsmul,
    Profinite.nsmul_continuousMapRingObjMulLeft, pow_succ', ← _root_.mul_assoc,
    mul_inv_cancel₀ (ell_ne_zero ℓ E), _root_.one_mul]

/-- **`E̲ = colim(𝒪̲_E --ℓ--> 𝒪̲_E --ℓ--> ⋯)`** for the closed unit ball `𝒪_E` of a normed
extension `E` of `ℚ_ℓ`: the maps `ℓ⁻ᵏ φ` exhibit `E̲` as the sequential colimit of the
multiplications by `ℓ` on `𝒪̲_E`. This is base
`Profinite.isColimitPadicIntegersRingObjSmulSequenceCocone` for a general normed `E`. Sectionwise,
every continuous map from a profinite set to `E` has a common denominator `ℓⁿ`
(`continuousIntegralFunctions_isLocalization`), and the maps `ℓ⁻ᵏ φ` are injective.
Source: Bhatt--Scholze, Lemma 6.8.2
(auxiliary; not a blueprint node). -/
noncomputable def isColimitIntegralCoeffSmulSequenceCocone :
    IsColimit (Mod.smulSequenceCocone ℓ (integralScalarMapInvPow.{u} ℓ E)
      (nsmul_integralScalarMapInvPow_succ ℓ E)) := by
  have hℓ := ell_ne_zero ℓ E
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget Ab.{u + 1})
  have : ReflectsColimitsOfShape ℕ (forget Ab.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (sheafToPresheaf _ _) ?_
  refine evaluationJointlyReflectsColimits _ fun S ↦
    isColimitOfReflects (forget Ab.{u + 1}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    obtain ⟨x⟩ := x
    let φ := (continuousIntegers ℓ E).subtype.compLeftContinuous S.unop continuous_subtype_val
    let := φ.toAlgebra
    have hloc := continuousIntegralFunctions_isLocalization ℓ E S.unop
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj
      (ContinuousMap.const S.unop (ℓ : continuousIntegers ℓ E)) x
    refine ⟨n, ULift.up a, ULift.ext _ _ (ContinuousMap.ext fun s ↦ ?_)⟩
    have ha' := congrArg (fun f : C(S.unop, E) ↦ f s) ha
    change x s * (ℓ : E) ^ n = (a s : E) at ha'
    have key : (ℓ : E)⁻¹ ^ n * (a s : E) = x s := by
      rw [← ha', inv_pow, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero n hℓ), mul_comm]
    first
      | exact key
      | exact key.symm
  · intro k x y h
    refine ⟨k, 𝟙 k, ?_⟩
    rw [CategoryTheory.Functor.map_id]
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    have hk : (ℓ : E)⁻¹ ^ k ≠ 0 := pow_ne_zero _ (inv_ne_zero hℓ)
    have h' (s : S.unop) :
        (ℓ : E)⁻¹ ^ k * (x s : E) = (ℓ : E)⁻¹ ^ k * (y s : E) :=
      congrArg (fun z : ULift.{u + 1} C(S.unop, E) ↦ z.down s) h
    obtain rfl : x = y := ContinuousMap.ext fun s ↦ Subtype.ext (mul_left_cancel₀ hk (h' s))
    rfl

/-- Integral-to-E scalar extension is exact. `E_X = p_X^* E̲` is the sequential colimit of the
multiplications by `ℓ` on `𝒪_{E,X} = p_X^* 𝒪̲_E` (`isColimitIntegralCoeffSmulSequenceCocone`,
preserved by the additive left adjoint `p_X^*`), so base
`Mod.preservesFiniteLimits_extendScalars_of_isColimit` applies. This is the proof of base
`preservesFiniteLimits_extendScalars_padicIntegersToPadicSubfield` for a general normed `E`.
Source: Bhatt--Scholze, Lemma 6.8.2
(auxiliary; not a blueprint node). -/
@[instance] theorem integralScalarExtension_exact (X : Scheme.{u}) :
    PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)) := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  have := Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)
  have := AB5OfSize_of_univLE.{0, 0} (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  exact Mod.preservesFiniteLimits_extendScalars_of_isColimit _
    (Mod.isColimitSmulSequenceCoconeMap (upperStarFromPoint X) _
      (isColimitIntegralCoeffSmulSequenceCocone ℓ E))
    (by rw [integralScalarMapInvPow_zero])

end AlgebraicGeometry.ProEtale.CondensedRing
