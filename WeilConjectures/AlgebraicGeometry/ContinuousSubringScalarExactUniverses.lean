/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.Normed.Algebra.Basic
public import WeilConjectures.Topology.ContinuousMapCondensedRingMap
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.ConstructibleSheaf.FreeLifting

/-! # Exactness of integral scalar localization -/

@[expose] public section

universe u
set_option autoImplicit false
attribute [local instance] Profinite.continuousMapRingObjOfUniverseMonObj
attribute [local instance] Profinite.isCommMonObj_continuousMapRingObjOfUniverse
attribute [local instance] Profinite.isMonHom_continuousMapRingObjMapOfUniverse

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  (A : Subring E) (hA : ∀ x : E, x ∈ A ↔ ‖x‖ ≤ 1)

private noncomputable abbrev coefficientPresheaf (R : Type u) [TopologicalSpace R]
    [Ring R] [IsTopologicalRing R] : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1} :=
  Profinite.continuousMapRingPresheafOfUniverse.{u, u} R ⋙ forget₂ RingCat Ab

private noncomputable abbrev integralPresheafMap :
    coefficientPresheaf.{u} (A) ⟶ coefficientPresheaf E :=
  Functor.whiskerRight
    (Profinite.continuousMapRingPresheafMapOfUniverse (A).subtype
      continuous_subtype_val) (forget₂ RingCat Ab)

private noncomputable def localizationLegHom (n : ℕ) :
    coefficientPresheaf.{u} (A) ⟶ coefficientPresheaf E where
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
    Mod.regular (coefficientPresheaf.{u} (A)) ⟶
      (Mod.comap (integralPresheafMap E A)).obj (Mod.regular (coefficientPresheaf E)) :=
  Mod.homMk (localizationLegHom ℓ E A n) (by
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
      (coefficientPresheaf (A)) :=
  Functor.ofSequence (fun _ ↦ ℓ • 𝟙 (Mod.regular
    (coefficientPresheaf (A))))

private lemma ell_ne_zero : (ℓ : E) ≠ 0 := by
  have h : (ℓ : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  simpa only [map_natCast, map_zero] using (algebraMap ℚ_[ℓ] E).injective.ne h

private noncomputable def localizationCocone : Cocone (localizationSequence.{u} ℓ E A) where
  pt := (Mod.comap (integralPresheafMap E A)).obj (Mod.regular (coefficientPresheaf E))
  «ι» := NatTrans.ofSequence (localizationLeg ℓ E A) (by
    intro n
    simp only [localizationSequence, Functor.ofSequence_map_homOfLE_succ,
      Functor.const_obj_map]
    apply Mod.hom_ext
    ext S x
    apply ULift.ext
    ext s
    change (A).subtype (ℓ • x.down s) / (ℓ : E) ^ (n + 1) =
      (x.down s : E) / (ℓ : E) ^ n
    rw [map_nsmul, nsmul_eq_mul, pow_succ]
    field_simp [ell_ne_zero ℓ E]
    rfl)

private theorem compactFunctionsLocalization
    (hA : ∀ x : E, x ∈ A ↔ ‖x‖ ≤ 1)
    (S : Type u) [TopologicalSpace S] [CompactSpace S] :
    letI := ((A).subtype.compLeftContinuous S
      continuous_subtype_val).toAlgebra
    IsLocalization.Away (ContinuousMap.const S (ℓ : A)) C(S, E) := by
  let φ := (A).subtype.compLeftContinuous S continuous_subtype_val
  let := φ.toAlgebra
  change IsLocalization.Away (ContinuousMap.const S (ℓ : A)) C(S, E)
  have hp : (ℓ : E) ≠ 0 := by
    have h : (ℓ : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    simpa only [map_natCast, map_zero] using (algebraMap ℚ_[ℓ] E).injective.ne h
  have hnorm : ‖(ℓ : E)‖ < 1 := by
    have h : ‖(ℓ : E)‖ = ‖(ℓ : ℚ_[ℓ])‖ := by
      simpa only [map_natCast] using (norm_algebraMap' E (ℓ : ℚ_[ℓ]))
    rw [h]
    exact Padic.norm_p_lt_one
  apply IsLocalization.Away.mk
  · exact (isUnit_iff_ne_zero.mpr hp).map (ContinuousMap.C : E →+* C(S, E))
  · intro f
    have hb : 0 < ‖f‖ + 1 := by positivity
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hb) hnorm
    have hmem (x : S) : f x * (ℓ : E) ^ n ∈ A := by
      apply (hA _).mpr
      rw [norm_mul, norm_pow]
      calc
        ‖f x‖ * ‖(ℓ : E)‖ ^ n ≤ (‖f‖ + 1) * ‖(ℓ : E)‖ ^ n :=
          mul_le_mul_of_nonneg_right (f.norm_coe_le_norm x |>.trans (by linarith))
            (by positivity)
        _ ≤ (‖f‖ + 1) * (‖f‖ + 1)⁻¹ := (mul_lt_mul_of_pos_left hn hb).le
        _ = 1 := mul_inv_cancel₀ hb.ne'
    let a : C(S, A) :=
      ⟨fun x ↦ ⟨f x * (ℓ : E) ^ n, hmem x⟩,
        (f.continuous.mul continuous_const).subtype_mk _⟩
    exact ⟨n, a, rfl⟩
  · intro a b hab
    have h : a = b := by
      ext x
      exact congrArg (fun f : C(S, E) ↦ f x) hab
    subst b
    exact ⟨0, rfl⟩


private noncomputable def localizationCoconeIsColimit :
    IsColimit (localizationCocone.{u} ℓ E A) := by
  let := Functor.functorCategoryMonoidalClosed Profinite.{u}ᵒᵖ Ab.{u + 1}
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget Ab.{u + 1})
  have : ReflectsColimitsOfShape ℕ (forget Ab.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  have : ReflectsColimitsOfShape ℕ
      (Mod.forget (D := Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1})
        (coefficientPresheaf (A))) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (Mod.forget (D := Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1})
    (coefficientPresheaf (A)))
  refine evaluationJointlyReflectsColimits _ fun S ↦
    isColimitOfReflects (forget Ab.{u + 1}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    let φ := (A).subtype.compLeftContinuous S.unop continuous_subtype_val
    let := φ.toAlgebra
    have hloc := compactFunctionsLocalization ℓ E A hA S.unop
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj
      (ContinuousMap.const S.unop (ℓ : A)) x.down
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

@[irreducible] private noncomputable def pointCoefficientIso (R : Type u) [TopologicalSpace R]
    [Ring R] [IsTopologicalRing R] :
    (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (coefficientPresheaf R) ≅ Profinite.continuousMapRingObjOfUniverse.{u, u} R :=
  Sheaf.sheafifyRingPresheafIso (coherentTopology Profinite.{u})
    (Profinite.continuousMapRingSheafOfUniverse.{u, u} R)

private instance pointCoefficientIso_isMonHom (R : Type u) [TopologicalSpace R]
    [Ring R] [IsTopologicalRing R] : IsMonHom (pointCoefficientIso R).hom := by
  unfold pointCoefficientIso
  infer_instance

private noncomputable abbrev schemeCoefficientFunctor (X : Scheme.{u}) :=
  presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙ upperStarFromPoint X

private noncomputable def schemeCoefficientIso (X : Scheme.{u})
    (R : Type u) [TopologicalSpace R] [Ring R] [IsTopologicalRing R] :
    (schemeCoefficientFunctor X).obj (coefficientPresheaf R) ≅
      condensedRingObj (Profinite.continuousCoefficientRingObj R) X :=
  (upperStarFromPoint X).mapIso (pointCoefficientIso R)

private theorem schemeCoefficientIso_naturality (X : Scheme.{u}) :
    (schemeCoefficientFunctor X).map (integralPresheafMap E A) ≫
        (schemeCoefficientIso X E).hom =
      (schemeCoefficientIso X (A)).hom ≫
        coefficientMap
          (Profinite.continuousMapRingObjMapOfUniverse.{u, u} A.subtype
            continuous_subtype_val) X := by
  change (upperStarFromPoint X).map
      ((presheafToSheaf _ Ab).map (integralPresheafMap E A)) ≫
        (upperStarFromPoint X).map (pointCoefficientIso E).hom =
    (upperStarFromPoint X).map (pointCoefficientIso (A)).hom ≫
      (upperStarFromPoint X).map
        (Profinite.continuousMapRingObjMapOfUniverse.{u, u} A.subtype continuous_subtype_val)
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [Profinite.continuousMapRingObjMapOfUniverse, Sheaf.sheafCompose_map_eq]
  simp only [pointCoefficientIso, Iso.hom_inv_id_assoc]
  rfl

set_option maxHeartbeats 800000 in
-- The filtered-colimit proof compares several induced module functors and their instances.
/-- Integral-to-E scalar extension is exact: its restricted regular coefficient module is
an ℕ-filtered colimit of regular integral modules, with transition multiplication by ℓ.
Source: Bhatt--Scholze, Lemma 6.8.2; the compact-test coefficient localization theorem.
(blueprint: lem-weil-pbc-continuous-subring-scalar-exact-universes).

Proof. On a compact profinite test S, the nth map sends a to a/ℓⁿ. Every continuous
E-valued function has one common denominator by compactness, and the inclusion of the
integral coefficient ring is injective. These maps therefore form a colimit cocone.
Exact monoidal sheafification and inverse image from the point preserve this cocone
and identify each stage with the regular integral module on X. Filtered colimits of
flat objects are flat. Tensoring with this restricted regular module is thus exact;
the faithful exact forgetful functor identifies it with scalar extension. -/
theorem continuousSubringScalarExtension_exact (ℓ : ℕ) [Fact ℓ.Prime]
    [NormedAlgebra ℚ_[ℓ] E] (hA : ∀ x : E, x ∈ A ↔ ‖x‖ ≤ 1)
    (X : Scheme.{u}) :
    PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap
        (Profinite.continuousMapRingObjMapOfUniverse.{u, u} A.subtype
          continuous_subtype_val) X)) := by
  let := Functor.functorCategoryMonoidalClosed Profinite.{u}ᵒᵖ Ab.{u + 1}
  have : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  let L := schemeCoefficientFunctor X
  let R := coefficientPresheaf.{u} (A)
  let S := coefficientPresheaf.{u} E
  let R₀ := condensedRingObj (Profinite.continuousCoefficientRingObj A) X
  let B := condensedRingObj (Profinite.continuousCoefficientRingObj E) X
  let a := schemeCoefficientIso X (A)
  let b := schemeCoefficientIso X E
  let φ := integralPresheafMap.{u} E A
  let ψ := coefficientMap
    (Profinite.continuousMapRingObjMapOfUniverse.{u, u} A.subtype continuous_subtype_val) X
  have : IsMonHom (Profinite.continuousMapRingObjMapOfUniverse.{u, u} A.subtype
      continuous_subtype_val) :=
    Profinite.isMonHom_continuousMapRingObjMapOfUniverse.{u, u} A.subtype continuous_subtype_val
  have : IsMonHom a.hom := by
    change @IsMonHom _ _ _ _ _ (L.monObjObj R) _ a.hom
    rw [Functor.monObjObj_comp]
    exact Functor.map.instIsMonHom (F := upperStarFromPoint X) _ _
      (pointCoefficientIso (A)).hom
  have : IsMonHom a.inv := by infer_instance
  have : IsMonHom b.hom := by
    change @IsMonHom _ _ _ _ _ (L.monObjObj S) _ b.hom
    rw [Functor.monObjObj_comp]
    exact Functor.map.instIsMonHom (F := upperStarFromPoint X) _ _
      (pointCoefficientIso E).hom
  let F := L.mapMod R ⋙ Mod.comap a.inv
  have : L.Additive := by
    exact rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [rightExactFunctor_iff]
      infer_instance)
  have : (L.mapMod R).Additive := ⟨fun {M N f g} ↦
    Mod.hom_ext _ _ (L.map_add (f := f.hom) (g := g.hom))⟩
  have : PreservesColimitsOfShape ℕ (L.mapMod R) := by
    have : PreservesColimitsOfShape ℕ
        (L.mapMod R ⋙ Mod.forget (L.obj R)) :=
      inferInstanceAs (PreservesColimitsOfShape ℕ (Mod.forget R ⋙ L))
    exact preservesColimitsOfShape_of_reflects_of_preserves _ (Mod.forget (L.obj R))
  have er : F.obj (Mod.regular R) ≅ Mod.regular R₀ :=
    (Mod.comap a.inv).mapIso (mappedRegularIso L R) ≪≫
      restrictedRegularIso a.inv (𝟙 R₀) a (by exact a.inv_hom_id) ≪≫ (Mod.comapId R₀).app _
  have es : F.obj ((Mod.comap φ).obj (Mod.regular S)) ≅
      (Mod.comap ψ).obj (Mod.regular B) :=
    (Mod.comap a.inv).mapIso
      ((L.mapModComapIso φ).app (Mod.regular S) ≪≫
        (Mod.comap (L.map φ)).mapIso (mappedRegularIso L S)) ≪≫
      (Mod.comapComp a.inv (L.map φ)).symm.app (Mod.regular (L.obj S)) ≪≫
      restrictedRegularIso (a.inv ≫ L.map φ) ψ b (by
        rw [Category.assoc, schemeCoefficientIso_naturality E A X, Iso.inv_hom_id_assoc])
  have hc := isColimitOfPreserves F (localizationCoconeIsColimit.{u} ℓ E A hA)
  let D := localizationSequence.{u} ℓ E A ⋙ F
  have hD (n : ℕ) : ObjectProperty.flat (D.obj n) :=
    ObjectProperty.prop_of_iso _ er.symm (ObjectProperty.flat_of_tensorIso
      (λ_ (Mod.regular R₀)))
  have : AB5OfSize.{0, 0} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R₀) :=
    AB5OfSize_of_univLE.{0, 0, u + 1, u + 1} _
  have hflat : ObjectProperty.flat ((Mod.comap ψ).obj (Mod.regular B)) :=
    ObjectProperty.prop_of_iso _
      (colimit.isoColimitCocone ⟨F.mapCocone (localizationCocone ℓ E A), hc⟩ ≪≫ es)
      (ObjectProperty.flat_colimit D hD)
  have : PreservesFiniteLimits (tensorLeft ((Mod.comap ψ).obj (Mod.regular B))) :=
    hflat.1.1
  have : PreservesFiniteLimits (Mod.forget
      (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R₀) := by infer_instance
  have ht : PreservesFiniteLimits
      (tensorLeft ((Mod.comap ψ).obj (Mod.regular B)) ⋙ Mod.forget R₀) := by
    infer_instance
  have : PreservesFiniteLimits (Mod.extendScalars ψ ⋙ Mod.forget B) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _
      (Mod.extendForgetTensorIso ψ).symm ht
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Mod.forget B)

end AlgebraicGeometry.ProEtale.CondensedRing
