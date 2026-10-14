module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionChartSectionModules
import Mathlib.AlgebraicGeometry.Morphisms.Flat

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- Affine chart tensor comparison via a bijective structural-linear map.
Source: Stacks Project, Tags 01JO, 0BLH and 05EL.
(blueprint: new-sbc-punctured-completion-chart-tensor-sections-aux)

This is the affine fibre-product calculation transported through the overlap
isomorphism.  The bijectivity assertion is the underlying construction; the
public theorem upgrades this map to a linear equivalence.
-/
theorem exists_chart_tensor_sections_bijective
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens} {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} [IsAffine E] {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (f : A)
    (hf : PrimeSpectrum.basicOpen f ≤ U)
    (hV : IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen f)) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let W := s ⁻¹ᵁ PrimeSpectrum.basicOpen (φ f)
    letI : Module C Γ(E, W) := Module.compHom _
      ((ΓSpecIso (.of C)).inv ≫ s.appTop ≫
        E.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
    let N := ModuleCat.of C Γ(E, W)
    ∃ e : FormalGlueing.extend φ
      (FormalGlueing.piece f (chartSectionModule (q ≫ U.ι) f)) →ₗ[C] N,
      Function.Bijective e := by
  classical
  dsimp
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let φ := algebraMap A C
  let V := (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen f
  let W := s ⁻¹ᵁ PrimeSpectrum.basicOpen (φ f)
  let O := pullback q (completionSpecMap A ∣_ U)
  let p : O ⟶ Y := pullback.fst q (completionSpecMap A ∣_ U)
  let hC := pullback.snd q (completionSpecMap A ∣_ U) ≫
    (completionSpecMap A ⁻¹ᵁ U).ι
  let aY := ((ΓSpecIso (.of A)).inv ≫ (q ≫ U.ι).appTop ≫
    Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom
  let aO := ((ΓSpecIso (.of C)).inv ≫ hC.appTop ≫
    O.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V ≤ ⊤)).op).hom
  let aE := ((ΓSpecIso (.of C)).inv ≫ s.appTop ≫
    E.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
  let : Algebra A C := φ.toAlgebra
  let : Algebra A Γ(Y, V) := aY.toAlgebra
  let : Module C Γ(E, W) := Module.compHom _ aE
  have H : IsPullback p hC (q ≫ U.ι) (completionSpecMap A) :=
    (IsPullback.of_hasPullback q (completionSpecMap A ∣_ U)).paste_vert
      (isPullback_morphismRestrict (completionSpecMap A) U)
  have hUST : (⊤ : (Spec (.of C)).Opens) ≤ completionSpecMap A ⁻¹ᵁ ⊤ := by simp
  have hUSX : V ≤ (q ≫ U.ι) ⁻¹ᵁ ⊤ := by simp
  have hUY : p ⁻¹ᵁ V = p ⁻¹ᵁ V ⊓ hC ⁻¹ᵁ ⊤ := by simp
  let := isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY
    (isAffineOpen_top _) (isAffineOpen_top _) hV
  have Hs := (isIso_pushoutSection_iff H hUST hUSX hUY).mp inferInstance
  have Hs' : IsPushout (CommRingCat.ofHom aY)
      (CommRingCat.ofHom φ) (p.app V) (CommRingCat.ofHom aO) := by
    refine Hs.of_iso (ΓSpecIso (.of A)) (Iso.refl _) (ΓSpecIso (.of C))
      (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [Scheme.Hom.appLE, aY]
    · simp [Scheme.Hom.appLE, completionSpecMap, φ, C]
    · simp [Scheme.Hom.appLE]
    · simp [Scheme.Hom.appLE, aO]
  let Q := ((CommRingCat.isPushout_tensorProduct A C Γ(Y, V)).isoIsPushout
    (.of C) Γ(Y, V) Hs'.flip).commRingCatIsoToRingEquiv
  have hQ (c : C) : Q (TensorProduct.tmul A c (1 : Γ(Y, V))) = aO c := by
    exact congr($( (CommRingCat.isPushout_tensorProduct A C Γ(Y, V)).inl_isoIsPushout_hom
      (.of C) Γ(Y, V) Hs'.flip ) c)
  have ht : D.toCompleted ≫ s = hC := by
    change (D.overlapIso.hom ≫ (s ⁻¹ᵁ (completionSpecMap A ⁻¹ᵁ U)).ι) ≫ s = _
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, D.over]
  let : IsOpenImmersion D.toCompleted := by unfold toCompleted; infer_instance
  have hW : W ≤ D.toCompleted.opensRange := by
    change W ≤ (D.overlapIso.hom ≫ (s ⁻¹ᵁ (completionSpecMap A ⁻¹ᵁ U)).ι).opensRange
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
    apply s.preimage_mono
    change completionSpecMap A ⁻¹ᵁ PrimeSpectrum.basicOpen f ≤ _
    exact (completionSpecMap A).preimage_mono hf
  have he : p ⁻¹ᵁ V = D.toCompleted ⁻¹ᵁ W := by
    change (p ≫ q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen f =
      (D.toCompleted ≫ s ≫ completionSpecMap A) ⁻¹ᵁ PrimeSpectrum.basicOpen f
    rw [← D.overlap_base]
  let F : Γ(E, W) ⟶ Γ(O, p ⁻¹ᵁ V) := D.toCompleted.app W ≫
    O.presheaf.map (eqToHom he).op
  let := D.toCompleted.isIso_app W hW
  let R := Q.trans (asIso F).commRingCatIsoToRingEquiv.symm
  have hF (c : C) : F (aE c) = aO c := by
    have hh : CommRingCat.ofHom aE ≫ F = CommRingCat.ofHom aO := by
      dsimp only [aE, aO, F, CommRingCat.ofHom_hom]
      simp only [Category.assoc]
      rw [D.toCompleted.naturality_assoc]
      simp only [← Category.assoc, ← Scheme.Hom.comp_appTop, ht]
      dsimp only [O]
      simp only [Category.assoc, ← Functor.map_comp]
      rfl
    exact congr($(hh) c)
  have hR (c : C) : R (TensorProduct.tmul A c (1 : Γ(Y, V))) = aE c := by
    apply (asIso F).commRingCatIsoToRingEquiv.injective
    simp only [R, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
    change Q (TensorProduct.tmul A c (1 : Γ(Y, V))) = F (aE c)
    rw [hQ, hF]
  let B : FormalGlueing.piece f (chartSectionModule (q ≫ U.ι) f) ≃ₗ[A] Γ(Y, V) :=
    { __ := AddEquiv.refl _
      map_smul' := chartSectionModule_smul (q ≫ U.ι) f }
  let T := B.baseChange A C _ _
  let L : TensorProduct A C Γ(Y, V) ≃ₗ[C] Γ(E, W) :=
    { __ := R.toAddEquiv
      map_smul' := by
        intro c x
        change R (c • x) = aE c * R x
        rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, map_mul, hR]
        rfl }
  exact ⟨L.toLinearMap.comp T.toLinearMap, L.bijective.comp T.bijective⟩

end AlgebraicGeometry.Scheme.CompletionGluingData
