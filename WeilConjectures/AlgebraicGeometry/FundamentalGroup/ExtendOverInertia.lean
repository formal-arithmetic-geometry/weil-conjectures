/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DecompositionGroup
public import WeilConjectures.Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Covers on which inertia acts trivially extend over the point

Let `j : U ⟶ C` be an open immersion into an integral scheme, `z` a closed point of `C` outside
`U`, and `W` an affine open neighbourhood of `z` with `W ∩ U = D(π)` for some `π ∈ Γ(C, W)`. A
finite étale `U`-scheme `Z` on whose generic geometric fibre the inertia group at `z` acts
trivially extends to a finite étale scheme over `U ∪ W`
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_pullback_iso_of_forall_inertia`): the
normalization `N` of `C` in `Z` restricts to `Z` over `U`, and over `W` it is the spectrum of the
integral closure of `Γ(C, W)` in `Γ(Z, f⁻¹ W)`, which is finite étale by
`Ideal.etale_integralClosure_of_forall_inertia`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X U C : Scheme.{u}} (g : X ⟶ U) (j : U ⟶ C) [IsOpenImmersion j] [IsIntegralHom g]
  [QuasiCompact (g ≫ j)] [QuasiSeparated (g ≫ j)]

instance : IsIntegralHom (pullback.snd (g ≫ j) j) := by
  have h : pullback.snd (g ≫ j) j = pullback.fst (g ≫ j) j ≫ g := by
    rw [← cancel_mono j, Category.assoc, ← pullback.condition]
  rw [h]
  infer_instance

/-- The normalization of `C` in an integral `U`-scheme `X`, restricted to the open `U`, is `X`. -/
noncomputable def pullbackFromNormalizationIso : pullback (g ≫ j).fromNormalization j ≅ X :=
  (asIso ((g ≫ j).normalizationPullback j)).symm ≪≫
    (asIso (pullback.snd (g ≫ j) j).toNormalization).symm ≪≫ asIso (pullback.fst (g ≫ j) j)

@[reassoc (attr := simp)]
lemma pullbackFromNormalizationIso_hom_comp :
    (pullbackFromNormalizationIso g j).hom ≫ g = pullback.snd _ _ := by
  have h : pullback.fst (g ≫ j) j ≫ g = pullback.snd (g ≫ j) j := by
    rw [← cancel_mono j, Category.assoc, pullback.condition]
  simp only [pullbackFromNormalizationIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, asIso_inv, h, IsIso.inv_comp_eq]
  rw [normalizationPullback_snd, toNormalization_fromNormalization]

end Scheme.Hom

/-- A ring-hom property of `f ∣_ U`, for `U` affine with affine preimage, is that of `f.app U`. -/
lemma morphismRestrict_appTop_iff {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hQ : RingHom.RespectsIso Q) {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    Q (f ∣_ U).appTop.hom ↔ Q (f.app U).hom := by
  rw [morphismRestrict_appTop]
  refine (hQ.cancel_right_isIso (f.app (U.ι ''ᵁ ⊤)) _).trans ?_
  have h : U.ι ''ᵁ ⊤ = U := Scheme.Opens.ι_image_top U
  have : ∀ V : Y.Opens, V = U → (Q (f.app V).hom ↔ Q (f.app U).hom) := by
    rintro V rfl
    rfl
  exact this _ h

/-- A point `Spec Ω ⟶ X` landing in an affine open `V` comes from a ring map `Γ(X, V) ⟶ Ω`. -/
lemma IsAffineOpen.exists_specMap_comp_fromSpec {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) {Ω : Type u} [CommRing Ω] (t : Spec (.of Ω) ⟶ X)
    (ht : Set.range t.base ⊆ V) :
    ∃ ψ : Γ(X, V) ⟶ CommRingCat.of Ω, Spec.map ψ ≫ hV.fromSpec = t := by
  let t' := IsOpenImmersion.lift V.ι t (by rwa [Scheme.Opens.range_ι])
  refine ⟨Spec.preimage (t' ≫ hV.isoSpec.hom), ?_⟩
  rw [Spec.map_preimage, ← hV.isoSpec_inv_ι, Category.assoc, hV.isoSpec.hom_inv_id_assoc]
  exact IsOpenImmersion.lift_fac _ _ _

/-- The generic point of an integral scheme factors through every nonempty affine open. -/
lemma IsAffineOpen.fromSpecFunctionField_eq {X : Scheme.{u}} [IsIntegral X] {W : X.Opens}
    (hW : IsAffineOpen W) [Nonempty W] :
    X.fromSpecFunctionField = Spec.map (X.germToFunctionField W) ≫ hW.fromSpec := by
  have hgen : genericPoint X ∈ W := by
    obtain ⟨⟨w, hw⟩⟩ := (inferInstance : Nonempty W)
    exact ((genericPoint_spec X).specializes (Set.mem_univ w)).mem_open W.isOpen hw
  change X.fromSpecStalk (genericPoint X) = _
  rw [← hW.fromSpecStalk_eq_fromSpecStalk hgen]
  rfl

namespace Scheme.FiniteEtale

variable {C U : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] {W : C.Opens}

/-- **Extension of a cover over an open containing the points where the normalization is finite
étale.** If the normalization `N ⟶ C` of `C` in a finite étale `U`-scheme `Z` is finite and étale
over an open `W`, then `Z` extends to a finite étale scheme over `V = U ∪ W`. -/
instance (Z : U.FiniteEtale) : QuasiCompact (Z.obj.hom ≫ j) :=
  have : IsFinite Z.obj.hom := Z.property
  inferInstance

instance (Z : U.FiniteEtale) : QuasiSeparated (Z.obj.hom ≫ j) :=
  have : IsFinite Z.obj.hom := Z.property
  inferInstance

instance (Z : U.FiniteEtale) : IsIntegralHom Z.obj.hom :=
  have : IsFinite Z.obj.hom := Z.property
  inferInstance

set_option backward.isDefEq.respectTransparency.types false in
theorem exists_pullback_iso_of_fromNormalization (Z : U.FiniteEtale)
    (hW : IsFinite ((Z.obj.hom ≫ j).fromNormalization ∣_ W) ∧
      Etale ((Z.obj.hom ≫ j).fromNormalization ∣_ W))
    (V : C.Opens) (hjV : j.opensRange ≤ V) (hWV : W ≤ V) (hV : V ≤ j.opensRange ⊔ W) :
    ∃ Z' : V.toScheme.FiniteEtale, Nonempty ((pullback (IsOpenImmersion.lift V.ι j (by
      rw [Scheme.Opens.range_ι]; exact hjV))).obj Z' ≅ Z) := by
  have : IsFinite Z.obj.hom := Z.property
  have : Etale Z.obj.hom := Z.obj.prop
  set pN := (Z.obj.hom ≫ j).fromNormalization
  let e := Scheme.Hom.pullbackFromNormalizationIso Z.obj.hom j
  -- over `U` the normalization is `Z`
  have earr : Arrow.mk (pN ∣_ j.opensRange) ≅ Arrow.mk Z.obj.hom :=
    morphismRestrictOpensRange pN j ≪≫ Arrow.isoMk e (Iso.refl _) (by
      simp [e, pN])
  have hU : IsFinite (pN ∣_ j.opensRange) ∧ Etale (pN ∣_ j.opensRange) :=
    ⟨(MorphismProperty.arrow_mk_iso_iff _ earr).2 inferInstance,
      (MorphismProperty.arrow_mk_iso_iff _ earr).2 inferInstance⟩
  -- over `V`
  have hres (O : C.Opens) (hO : O ≤ V) :
      Arrow.mk ((pN ∣_ V) ∣_ V.ι ⁻¹ᵁ O) ≅ Arrow.mk (pN ∣_ O) := by
    refine morphismRestrictRestrict pN V (V.ι ⁻¹ᵁ O) ≪≫ morphismRestrictEq pN ?_
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 hO]
  have hcov : ⨆ i : Bool, (if i then V.ι ⁻¹ᵁ j.opensRange else V.ι ⁻¹ᵁ W) = ⊤ := by
    rw [iSup_bool_eq]
    refine top_le_iff.1 fun x _ ↦ ?_
    have hx : V.ι x ∈ j.opensRange ⊔ W := hV (by simp)
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  have hVP : IsFinite (pN ∣_ V) ∧ Etale (pN ∣_ V) := by
    constructor <;>
    · refine IsZariskiLocalAtTarget.of_iSup_eq_top _ hcov fun i ↦ ?_
      cases i
      · exact (MorphismProperty.arrow_mk_iso_iff _ (hres W hWV)).2
          (by first | exact hW.1 | exact hW.2)
      · exact (MorphismProperty.arrow_mk_iso_iff _ (hres _ hjV)).2 (by first | exact hU.1 | exact hU.2)
  -- the extension
  have earrV : Arrow.mk (pN ∣_ V) ≅ Arrow.mk (pullback.snd pN V.ι) :=
    morphismRestrictEq pN (Scheme.Opens.opensRange_ι V).symm ≪≫ morphismRestrictOpensRange pN V.ι
  have hP : IsFinite (pullback.snd pN V.ι) ∧ Etale (pullback.snd pN V.ι) :=
    ⟨(MorphismProperty.arrow_mk_iso_iff _ earrV).1 hVP.1,
      (MorphismProperty.arrow_mk_iso_iff _ earrV).1 hVP.2⟩
  let Z' : V.toScheme.FiniteEtale :=
    ⟨MorphismProperty.Over.mk ⊤ (pullback.snd pN V.ι) hP.2, hP.1⟩
  set jV := IsOpenImmersion.lift V.ι j (by rw [Scheme.Opens.range_ι]; exact hjV)
  have hjV' : jV ≫ V.ι = j := IsOpenImmersion.lift_fac _ _ _
  let eL : ((pullback jV).obj Z').obj.left ≅ Z.obj.left :=
    pullbackLeftPullbackSndIso pN V.ι jV ≪≫ pullback.congrHom rfl hjV' ≪≫ e
  refine ⟨Z', ⟨ObjectProperty.isoMk _ (MorphismProperty.Over.isoMk eL ?_)⟩⟩
  change eL.hom ≫ Z.obj.hom = pullback.snd (pullback.snd pN V.ι) jV
  simp only [eL, e, Iso.trans_hom, Category.assoc,
    Scheme.Hom.pullbackFromNormalizationIso_hom_comp, pullback.congrHom_hom]
  rw [pullback.lift_snd, Category.comp_id]
  exact pullbackLeftPullbackSndIso_hom_snd pN V.ι jV

end Scheme.FiniteEtale

end AlgebraicGeometry
