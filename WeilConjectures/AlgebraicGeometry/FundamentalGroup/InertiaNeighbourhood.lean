/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ExtendOverInertia
public import WeilConjectures.RingTheory.InertiaUnramifiedPoint
public import WeilConjectures.RingTheory.StrictlyHenselianNormal

/-!
# Points of a cover fixed by inertia extend to an étale neighbourhood

Let `j : U ⟶ C` be an open immersion into an integral scheme, `W` an affine open with Dedekind
ring of sections and `W ∩ U = D(ϖ)`, `Ω` a separable closure of the function field and `Q` a
maximal ideal over a maximal ideal `m` of `Γ(C, W)` of the integral closure `B` of `Γ(C, W)`
in `Ω`. Write `A = B_Q` (a strictly henselian local ring with fraction field `Ω`,
`Ideal.isStrictlyHenselianLocalRing_atPrime`) and
`a : Spec A ⟶ Spec Γ(C, W) ⟶ C` (`AlgebraicGeometry.Scheme.FiniteEtale.specAtPrime`); the generic
geometric point `η : Spec Ω ⟶ U` factors through `a`.

Let `Z` be a finite étale `U`-scheme and `t` a point of `Z` over `η` fixed by the inertia group of
`Q`. Then there are an étale `C`-scheme `V`, a lift `ℓ : Spec A ⟶ V` of `a`, and a `U`-morphism
`V ×_C U ⟶ Z` mapping the point `(ℓ|_{Spec Ω}, η)` to `t`
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_etale_lift_of_forall_inertia`). For `Z` integral,
`V` is an open of the normalization `N` of `C` in `Z` around the image of the closed point of
`Spec A`: the integral closure of `Γ(C, W)` in `Γ(Z, W)` is étale there
(`Ideal.exists_etale_localization_away_of_inertia`), and `V ×_C U ⊆ N ×_C U = Z`. In general `t`
lies in a connected component of `Z`.

This is the geometric input for the surjectivity part of blueprint
`lem-wf-boundary-stalk-invariants`: an inertia invariant of the generic stalk of a finite locally
constant sheaf comes from a section over the punctured part of an étale neighbourhood of the
boundary point.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X U C : Scheme.{u}} (g : X ⟶ U) (j : U ⟶ C) [IsOpenImmersion j] [IsIntegralHom g]
  [QuasiCompact (g ≫ j)] [QuasiSeparated (g ≫ j)]

@[reassoc (attr := simp)]
lemma pullbackFromNormalizationIso_inv_fst :
    (pullbackFromNormalizationIso g j).inv ≫ pullback.fst _ _ = (g ≫ j).toNormalization := by
  simp [pullbackFromNormalizationIso]

@[reassoc (attr := simp)]
lemma pullbackFromNormalizationIso_inv_snd :
    (pullbackFromNormalizationIso g j).inv ≫ pullback.snd _ _ = g := by
  rw [Iso.inv_comp_eq, pullbackFromNormalizationIso_hom_comp]

end Scheme.Hom

namespace Scheme.FiniteEtale

variable {C U : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [IsIntegral C]
  [Nonempty U] {W : C.Opens} (hW : IsAffineOpen W) [Nonempty W] [IsDedekindDomain Γ(C, W)]
  (ϖ : Γ(C, W)) (hϖ : ϖ ≠ 0) (hWU : j.opensRange ⊓ W = C.basicOpen ϖ)
  (m : Ideal Γ(C, W)) [m.IsMaximal] [PerfectField m.ResidueField]
  {Ω : Type u} [Field Ω] [Algebra C.functionField Ω] [Algebra Γ(C, W) Ω]
  [IsScalarTower Γ(C, W) C.functionField Ω] [IsGalois C.functionField Ω] [IsSepClosed Ω]
  (Q : Ideal (integralClosure Γ(C, W) Ω)) [Q.IsMaximal] [Q.LiesOver m]

/-- The morphism `Spec B_Q ⟶ Spec Γ(C, W) ⟶ C` for a prime `Q` of the integral closure `B` of
`Γ(C, W)` in `Ω`. -/
noncomputable def specAtPrime : Spec (.of (Localization.AtPrime Q)) ⟶ C :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(C, W) (Localization.AtPrime Q))) ≫ hW.fromSpec

omit [QuasiCompact j] [IsDedekindDomain Γ(C, W)] [IsGalois C.functionField Ω] [IsSepClosed Ω]
  in
/-- The generic geometric point of `U` factors through `Spec B_Q ⟶ C`. -/
lemma pointOfAlgebra_comp_eq_specAtPrime :
    pointOfAlgebra Ω (genericPointLift j) ≫ j =
      Spec.map (CommRingCat.ofHom (Ideal.atPrimeToField Q)) ≫ specAtPrime hW Q := by
  rw [Category.assoc, genericPointLift_comp, hW.fromSpecFunctionField_eq, ← Category.assoc,
    ← Spec.map_comp, specAtPrime, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext r
  change algebraMap C.functionField Ω (algebraMap Γ(C, W) C.functionField r) =
    Ideal.atPrimeToField Q (algebraMap _ _ r)
  rw [IsScalarTower.algebraMap_apply Γ(C, W) (integralClosure Γ(C, W) Ω)
    (Localization.AtPrime Q), Ideal.atPrimeToField_algebraMap]
  exact (IsScalarTower.algebraMap_apply Γ(C, W) C.functionField Ω r).symm

set_option maxHeartbeats 1000000 in
-- the elaboration of the integral closure and localization instances is slow
include hϖ hWU m in
/-- **A point of an integral cover fixed by inertia extends to an étale neighbourhood.** Let `Z`
be an integral finite étale `U`-scheme and `t` a point of `Z` over the generic geometric point `η`
fixed by the inertia group of `Q`. Then there are an étale `C`-scheme `V`, a lift
`ℓ : Spec B_Q ⟶ V` of `Spec B_Q ⟶ C` and a `U`-morphism `V ×_C U ⟶ Z` sending the point
`(ℓ|_{Spec Ω}, η)` to `t`. -/
theorem exists_etale_lift_of_forall_inertia_of_isIntegral (Z : U.FiniteEtale)
    [IsIntegral Z.obj.left] (t : (fiber (pointOfAlgebra Ω (genericPointLift j))).obj Z)
    (ht : ∀ σ ∈ Q.inertia (Ω ≃ₐ[C.functionField] Ω),
      (galoisToAut (genericPointLift j) σ).hom.app Z t = t) :
    ∃ (V : C.Etale) (ℓ : Spec (.of (Localization.AtPrime Q)) ⟶ V.left)
      (hℓ : ℓ ≫ V.hom = specAtPrime hW Q) (g : Limits.pullback V.hom j ⟶ Z.obj.left),
      g ≫ Z.obj.hom = pullback.snd _ _ ∧
      pullback.lift (Spec.map (CommRingCat.ofHom (Ideal.atPrimeToField Q)) ≫ ℓ)
        (pointOfAlgebra Ω (genericPointLift j))
        (by rw [Category.assoc, hℓ, pointOfAlgebra_comp_eq_specAtPrime j hW Q]) ≫ g = t.left := by
  have : IsFinite Z.obj.hom := Z.property
  have : Etale Z.obj.hom := Z.obj.prop
  let f := Z.obj.hom ≫ j
  let A := Γ(Z.obj.left, f ⁻¹ᵁ W)
  let _ : Algebra Γ(C, W) A := (f.app W).hom.toAlgebra
  have : IsFractionRing Γ(C, W) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C W hW
  -- the open `f⁻¹ W = f⁻¹ D(ϖ)` is affine
  have hDϖ : C.basicOpen ϖ ≤ j.opensRange := by
    rw [← hWU]
    exact inf_le_left
  have hfW : f ⁻¹ᵁ W = f ⁻¹ᵁ C.basicOpen ϖ := by
    ext x
    change f x ∈ W ↔ f x ∈ C.basicOpen ϖ
    rw [← hWU]
    have hx : f x ∈ j.opensRange := ⟨Z.obj.hom x, rfl⟩
    exact ⟨fun h ↦ ⟨hx, h⟩, fun h ↦ h.2⟩
  have hjD : IsAffineOpen (j ⁻¹ᵁ C.basicOpen ϖ) :=
    (hW.basicOpen ϖ).preimage_of_isOpenImmersion j hDϖ
  have hV : IsAffineOpen (f ⁻¹ᵁ W) := by
    rw [hfW]
    exact hjD.preimage Z.obj.hom
  -- `R' = Γ(C, D(ϖ))`, over which `A` is finite étale
  let R' := Γ(C, C.basicOpen ϖ)
  let _ : Algebra Γ(C, W) R' :=
    (C.presheaf.map (homOfLE (C.basicOpen_le ϖ)).op).hom.toAlgebra
  have : IsLocalization.Away ϖ R' :=
    hW.isLocalization_of_eq_basicOpen ϖ (homOfLE (C.basicOpen_le ϖ)) rfl
  let _ : Algebra R' A := (f.appLE (C.basicOpen ϖ) (f ⁻¹ᵁ W) hfW.le).hom.toAlgebra
  have : IsScalarTower Γ(C, W) R' A := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change (f.app W) r = (f.appLE _ _ hfW.le) ((C.presheaf.map _) r)
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE]
  have : Algebra.Etale R' A := by
    rw [← RingHom.etale_algebraMap]
    exact HasRingHomProperty.appLE (P := @Etale) f inferInstance ⟨_, hW.basicOpen ϖ⟩ ⟨_, hV⟩
      hfW.le
  have : Module.Finite R' A := by
    rw [← RingHom.finite_algebraMap]
    change (f.appLE (C.basicOpen ϖ) (f ⁻¹ᵁ W) hfW.le).hom.Finite
    have : IsIso (j.app (C.basicOpen ϖ)) := Scheme.Hom.isIso_app j _ hDϖ
    rw [Scheme.Hom.comp_appLE, CommRingCat.hom_comp]
    refine RingHom.Finite.comp ?_ (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (j.app (C.basicOpen ϖ))).2)
    have hi : Z.obj.hom ⁻¹ᵁ (j ⁻¹ᵁ C.basicOpen ϖ) = f ⁻¹ᵁ W := by
      rw [hfW]
      rfl
    have h2 : Z.obj.hom.appLE (j ⁻¹ᵁ C.basicOpen ϖ) (f ⁻¹ᵁ W) hi.ge =
        Z.obj.hom.app _ ≫ Z.obj.left.presheaf.map (eqToHom hi.symm).op := by
      change Z.obj.hom.app _ ≫ Z.obj.left.presheaf.map _ = _
      congr 2
    rw [h2, CommRingCat.hom_comp]
    refine RingHom.Finite.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Z.obj.left.presheaf.map (eqToHom hi.symm).op)).2) ?_
    exact IsFinite.finite_app Z.obj.hom _ hjD
  -- the generic geometric point factors through `W`
  have hgen : pointOfAlgebra Ω (genericPointLift j) ≫ j =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(C, W) Ω)) ≫ hW.fromSpec := by
    rw [Category.assoc, genericPointLift_comp, hW.fromSpecFunctionField_eq, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
    ext r
    exact (IsScalarTower.algebraMap_apply Γ(C, W) C.functionField Ω r).symm
  -- `Γ(C, W)`-algebra maps `A → Ω` give points of `Z` over the generic geometric point
  have ht₀ : t.left ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Γ(C, W) Ω)) ≫ hW.fromSpec := by
    rw [← hgen]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ j) (fiber_left_comp _ t))
  have hrange (y : Spec (.of Ω)) : t.left y ∈ f ⁻¹ᵁ W := by
    change (t.left ≫ f) y ∈ W
    rw [ht₀, Scheme.Hom.comp_apply, ← SetLike.mem_coe, ← hW.range_fromSpec]
    exact Set.mem_range_self _
  obtain ⟨y₀⟩ := (inferInstance : Nonempty (Spec (.of Ω)))
  have : Nonempty (f ⁻¹ᵁ W) := ⟨⟨t.left y₀, hrange y₀⟩⟩
  obtain ⟨φ₀, hφ₀⟩ := hV.exists_specMap_comp_fromSpec t.left (by rintro _ ⟨y, rfl⟩; exact hrange y)
  have hφ₀R : f.app W ≫ φ₀ = CommRingCat.ofHom (algebraMap Γ(C, W) Ω) := by
    apply Spec.map_injective
    rw [← cancel_mono hW.fromSpec, ← ht₀, ← hφ₀, Spec.map_comp, Category.assoc,
      Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec f hW hV le_rfl]
    exact (Category.assoc _ _ _).symm
  let ψ₀ : A →ₐ[Γ(C, W)] Ω :=
    { φ₀.hom with commutes' := fun r ↦ RingHom.congr_fun (congrArg CommRingCat.Hom.hom hφ₀R) r }
  -- inertia fixes the image of `ψ₀`
  have hI : ∀ σ ∈ Q.inertia (Ω ≃ₐ[C.functionField] Ω), ∀ x : A, σ (ψ₀ x) = ψ₀ x := by
    intro σ hσ x
    have h := congrArg Over.Hom.left (ht σ hσ)
    rw [galoisToAut_hom_app_left, ← hφ₀, ← Category.assoc, ← Spec.map_comp, cancel_mono] at h
    have := Spec.map_injective h
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom this) x
  -- the integral closure `T` of `Γ(C, W)` in `A` is étale at the point of `t`
  obtain ⟨g, hgq, hgE⟩ := Ideal.exists_etale_localization_away_of_inertia (K := C.functionField)
    m Q ϖ (R' := R') hϖ ψ₀ hI
  let T := integralClosure Γ(C, W) A
  let L := Localization.Away g
  -- the étale neighbourhood `V = Spec T[1/g] ⟶ N ⟶ C`
  let pN := f.fromNormalization
  have hNW : IsAffineOpen (pN ⁻¹ᵁ W) := hW.preimage pN
  let e := f.normalizationObjIso hW
  let ιV : Spec (.of L) ⟶ f.normalization :=
    Spec.map (CommRingCat.ofHom (algebraMap T L)) ≫ Spec.map e.hom ≫ hNW.fromSpec
  have hpV : ιV ≫ pN = Spec.map (CommRingCat.ofHom (algebraMap Γ(C, W) L)) ≫ hW.fromSpec := by
    simp only [ιV, Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec pN hW hNW le_rfl, ← Scheme.Hom.app_eq_appLE,
      Scheme.Hom.fromNormalization_app f hW, ← Category.assoc, ← Spec.map_comp,
      ← Category.assoc, ← Spec.map_comp]
    congr 2
    change CommRingCat.ofHom (algebraMap Γ(C, W) T) ≫ (e.inv ≫ e.hom) ≫ _ = _
    rw [e.inv_hom_id]
    ext r
    change algebraMap T L (algebraMap Γ(C, W) T r) = _
    exact (IsScalarTower.algebraMap_apply Γ(C, W) T L r).symm
  have : Etale (ιV ≫ pN) := by
    rw [hpV]
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(C, W) L))) :=
      HasRingHomProperty.Spec_iff.2 (RingHom.etale_algebraMap.2 hgE)
    infer_instance
  let V : C.Etale := Etale.mk (ιV ≫ pN)
  -- the lift `ℓ : Spec B_Q ⟶ V`
  let ψ : T →ₐ[Γ(C, W)] Ω := ψ₀.comp (IsScalarTower.toAlgHom Γ(C, W) T A)
  let χ : T →+* Localization.AtPrime Q :=
    (algebraMap (integralClosure Γ(C, W) Ω) (Localization.AtPrime Q)).comp
      (Ideal.integralClosureMap ψ)
  have hu : IsUnit (χ g) := IsLocalization.map_units (M := Q.primeCompl) _ ⟨_, hgq⟩
  let lam : L →+* Localization.AtPrime Q := IsLocalization.Away.lift g hu
  have hlam (x : T) : lam (algebraMap T L x) = χ x := IsLocalization.Away.lift_eq g hu x
  have hlamι (x : T) : Ideal.atPrimeToField Q (lam (algebraMap T L x)) = ψ x := by
    rw [hlam]
    exact Ideal.atPrimeToField_algebraMap Q _
  have hℓ' : Spec.map (CommRingCat.ofHom lam) ≫ ιV ≫ pN = specAtPrime hW Q := by
    rw [hpV, specAtPrime, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext r
    change lam (algebraMap T L (algebraMap Γ(C, W) T r)) = _
    rw [hlam]
    change χ (algebraMap Γ(C, W) T r) = algebraMap Γ(C, W) (Localization.AtPrime Q) r
    rw [IsScalarTower.algebraMap_apply Γ(C, W) (integralClosure Γ(C, W) Ω)
      (Localization.AtPrime Q)]
    exact congrArg (algebraMap (integralClosure Γ(C, W) Ω) (Localization.AtPrime Q))
      (Subtype.ext (by exact ψ.commutes r) : Ideal.integralClosureMap ψ (algebraMap Γ(C, W) T r) =
        algebraMap Γ(C, W) (integralClosure Γ(C, W) Ω) r)
  -- the point of `t` in the normalization
  have hring : CommRingCat.ofHom (algebraMap T L) ≫ CommRingCat.ofHom lam ≫
      CommRingCat.ofHom (Ideal.atPrimeToField Q) =
        CommRingCat.ofHom (integralClosure Γ(C, W) A).val.toRingHom ≫ φ₀ := by
    ext x
    exact hlamι x
  have h1 : t.left ≫ f.toNormalization = Spec.map (e.hom ≫
      CommRingCat.ofHom (integralClosure Γ(C, W) A).val.toRingHom ≫ φ₀) ≫ hNW.fromSpec := by
    rw [← hφ₀, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f.toNormalization hNW hV
      (by simp [pN, ← Scheme.Hom.comp_preimage]), ← Scheme.Hom.normalizationObjIso_hom_val f hW,
      ← Category.assoc, ← Spec.map_comp]
    simp only [Category.assoc]
    rfl
  have hkey : Spec.map (CommRingCat.ofHom (Ideal.atPrimeToField Q)) ≫
      Spec.map (CommRingCat.ofHom lam) ≫ ιV = t.left ≫ f.toNormalization := by
    rw [h1, ← hring]
    simp only [ιV, Spec.map_comp, Category.assoc]
  -- the morphism `V ×_C U ⟶ N ×_C U ≅ Z`
  let gmap : Limits.pullback (ιV ≫ pN) j ⟶ Z.obj.left :=
    Limits.pullback.map (ιV ≫ pN) j pN j ιV (𝟙 U) (𝟙 C) (by simp) (by simp) ≫
      (Scheme.Hom.pullbackFromNormalizationIso Z.obj.hom j).hom
  refine ⟨V, Spec.map (CommRingCat.ofHom lam), hℓ', gmap, ?_, ?_⟩
  · simp only [gmap, Category.assoc, Scheme.Hom.pullbackFromNormalizationIso_hom_comp]
    rw [Limits.pullback.lift_snd, Category.comp_id]
    rfl
  · have h : pullback.lift (Spec.map (CommRingCat.ofHom (Ideal.atPrimeToField Q)) ≫
        Spec.map (CommRingCat.ofHom lam)) (pointOfAlgebra Ω (genericPointLift j)) (by
          rw [Category.assoc]
          exact (congrArg (Spec.map (CommRingCat.ofHom (Ideal.atPrimeToField Q)) ≫ ·)
            hℓ').trans (pointOfAlgebra_comp_eq_specAtPrime j hW Q).symm) ≫
        Limits.pullback.map (ιV ≫ pN) j pN j ιV (𝟙 U) (𝟙 C) (by simp) (by simp) =
          t.left ≫ (Scheme.Hom.pullbackFromNormalizationIso Z.obj.hom j).inv := by
      refine Limits.pullback.hom_ext ?_ ?_
      · rw [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc,
          Category.assoc]
        exact hkey.trans (congrArg (t.left ≫ ·)
          (Scheme.Hom.pullbackFromNormalizationIso_inv_fst Z.obj.hom j).symm)
      · rw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc,
          Category.comp_id, Category.assoc, Scheme.Hom.pullbackFromNormalizationIso_inv_snd]
        exact (fiber_left_comp _ t).symm
    refine (congrArg (· ≫ (Scheme.Hom.pullbackFromNormalizationIso Z.obj.hom j).hom) h).trans ?_
    simp

include hϖ hWU m in
/-- **A point of a cover fixed by inertia extends to an étale neighbourhood.** Let `U` be
connected, with connected finite étale `U`-schemes integral (e.g. `U` normal), `Z` a finite étale
`U`-scheme and `t` a point of `Z` over the generic geometric point `η` fixed by the inertia group
of `Q`. Then there are an étale `C`-scheme `V`, a lift `ℓ : Spec B_Q ⟶ V` of `Spec B_Q ⟶ C` and
a `U`-morphism `V ×_C U ⟶ Z` sending the point `(ℓ|_{Spec Ω}, η)` to `t`. -/
theorem exists_etale_lift_of_forall_inertia [ConnectedSpace U]
    (hint : ∀ Y : U.FiniteEtale, PreGaloisCategory.IsConnected Y → IsIntegral Y.obj.left)
    (Z : U.FiniteEtale) (t : (fiber (pointOfAlgebra Ω (genericPointLift j))).obj Z)
    (ht : ∀ σ ∈ Q.inertia (Ω ≃ₐ[C.functionField] Ω),
      (galoisToAut (genericPointLift j) σ).hom.app Z t = t) :
    ∃ (V : C.Etale) (ℓ : Spec (.of (Localization.AtPrime Q)) ⟶ V.left)
      (hℓ : ℓ ≫ V.hom = specAtPrime hW Q) (g : Limits.pullback V.hom j ⟶ Z.obj.left),
      g ≫ Z.obj.hom = pullback.snd _ _ ∧
      pullback.lift (Spec.map (CommRingCat.ofHom (Ideal.atPrimeToField Q)) ≫ ℓ)
        (pointOfAlgebra Ω (genericPointLift j))
        (by rw [Category.assoc, hℓ, pointOfAlgebra_comp_eq_specAtPrime j hW Q]) ≫ g = t.left := by
  obtain ⟨Y, i, y, rfl, hY, hi⟩ :=
    PreGaloisCategory.fiber_in_connected_component (fiber (pointOfAlgebra Ω (genericPointLift j)))
      Z t
  have := hint Y hY
  have hinj : Function.Injective ((fiber (pointOfAlgebra Ω (genericPointLift j))).map i) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback _).1
      inferInstance
  have hy : ∀ σ ∈ Q.inertia (Ω ≃ₐ[C.functionField] Ω),
      (galoisToAut (genericPointLift j) σ).hom.app Y y = y := by
    intro σ hσ
    apply hinj
    rw [← ht σ hσ]
    exact (ConcreteCategory.congr_hom
      ((galoisToAut (genericPointLift j) σ).hom.naturality i) y).symm
  obtain ⟨V, ℓ, hℓ, g, hg, hgy⟩ :=
    exists_etale_lift_of_forall_inertia_of_isIntegral j hW ϖ hϖ hWU m Q Y y hy
  refine ⟨V, ℓ, hℓ, g ≫ i.hom.left, ?_, ?_⟩
  · rw [Category.assoc, MorphismProperty.Over.w i.hom, hg]
  · rw [← Category.assoc, hgy]
    rfl

end Scheme.FiniteEtale

end AlgebraicGeometry
