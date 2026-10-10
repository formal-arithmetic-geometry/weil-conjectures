/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
public import WeilConjectures.Topology.Sheaves.CohomologyColimit

/-!
# Cohomology and base change along a field extension

Let `X` be a scheme over a field `k`, let `K/k` be a field extension, let
`p : X_K = X ×_{Spec k} Spec K ⟶ X` be the projection and let `M` be a quasi-coherent
`𝒪_X`-module.

* For an affine open `W` of `X`, the open `p⁻¹ W` of `X_K` is `Spec (Γ(X, W) ⊗[k] K)`, and the
  sections of `p^* M` over it are `K ⊗[k] Γ(M, W)`.
* Choosing a `k`-basis `B` of `K`, this says that `p_* p^* M` is the direct sum `⨁_B M` (as a
  sheaf of abelian groups).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  (K : Type u) [Field K] [Algebra k K]

namespace BaseChangeField

/-- The structure map `k ⟶ Γ(X, W)` of an affine open `W`. -/
noncomputable def structureMap {W : X.Opens} (hW : IsAffineOpen W) :
    CommRingCat.of k ⟶ Γ(X, W) :=
  Spec.preimage (hW.fromSpec ≫ X ↘ Spec (.of k))

lemma spec_map_structureMap {W : X.Opens} (hW : IsAffineOpen W) :
    Spec.map (structureMap k hW) = hW.fromSpec ≫ X ↘ Spec (.of k) :=
  Spec.map_preimage _

/-- `Γ(X, W)` as a `k`-algebra. -/
noncomputable abbrev algebra {W : X.Opens} (hW : IsAffineOpen W) : Algebra k Γ(X, W) :=
  (structureMap k hW).hom.toAlgebra

/-- The ring `Γ(X, W) ⊗[k] K`. -/
noncomputable abbrev tensorRing (K : Type u) [Field K] [Algebra k K] {W : X.Opens}
    (hW : IsAffineOpen W) : CommRingCat.{u} :=
  letI := algebra k hW
  CommRingCat.of (Γ(X, W) ⊗[k] K)

/-- The inclusion `Γ(X, W) ⟶ Γ(X, W) ⊗[k] K`. -/
noncomputable abbrev inclLeft {W : X.Opens} (hW : IsAffineOpen W) :
    Γ(X, W) ⟶ tensorRing k K hW :=
  letI := algebra k hW
  CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom

/-- The inclusion `K ⟶ Γ(X, W) ⊗[k] K`. -/
noncomputable abbrev inclRight {W : X.Opens} (hW : IsAffineOpen W) :
    CommRingCat.of K ⟶ tensorRing k K hW :=
  letI := algebra k hW
  CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom

lemma isPullback_spec {W : X.Opens} (hW : IsAffineOpen W) :
    IsPullback (Spec.map (inclLeft k K hW)) (Spec.map (inclRight k K hW))
      (Spec.map (structureMap k hW)) (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  letI := algebra k hW
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct k Γ(X, W) K)

variable {k K} in
/-- The base change `X_K ⟶ X`. -/
noncomputable abbrev proj : Limits.pullback (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ X :=
  Limits.pullback.fst _ _

/-- The open immersion `Spec (Γ(X, W) ⊗[k] K) ⟶ X_K` onto `p⁻¹ W`. -/
noncomputable def openImm {W : X.Opens} (hW : IsAffineOpen W) :
    Spec (tensorRing k K hW) ⟶ Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  Limits.pullback.lift (Spec.map (inclLeft k K hW) ≫ hW.fromSpec) (Spec.map (inclRight k K hW)) (by
    rw [Category.assoc, ← spec_map_structureMap k]
    exact (isPullback_spec k K hW).w)

@[reassoc (attr := simp)]
lemma openImm_fst {W : X.Opens} (hW : IsAffineOpen W) :
    openImm k K hW ≫ proj = Spec.map (inclLeft k K hW) ≫ hW.fromSpec :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma openImm_snd {W : X.Opens} (hW : IsAffineOpen W) :
    openImm k K hW ≫ Limits.pullback.snd _ _ = Spec.map (inclRight k K hW) :=
  Limits.pullback.lift_snd _ _ _

lemma isPullback_openImm {W : X.Opens} (hW : IsAffineOpen W) :
    IsPullback (openImm k K hW) (Spec.map (inclLeft k K hW)) proj hW.fromSpec := by
  refine IsPullback.of_right (h₁₂ := Limits.pullback.snd _ _) (h₂₂ := X ↘ Spec (.of k))
    (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap k K))) ?_ (openImm_fst k K hW)
    (IsPullback.of_hasPullback _ _).flip
  rw [openImm_snd, ← spec_map_structureMap k]
  exact (isPullback_spec k K hW).flip

instance {W : X.Opens} (hW : IsAffineOpen W) : IsOpenImmersion (openImm k K hW) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (isPullback_openImm k K hW).flip inferInstance

lemma opensRange_openImm {W : X.Opens} (hW : IsAffineOpen W) :
    (openImm k K hW).opensRange = proj ⁻¹ᵁ W := by
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange]
  have h : (openImm k K hW).base = (isPullback_openImm k K hW).isoPullback.hom.base ≫
      (Limits.pullback.fst proj hW.fromSpec).base := by
    rw [← Scheme.Hom.comp_base, (isPullback_openImm k K hW).isoPullback_hom_fst]
  rw [h, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.2 (ConcreteCategory.bijective_of_isIso
      (isPullback_openImm k K hW).isoPullback.hom.base).2, Set.image_univ,
    IsOpenImmersion.range_pullbackFst, hW.opensRange_fromSpec]

variable {k K} {W : X.Opens} (hW : IsAffineOpen W) (M : X.Modules)

open Modules

lemma top_le_fromSpec_preimage : (⊤ : (Spec Γ(X, W)).Opens) ≤ hW.fromSpec ⁻¹ᵁ W :=
  hW.fromSpec_preimage_self.ge

/-- The sections of `M` over the affine open `W` are the global sections of its pullback to
`Spec Γ(X, W)`. -/
noncomputable def sectionsEquiv : Γ(M, W) ≃ₗ[Γ(X, W)]
    Γ((Modules.pullback hW.fromSpec).obj M, ⊤) := by
  refine LinearEquiv.ofBijective
    { toFun m := ((Modules.pullback hW.fromSpec).obj M).presheaf.map
        (homOfLE (top_le_fromSpec_preimage hW)).op (pullbackUnitApp hW.fromSpec M W m)
      map_add' _ _ := by rw [map_add, map_add]
      map_smul' a m := ?_ } ?_
  · change _ = a • _
    rw [pullbackUnitApp_smul, Modules.map_smul]
    rw [smul_Spec_def, hW.fromSpec_app_self]
    congr 1
  · have h₁ := bijective_pullbackUnit_app_of_isOpenImmersion hW.fromSpec M
      hW.opensRange_fromSpec.ge
    have : IsIso (homOfLE (top_le_fromSpec_preimage hW)) := by
      rw [show homOfLE (top_le_fromSpec_preimage hW) = eqToHom hW.fromSpec_preimage_self.symm
        from Subsingleton.elim _ _]
      infer_instance
    exact (ConcreteCategory.bijective_of_isIso
      (((Modules.pullback hW.fromSpec).obj M).presheaf.map
        (homOfLE (top_le_fromSpec_preimage hW)).op)).comp h₁

lemma sectionsEquiv_apply (m : Γ(M, W)) : sectionsEquiv hW M m =
    ((Modules.pullback hW.fromSpec).obj M).presheaf.map
      (homOfLE (top_le_fromSpec_preimage hW)).op (pullbackUnitApp hW.fromSpec M W m) :=
  rfl

variable (K) in
lemma top_le_openImm_preimage :
    (⊤ : (Spec (tensorRing k K hW)).Opens) ≤ openImm k K hW ⁻¹ᵁ proj ⁻¹ᵁ W := by
  rw [← opensRange_openImm k K hW, Scheme.Hom.preimage_opensRange]

variable (K) in
/-- The first step of `BaseChangeField.sectionsBaseChange`: sections of `p^* M` over `p⁻¹ W` are
the global sections of the pullback to `Spec (Γ(X, W) ⊗[k] K)`. -/
noncomputable def sectionsBaseChange₁ :
    Γ((Modules.pullback (proj (k := k) (K := K))).obj M, proj ⁻¹ᵁ W) ≃+
      Γ((Modules.pullback (openImm k K hW)).obj ((Modules.pullback proj).obj M), ⊤) := by
  refine AddEquiv.ofBijective (({
      toFun x := ((Modules.pullback (openImm k K hW)).obj
          ((Modules.pullback proj).obj M)).presheaf.map
        (homOfLE (top_le_openImm_preimage (k := k) K hW)).op
          (pullbackUnitApp (openImm k K hW) _ (proj ⁻¹ᵁ W) x)
      map_zero' := by rw [map_zero, map_zero]
      map_add' _ _ := by rw [map_add, map_add] }) :
        Γ((Modules.pullback (proj (k := k) (K := K))).obj M, proj ⁻¹ᵁ W) →+
          Γ((Modules.pullback (openImm k K hW)).obj ((Modules.pullback proj).obj M), ⊤)) ?_
  have h₁ := bijective_pullbackUnit_app_of_isOpenImmersion (openImm k K hW)
    ((Modules.pullback proj).obj M) (opensRange_openImm k K hW).ge
  have : IsIso (homOfLE (top_le_openImm_preimage (k := k) K hW)) := by
    rw [show homOfLE (top_le_openImm_preimage (k := k) K hW) = eqToHom (by
      rw [← opensRange_openImm k K hW, Scheme.Hom.preimage_opensRange]) from
        Subsingleton.elim _ _]
    infer_instance
  exact (ConcreteCategory.bijective_of_isIso
    (((Modules.pullback (openImm k K hW)).obj ((Modules.pullback proj).obj M)).presheaf.map
      (homOfLE (top_le_openImm_preimage (k := k) K hW)).op)).comp h₁

variable (K) in
/-- **Sections of a pullback along a field extension over an affine open.** For an affine open
`W` of `X`, the sections of `p^* M` over `p⁻¹ W` are the global sections of the pullback of
`M|_W` along `Spec (Γ(X, W) ⊗[k] K) ⟶ Spec Γ(X, W)`. -/
noncomputable def sectionsBaseChange :
    Γ((Modules.pullback (proj (k := k) (K := K))).obj M, proj ⁻¹ᵁ W) ≃+
      Γ((Modules.pullback (Spec.map (inclLeft k K hW))).obj
        ((Modules.pullback hW.fromSpec).obj M), ⊤) :=
  (sectionsBaseChange₁ K hW M).trans ((appLinearEquivOfIso (pullbackCompOfEq (openImm k K hW)
    proj _ rfl M) ⊤).toAddEquiv.trans (appLinearEquivOfIso (pullbackCompOfEq
      (Spec.map (inclLeft k K hW)) hW.fromSpec _ (openImm_fst k K hW).symm M).symm ⊤).toAddEquiv)

lemma sectionsBaseChange_apply
    (x : Γ((Modules.pullback (proj (k := k) (K := K))).obj M, proj ⁻¹ᵁ W)) :
    sectionsBaseChange K hW M x = appLinearEquivOfIso (pullbackCompOfEq
      (Spec.map (inclLeft k K hW)) hW.fromSpec _ (openImm_fst k K hW).symm M).symm ⊤
        (appLinearEquivOfIso (pullbackCompOfEq (openImm k K hW) proj _ rfl M) ⊤
          (sectionsBaseChange₁ K hW M x)) :=
  rfl

lemma sectionsBaseChange_pullbackUnitApp (m : Γ(M, W)) :
    sectionsBaseChange K hW M (pullbackUnitApp proj M W m) =
      pullbackUnitApp (Spec.map (inclLeft k K hW)) _ ⊤ (sectionsEquiv hW M m) := by
  have hV₂ : (⊤ : (Spec (tensorRing k K hW)).Opens) ≤ (openImm k K hW ≫ proj) ⁻¹ᵁ W :=
    top_le_openImm_preimage (k := k) K hW
  have hV₃ : (⊤ : (Spec (tensorRing k K hW)).Opens) ≤
      Spec.map (inclLeft k K hW) ⁻¹ᵁ hW.fromSpec ⁻¹ᵁ W := by
    rw [hW.fromSpec_preimage_self, Scheme.Hom.preimage_top]
  have h₂ := pullbackCompOfEq_hom_app_map_pullbackUnit (openImm k K hW) proj _ rfl M m
    (top_le_openImm_preimage (k := k) K hW) hV₂
  have h₃ := pullbackCompOfEq_hom_app_map_pullbackUnit (Spec.map (inclLeft k K hW))
    hW.fromSpec _ (openImm_fst k K hW).symm M m hV₃ hV₂
  change ((pullbackCompOfEq (Spec.map (inclLeft k K hW)) hW.fromSpec _
    (openImm_fst k K hW).symm M).inv).app ⊤ (((pullbackCompOfEq (openImm k K hW) proj _ rfl
      M).hom).app ⊤ _) = _
  erw [h₂, ← h₃]
  rw [← ConcreteCategory.comp_apply]
  erw [← Modules.Hom.comp_app, Iso.hom_inv_id, Modules.Hom.id_app, ConcreteCategory.id_apply]
  have key := Hom.app_presheaf_map (pullbackUnit (Spec.map (inclLeft k K hW))
    ((Modules.pullback hW.fromSpec).obj M)) (homOfLE (top_le_fromSpec_preimage hW))
      (pullbackUnitApp hW.fromSpec M W m)
  rw [pushforward_obj_presheaf_map] at key
  exact key.symm

variable (k) in
/-- The global function on `X_K` given by a scalar `c ∈ K`. -/
noncomputable def scalar (c : K) : Γ(Limits.pullback (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))), ⊤) :=
  Scheme.Hom.appTop (Limits.pullback.snd (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ((ΓSpecIso (.of K)).inv c)

lemma openImm_app_scalar (c : K) :
    (Spec (tensorRing k K hW)).presheaf.map (homOfLE (top_le_openImm_preimage (k := k) K hW)).op
      ((openImm k K hW).app (proj ⁻¹ᵁ W)
        ((Limits.pullback (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.map
            (homOfLE (le_top : proj ⁻¹ᵁ W ≤ ⊤)).op
            (scalar k c))) =
      (Spec (tensorRing k K hW)).presheaf.map (TopologicalSpace.Opens.leTop ⊤).op
        ((ΓSpecIso (tensorRing k K hW)).inv (inclRight k K hW c)) := by
  have e₁ : (openImm k K hW).appTop (scalar k c) =
      (ΓSpecIso (tensorRing k K hW)).inv (inclRight k K hW c) := by
    rw [scalar, ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, openImm_snd,
      ← ConcreteCategory.comp_apply, ← ΓSpecIso_inv_naturality, ConcreteCategory.comp_apply]
  have e₂ := congr($(Scheme.Hom.naturality (openImm k K hW)
    (homOfLE (le_top : proj ⁻¹ᵁ W ≤ ⊤)).op) (scalar k c))
  simp only [ConcreteCategory.comp_apply] at e₂
  rw [e₂]
  erw [e₁]
  rw [show (TopologicalSpace.Opens.leTop (⊤ : (Spec (tensorRing k K hW)).Opens)) = 𝟙 _ from
    Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

lemma sectionsBaseChange_smul (c : K)
    (x : Γ((Modules.pullback (proj (k := k) (K := K))).obj M, proj ⁻¹ᵁ W)) :
    sectionsBaseChange K hW M (((Limits.pullback (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.map
            (homOfLE (le_top : proj ⁻¹ᵁ W ≤ ⊤)).op
            (scalar k c)) • x) = inclRight k K hW c • sectionsBaseChange K hW M x := by
  have h₁ : sectionsBaseChange₁ K hW M (((Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.map
        (homOfLE (le_top : proj ⁻¹ᵁ W ≤ ⊤)).op (scalar k c)) • x) =
      (Spec (tensorRing k K hW)).presheaf.map (TopologicalSpace.Opens.leTop ⊤).op
        ((ΓSpecIso (tensorRing k K hW)).inv (inclRight k K hW c)) •
          sectionsBaseChange₁ K hW M x := by
    simp only [sectionsBaseChange₁, AddEquiv.ofBijective_apply, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk]
    rw [pullbackUnitApp_smul, Modules.map_smul, openImm_app_scalar]
  rw [sectionsBaseChange_apply, sectionsBaseChange_apply, h₁, LinearEquiv.map_smul,
    LinearEquiv.map_smul, smul_Spec_def]

end BaseChangeField

end AlgebraicGeometry.Scheme
