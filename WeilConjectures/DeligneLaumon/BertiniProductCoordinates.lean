/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
import WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealTensorSections
import WeilConjectures.AlgebraicGeometry.Modules.SectionAvoidance
import WeilConjectures.AlgebraicGeometry.NonvanishingTensorPullback
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination

/-!
# Products of ideal generators with projective coordinates

The section calculation in Stacks Project, Varieties, Tag 0FD5.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules

/-- Restriction is monoidal, so it preserves tensoring an isomorphism with an object. -/
private lemma restrict_tensor_iso {X : Scheme.{u}} {M M' : X.Modules}
    (f : M ⟶ M') (N : X.Modules) {U : X.Opens}
    [IsIso ((restrictFunctor U.ι).map f)] :
    IsIso ((restrictFunctor U.ι).map (f ▷ N)) := by
  rw [NatIso.isIso_map_iff (restrictFunctorIsoPullback U.ι)] at *
  have h := Functor.LaxMonoidal.μ_natural_left (pullback U.ι) f N
  rw [(IsIso.eq_inv_comp _).mpr h.symm]
  infer_instance

private theorem nonvanishing_iso {X : Scheme.{u}} {M N : X.Modules}
    [M.IsInvertible] [N.IsInvertible] (e : M ≅ N) (s : Γ(M, ⊤)) :
    nonvanishingLocus N (e.hom.app ⊤ s) = nonvanishingLocus M s := by
  ext x
  rw [mem_nonvanishingLocus_iff_generatesAt, mem_nonvanishingLocus_iff_generatesAt]
  have transport {P Q : X.Modules} (a : P ≅ Q) (t : Γ(P, ⊤))
      (h : GeneratesAt t x) : GeneratesAt (a.hom.app ⊤ t) x := by
    obtain ⟨U, hxU, ht⟩ := h
    refine ⟨U, hxU, ?_⟩
    rw [← Hom.app_presheaf_map]
    exact ht.app_hom a
  constructor
  · intro h
    have h' := transport e.symm (e.hom.app ⊤ s) h
    simpa only [Iso.symm_hom, inv_app_hom_app_apply_of_iso] using h'
  · exact transport e s

private theorem nonvanishing_tensor {X : Scheme.{u}} (M N : X.Modules)
    [M.IsInvertible] [N.IsInvertible] (s : Γ(M, ⊤)) (t : Γ(N, ⊤)) :
    nonvanishingLocus (M ⊗ N) (tmulSection s t) =
      nonvanishingLocus M s ∩ nonvanishingLocus N t := by
  have := IsInvertible.sheafOfModules_isInvertible M
  have := IsInvertible.sheafOfModules_isInvertible N
  ext x
  obtain ⟨U, hxU, _, ⟨e, he⟩, d, hd⟩ := exists_isFreeGenerator₂ M N
    (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨a, ha⟩ := he.exists_smul_eq (M.presheaf.map (homOfLE le_top).op s)
  obtain ⟨b, hb⟩ := hd.exists_smul_eq (N.presheaf.map (homOfLE le_top).op t)
  have hp : (M ⊗ N).presheaf.map (homOfLE le_top).op (tmulSection s t) =
      (a * b) • tmulSection e d := by
    rw [tmulSection_map, ← ha, ← hb, smul_tmulSection, tmulSection_smul, smul_smul]
  change x ∈ nonvanishingLocus (M ⊗ N) _ ↔
    x ∈ nonvanishingLocus M s ∧ x ∈ nonvanishingLocus N t
  rw [mem_nonvanishingLocus_iff_generatesAt,
    mem_nonvanishingLocus_iff_generatesAt, mem_nonvanishingLocus_iff_generatesAt,
    generatesAt_iff_mem_basicOpen (he.tmulSection hd) hp hxU,
    generatesAt_iff_mem_basicOpen he ha.symm hxU,
    generatesAt_iff_mem_basicOpen hd hb.symm hxU, X.basicOpen_mul]
  rfl

private theorem ideal_image_map {X : Scheme.{u}} (J : X.IdealSheafData)
    {M N : X.Modules} (a : M ⟶ N) (v : Γ(J.toModules ⊗ M, ⊤)) :
    (J.toModulesι ▷ N ≫ (λ_ N).hom).app ⊤ ((J.toModules ◁ a).app ⊤ v) =
      a.app ⊤ ((J.toModulesι ▷ M ≫ (λ_ M).hom).app ⊤ v) := by
  have h : J.toModules ◁ a ≫ J.toModulesι ▷ N ≫ (λ_ N).hom =
      (J.toModulesι ▷ M ≫ (λ_ M).hom) ≫ a := by
    let i : J.toModules ⟶ 𝟙_ X.Modules := J.toModulesι
    change J.toModules ◁ a ≫ i ▷ N ≫ (λ_ N).hom = (i ▷ M ≫ (λ_ M).hom) ≫ a
    rw [whisker_exchange_assoc, leftUnitor_naturality]
    simp only [Category.assoc]
  simpa only [Hom.comp_app, ConcreteCategory.comp_apply] using
    congrArg (fun b ↦ b.app ⊤ v) h

private theorem ideal_image_tensor {X : Scheme.{u}} (J : X.IdealSheafData)
    (M N : X.Modules) (v : Γ(J.toModules ⊗ M, ⊤)) (t : Γ(N, ⊤)) :
    (J.toModulesι ▷ (M ⊗ N) ≫ (λ_ (M ⊗ N)).hom).app ⊤
        ((α_ J.toModules M N).hom.app ⊤ (tmulSection v t)) =
      tmulSection ((J.toModulesι ▷ M ≫ (λ_ M).hom).app ⊤ v) t := by
  have h : (α_ J.toModules M N).hom ≫ J.toModulesι ▷ (M ⊗ N) ≫
      (λ_ (M ⊗ N)).hom = (J.toModulesι ▷ M ≫ (λ_ M).hom) ▷ N := by
    let i : J.toModules ⟶ 𝟙_ X.Modules := J.toModulesι
    change (α_ J.toModules M N).hom ≫ i ▷ (M ⊗ N) ≫ (λ_ (M ⊗ N)).hom =
      (i ▷ M ≫ (λ_ M).hom) ▷ N
    rw [← associator_naturality_left_assoc, leftUnitor_tensor_hom]
    simp only [Iso.hom_inv_id_assoc, comp_whiskerRight]
  have hh := congrArg (fun b ↦ b.app ⊤ (tmulSection v t)) h
  simpa only [Hom.comp_app, ConcreteCategory.comp_apply,
    whiskerRight_app_tmulSection] using hh

private theorem vanishing_range {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (L : X.Modules) [L.IsInvertible] (n : ℕ)
    (v : Γ(L.tensorPow n, ⊤)) :
    pullbackΓ i (L.tensorPow n) v = 0 ↔
      ∃ w, (i.ker.toModulesι ▷ L.tensorPow n ≫ (λ_ _).hom).app ⊤ w = v := by
  classical
  let M := L.tensorPow n
  let adj := Classical.choose (exists_tensorPullbackAdjunction i)
  let c := (adj.leftAdjointUniq (pullbackPushforwardAdjunction i)).app M
  have hc : c.hom.app ⊤ ((adj.unit.app M).app ⊤ v) = pullbackΓ i M v := by
    rw [pullbackΓ_apply]
    exact congrArg (fun t ↦ t.app ⊤ v)
      (adj.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction i) M)
  have hinj : Function.Injective (c.hom.app ⊤) :=
    (ConcreteCategory.bijective_of_isIso (c.hom.app ⊤)).1
  have hz : pullbackΓ i M v = 0 ↔ (adj.unit.app M).app ⊤ v = 0 := by
    rw [← hc]
    exact ⟨fun h ↦ hinj (h.trans (map_zero _).symm), fun h ↦ by rw [h, map_zero]⟩
  exact hz.trans ((closedImmersion_ideal_tensor_sections i L n).2 v)

private theorem pullback_generatesAt_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsInvertible] (s : Γ(M, ⊤)) (x : X) :
    GeneratesAt (pullbackΓ f M s) x ↔ GeneratesAt s (f x) := by
  classical
  let adj := Classical.choose (exists_tensorPullbackAdjunction f)
  let c := (adj.leftAdjointUniq (pullbackPushforwardAdjunction f)).app M
  have hc : c.hom.app ⊤ ((adj.unit.app M).app ⊤ s) = pullbackΓ f M s := by
    rw [pullbackΓ_apply]
    exact congrArg (fun t ↦ t.app ⊤ s)
      (adj.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction f) M)
  have : ((tensorPullback f).obj M).IsInvertible :=
    IsInvertible.of_iso c.symm
  rw [← mem_nonvanishingLocus_iff_generatesAt, ← mem_nonvanishingLocus_iff_generatesAt,
    ← hc, nonvanishing_iso c]
  exact nonvanishing_tensorPullback f M s x

private theorem pullback_relation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (s t : Γ(M, ⊤)) (R : Y.Opens) (p : Γ(Y, R))
    (h : M.presheaf.map (homOfLE (le_top : R ≤ ⊤)).op s =
      p • M.presheaf.map (homOfLE (le_top : R ≤ ⊤)).op t)
    (V : X.Opens) (hle : V ≤ f ⁻¹ᵁ R) :
    ((pullback f).obj M).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        (pullbackΓ f M s) =
      f.appLE R V hle p •
        ((pullback f).obj M).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
          (pullbackΓ f M t) := by
  have hp (v : Γ(M, ⊤)) : pullbackΓ f M v = pullbackTopSection f v := by
    rw [pullbackΓ_apply]
    exact (Scheme.Modules.presheaf_map_id_apply _ _).symm
  rw [hp, hp, ← presheaf_map_homOfLE_map_homOfLE
      (le_top : f ⁻¹ᵁ R ≤ ⊤) hle,
    ← presheaf_map_homOfLE_map_homOfLE (le_top : f ⁻¹ᵁ R ≤ ⊤) hle,
    pullbackTopSection_map, pullbackTopSection_map, h, pullbackSection_smul,
    Scheme.Modules.map_smul]
  rfl

/-- Products of ideal-twist generators and pulled-back projective coordinates vanish on the
closed subscheme. On its complement they include a local generator at every point. Wherever
one product generates, its projective coordinate generates, and the ratios of the products
are the ratios of the original projective coordinates.

Source: Stacks Project, varieties.tex, Tag 0FD5, lemma-generate-over-complement, the paragraph
starting with "Proof of the claim" and its displayed fractions.
(blueprint: lem-zl-bertini-product-coordinate-relations).

Proof: The ideal inclusion is an isomorphism on the complement of its support. Consequently
the images of the given ideal-twist generators generate the first tensor factor there. At
each point one of these images generates, by the rank-one fibre criterion. The standard
projective charts cover, so one pulled-back coordinate generates the second factor there.
Their tensor product generates, and this remains true under the tensor-power isomorphism
and restriction to the complement. Every product is in the image of the ideal inclusion
tensored with the degree-n module: use the associator and the tensor-power isomorphism to
write it as the image of the corresponding ideal-valued tensor. The kernel-of-restriction
identification therefore shows that its restriction to the closed subscheme is zero.
For the last assertion, trivialize both factors near a point. If their product is a local
basis, the product of their coefficients is a unit, hence each coefficient is a unit. Thus
the second factor is a basis there and the point maps into its standard chart. On that chart
the relation T_c = (T_c/T_b) T_b pulls back under j and transports through e. Tensoring this
relation with the fixed ideal-twist section gives the same ratio equation for the products.
The tensor-power comparison and restriction preserve scalar multiplication and the equation.
This proves the relation on the whole generating locus by restriction; it also applies to
empty schemes and to empty coordinate sets, when the covering assertion is vacuous. -/
theorem bertini_product_coordinate_relations
    {Y Z S : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (L : Y.Modules) [L.IsInvertible] (n r : ℕ) (hrn : r ≤ n)
    (σ : SheafOfModules.GeneratingSections (i.ker.toModules ⊗ₘ L.tensorPow (n - r)))
    (B : Type u) (j : Y ⟶ ℙ(B; S))
    (e : ProjectiveSpace.twistRestrict j 1 ≅ L.tensorPow r) :
    let U : Y.Opens := i.ker.support.compl
    let N := (Scheme.Modules.pullback U.ι).obj (L.tensorPow n)
    let μ : i.ker.toModules ⊗ₘ L.tensorPow (n - r) ⟶ L.tensorPow (n - r) :=
      i.ker.toModulesι ▷ L.tensorPow (n - r) ≫ (λ_ _).hom
    let E : L.tensorPow (n - r) ⊗ₘ L.tensorPow r ≅ L.tensorPow n :=
      (L.tensorPowAddIso (n - r) r).symm ≪≫
        eqToIso (congrArg L.tensorPow (Nat.sub_add_cancel hrn))
    let v : σ.I → B → Γ(L.tensorPow n, ⊤) := fun a b ↦ E.hom.app ⊤
      (tmulSection (μ.app ⊤ ((σ.s a).val (op ⊤)))
        (e.hom.app ⊤ (pullbackSection j (ProjectiveSpace.twistOneSection B S b))))
    let w : σ.I → B → Γ(N, ⊤) := fun a b ↦ pullbackΓ U.ι (L.tensorPow n) (v a b)
    (∀ a b, pullbackΓ i (L.tensorPow n) (v a b) = 0) ∧
      (∀ x : U, ∃ a b, GeneratesAt (w a b) x) ∧
      ∀ a b, ∃ hle : generatingLocus (w a b) ≤
          (U.ι ≫ j) ⁻¹ᵁ ProjectiveSpace.standardOpen B S b,
        ∀ c, N.presheaf.map (homOfLE
          (le_top : generatingLocus (w a b) ≤ ⊤)).op (w a c) =
            (U.ι ≫ j).appLE (ProjectiveSpace.standardOpen B S b)
              (generatingLocus (w a b)) hle (ProjectiveSpace.coordRatio B S b c) •
              N.presheaf.map (homOfLE
                (le_top : generatingLocus (w a b) ≤ ⊤)).op (w a b) := by
  classical
  let U : Y.Opens := i.ker.support.compl
  let N := (Scheme.Modules.pullback U.ι).obj (L.tensorPow n)
  let μ : i.ker.toModules ⊗ₘ L.tensorPow (n - r) ⟶ L.tensorPow (n - r) :=
    i.ker.toModulesι ▷ L.tensorPow (n - r) ≫ (λ_ _).hom
  let E : L.tensorPow (n - r) ⊗ₘ L.tensorPow r ≅ L.tensorPow n :=
    (L.tensorPowAddIso (n - r) r).symm ≪≫
      eqToIso (congrArg L.tensorPow (Nat.sub_add_cancel hrn))
  let α (a : σ.I) : Γ(L.tensorPow (n - r), ⊤) := μ.app ⊤ ((σ.s a).val (op ⊤))
  let β (b : B) : Γ(L.tensorPow r, ⊤) :=
    e.hom.app ⊤ (pullbackSection j (ProjectiveSpace.twistOneSection B S b))
  let v (a : σ.I) (b : B) : Γ(L.tensorPow n, ⊤) :=
    E.hom.app ⊤ (tmulSection (α a) (β b))
  let w (a : σ.I) (b : B) : Γ(N, ⊤) := pullbackΓ U.ι (L.tensorPow n) (v a b)
  change (∀ a b, pullbackΓ i (L.tensorPow n) (v a b) = 0) ∧
    (∀ x : U, ∃ a b, GeneratesAt (w a b) x) ∧ _
  have hβ (b : B) : e.hom.app _
      (pullbackSection j (ProjectiveSpace.twistOneSection B S b)) =
      (L.tensorPow r).presheaf.map (homOfLE (le_top : j ⁻¹ᵁ ⊤ ≤ ⊤)).op (β b) := by
    simp only [Scheme.Hom.preimage_top, presheaf_map_id_apply]
    rfl
  have hβgen (b : B) : generatingLocus (β b) =
      j ⁻¹ᵁ ProjectiveSpace.standardOpen B S b :=
    ProjectiveSpace.generatingLocus_eq_preimage_standardOpen e.hom hβ b
  have hvgen (a : σ.I) (b : B) (x : Y) :
      GeneratesAt (v a b) x ↔ GeneratesAt (α a) x ∧ GeneratesAt (β b) x := by
    simp only [← mem_nonvanishingLocus_iff_generatesAt, v, nonvanishing_iso,
      nonvanishing_tensor, Set.mem_inter_iff]
  have hwgen (a : σ.I) (b : B) (x : U) :
      GeneratesAt (w a b) x ↔ GeneratesAt (v a b) (U.ι x) :=
    pullback_generatesAt_iff U.ι (L.tensorPow n) (v a b) x
  have hαcover (x : Y) (hx : x ∈ U) : ∃ a, GeneratesAt (α a) x := by
    have : SheafOfModules.IsInvertible.{u, u, u} (L.tensorPow (n - r)) :=
      IsInvertible.sheafOfModules_isInvertible _
    have hepi : Epi ((restrictFunctor U.ι).map (σ.π ≫ μ)) := by
      have : IsIso ((restrictFunctor U.ι).map i.ker.toModulesι) :=
        i.ker.isIso_restrictFunctor_map_toModulesι (U := U) fun _ h ↦ h
      have := restrict_tensor_iso i.ker.toModulesι
        (L.tensorPow (n - r)) (U := U)
      have : Epi σ.π := σ.epi
      have h₁ : Epi ((restrictFunctor U.ι).map σ.π) := Functor.map_epi _ _
      dsimp only [μ]
      rw [Functor.map_comp, Functor.map_comp]
      exact epi_comp' h₁ (epi_comp' inferInstance inferInstance)
    obtain ⟨a, ha⟩ := exists_generatesAt_of_epi (σ.π ≫ μ) hx hepi
    refine ⟨a, ?_⟩
    have hσ := congrArg (fun q ↦ (q a).val (op ⊤))
      ((i.ker.toModules ⊗ₘ L.tensorPow (n - r)).freeHomEquiv.apply_symm_apply σ.s)
    change Hom.app (SheafOfModules.ιFree a ≫ σ.π) ⊤ (unitSectionsEquiv ⊤ 1) =
      (σ.s a).val (op ⊤) at hσ
    change GeneratesAt (μ.app ⊤ (Hom.app (SheafOfModules.ιFree a ≫ σ.π)
      ⊤ (unitSectionsEquiv ⊤ 1))) x at ha
    rw [hσ] at ha
    exact ha
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    apply (vanishing_range i L n (v a b)).mpr
    refine ⟨(i.ker.toModules ◁ E.hom).app ⊤
      ((α_ i.ker.toModules (L.tensorPow (n - r)) (L.tensorPow r)).hom.app ⊤
        (tmulSection ((σ.s a).val (op ⊤)) (β b))), ?_⟩
    rw [ideal_image_map, ideal_image_tensor]
  · intro x
    obtain ⟨a, ha⟩ := hαcover x.val x.property
    obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((ProjectiveSpace.iSup_standardOpen B S).ge (Set.mem_univ (j (U.ι x))))
    refine ⟨a, b, (hwgen a b x).mpr ((hvgen a b (U.ι x)).mpr ⟨ha, ?_⟩)⟩
    rw [← mem_generatingLocus, hβgen]
    exact hb
  · intro a b
    have hle : generatingLocus (w a b) ≤
        (U.ι ≫ j) ⁻¹ᵁ ProjectiveSpace.standardOpen B S b := by
      intro x hx
      have hb := ((hvgen a b _).mp ((hwgen a b x).mp hx)).2
      rw [← mem_generatingLocus, hβgen] at hb
      exact hb
    refine ⟨hle, fun c ↦ ?_⟩
    let R := j ⁻¹ᵁ ProjectiveSpace.standardOpen B S b
    have hrel : (L.tensorPow n).presheaf.map (homOfLE (le_top : R ≤ ⊤)).op (v a c) =
        j.app (ProjectiveSpace.standardOpen B S b) (ProjectiveSpace.coordRatio B S b c) •
          (L.tensorPow n).presheaf.map (homOfLE (le_top : R ≤ ⊤)).op (v a b) := by
      have hb := ProjectiveSpace.map_eq_coordRatio_smul_of_twistRestrict_iso e.hom hβ b c
      dsimp only [v]
      rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map, tmulSection_map,
        tmulSection_map, hb, tmulSection_smul, Hom.app_smul]
    have hp := pullback_relation U.ι (L.tensorPow n) (v a c) (v a b) R
      (j.app (ProjectiveSpace.standardOpen B S b) (ProjectiveSpace.coordRatio B S b c))
      hrel (generatingLocus (w a b)) hle
    rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_comp_appLE] at hp
    exact hp

end AlgebraicGeometry
