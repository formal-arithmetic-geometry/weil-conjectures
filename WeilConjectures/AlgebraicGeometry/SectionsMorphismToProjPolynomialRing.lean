/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjPolynomialTwistChart
public import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializesSupplement
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus

/-! # Morphism to polynomial Proj from generating sections

Source: literature/stacks-project/constructions.tex, Lemma 01N8
(blueprint: lem-weil-pbc-sections-morphism-to-proj-polynomial-ring).
-/

@[expose] public section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

section Construction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Scheme.Modules

variable {A : Type u} [CommRing A] {m : ℕ} {Y : Scheme.{u}} {M : Y.Modules}
  (s : Fin (m + 1) → Γ(M, ⊤)) (U : Fin (m + 1) → Y.Opens)
  (hs : ∀ k, IsFreeGenerator (M.presheaf.map (homOfLE (le_top : U k ≤ ⊤)).op (s k)))
  (g : Y ⟶ Spec (.of A))

private noncomputable def sectionRatio (k l : Fin (m + 1)) : Γ(Y, U k) :=
  (hs k).coeff (M.presheaf.map (homOfLE (le_top : U k ≤ ⊤)).op (s l))

private lemma sectionRatio_smul (k l : Fin (m + 1)) :
    sectionRatio s U hs k l • M.presheaf.map (homOfLE (le_top : U k ≤ ⊤)).op (s k) =
      M.presheaf.map (homOfLE (le_top : U k ≤ ⊤)).op (s l) :=
  (hs k).coeff_smul _

private lemma sectionRatio_self (k : Fin (m + 1)) : sectionRatio s U hs k k = 1 :=
  ((hs k).coeff_eq_iff _ 1).mpr (one_smul _ _)

private lemma sectionRatio_map_smul {W : Y.Opens} (k l : Fin (m + 1)) (h : W ≤ U k) :
    Y.presheaf.map (homOfLE h).op (sectionRatio s U hs k l) •
        M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s k) =
      M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s l) := by
  exact (presheaf_map_homOfLE_eq_smul (le_top : U k ≤ ⊤) h
    (sectionRatio_smul s U hs k l).symm).symm

private lemma sectionRatio_mul {W : Y.Opens} (k l j : Fin (m + 1))
    (hk : W ≤ U k) (hl : W ≤ U l) :
    Y.presheaf.map (homOfLE hl).op (sectionRatio s U hs l k) *
        Y.presheaf.map (homOfLE hk).op (sectionRatio s U hs k j) =
      Y.presheaf.map (homOfLE hl).op (sectionRatio s U hs l j) := by
  apply ((hs l).map hl).smul_left_injective
  simp only [presheaf_map_homOfLE_map_homOfLE]
  rw [sectionRatio_map_smul s U hs l j hl, mul_comm, mul_smul,
    sectionRatio_map_smul s U hs l k hl, sectionRatio_map_smul s U hs k j hk]

private noncomputable def localSections (k l : Fin (m + 1)) : Γ((U k).toScheme, ⊤) :=
  (U k).topIso.inv (sectionRatio s U hs k l)

private lemma span_range_localSections (k : Fin (m + 1)) :
    Ideal.span (Set.range (localSections s U hs k)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  apply Ideal.subset_span
  exact ⟨k, by simp [localSections, sectionRatio_self]⟩

private noncomputable def polynomialSectionsEval (k : Fin (m + 1)) :
    MvPolynomial (Fin (m + 1)) A →+* Γ((U k).toScheme, ⊤) :=
  MvPolynomial.eval₂Hom
    (((Scheme.ΓSpecIso (.of A)).inv ≫ ((U k).ι ≫ g).appTop).hom)
    (localSections s U hs k)

private lemma polynomialSectionsEval_irrelevant (k : Fin (m + 1)) :
    (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)).toIdeal.map
        (polynomialSectionsEval s U hs g k) = ⊤ := by
  rw [MvPolynomial.toIdeal_irrelevant_homogeneousSubmodule, Ideal.map_span,
    ← Set.range_comp]
  simpa [polynomialSectionsEval, Function.comp_def] using
    span_range_localSections s U hs k

private noncomputable def polynomialSectionsLocal (k : Fin (m + 1)) :
    (U k).toScheme ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) :=
  Proj.fromOfGlobalSections _ (polynomialSectionsEval s U hs g k)
    (polynomialSectionsEval_irrelevant s U hs g k)

private lemma polynomialSectionsLocal_compat (k l : Fin (m + 1)) :
    Y.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ polynomialSectionsLocal s U hs g k =
      Y.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫
        polynomialSectionsLocal s U hs g l := by
  classical
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A
  let ik := Y.homOfLE (inf_le_left : U k ⊓ U l ≤ U k)
  let il := Y.homOfLE (inf_le_right : U k ⊓ U l ≤ U l)
  let fk := ik.appTop.hom.comp (polynomialSectionsEval s U hs g k)
  let fl := il.appTop.hom.comp (polynomialSectionsEval s U hs g l)
  have hu : IsUnit ((U k ⊓ U l).topIso.inv
      (Y.presheaf.map (homOfLE inf_le_right).op
        (sectionRatio s U hs l k))) := by
    refine IsUnit.of_mul_eq_one ((U k ⊓ U l).topIso.inv
      (Y.presheaf.map (homOfLE inf_le_left).op
        (sectionRatio s U hs k l))) ?_
    rw [← map_mul, sectionRatio_mul s U hs k l l inf_le_left inf_le_right,
      sectionRatio_self, map_one, map_one]
  dsimp only [polynomialSectionsLocal]
  rw [Proj.comp_fromOfGlobalSections _ ik _ _
    (Proj.map_irrelevant_comp_appTop_eq_top _ ik _
      (polynomialSectionsEval_irrelevant s U hs g k)),
    Proj.comp_fromOfGlobalSections _ il _ _
      (Proj.map_irrelevant_comp_appTop_eq_top _ il _
        (polynomialSectionsEval_irrelevant s U hs g l))]
  refine Proj.fromOfGlobalSections_eq_of_unit_pow_mul 𝒜 hu.unit fk fl ?_ _ _
  intro d a ha
  have hc : il.appTop.hom.comp
      (((Scheme.ΓSpecIso (.of A)).inv ≫ ((U l).ι ≫ g).appTop).hom) =
      ik.appTop.hom.comp
        (((Scheme.ΓSpecIso (.of A)).inv ≫ ((U k).ι ≫ g).appTop).hom) := by
    change (((Scheme.ΓSpecIso (.of A)).inv ≫
      (((U l).ι ≫ g).appTop ≫ il.appTop)).hom) = _
    rw [← Scheme.Hom.comp_appTop, show il ≫ (U l).ι ≫ g = ik ≫ (U k).ι ≫ g by
      simp [ik, il]]
    rfl
  have hv (j : Fin (m + 1)) :
      il.appTop (localSections s U hs l j) =
        (hu.unit : Γ((U k ⊓ U l).toScheme, ⊤)) *
          ik.appTop (localSections s U hs k j) := by
    simp only [ik, il, localSections, Scheme.homOfLE_appTop_topIso_inv,
      IsUnit.unit_spec, ← map_mul]
    rw [sectionRatio_mul s U hs k l j inf_le_left inf_le_right]
  dsimp only [fk, fl, polynomialSectionsEval]
  rw [MvPolynomial.comp_eval₂Hom, MvPolynomial.comp_eval₂Hom, hc]
  simp_rw [hv]
  exact ((MvPolynomial.mem_homogeneousSubmodule _ _).mp ha).eval₂Hom_const_mul _ _ _

variable (hU : ⨆ k, U k = ⊤)

private noncomputable def polynomialSectionsHom :
    Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) :=
  Scheme.Opens.glueMorphismsOfTop U hU (polynomialSectionsLocal s U hs g)
    (polynomialSectionsLocal_compat s U hs g)

@[reassoc]
private lemma polynomialSectionsHom_ι (k : Fin (m + 1)) :
    (U k).ι ≫ polynomialSectionsHom s U hs g hU = polynomialSectionsLocal s U hs g k :=
  Scheme.Opens.ι_glueMorphismsOfTop ..

private lemma polynomialSectionsHom_preimage (k : Fin (m + 1)) :
    polynomialSectionsHom s U hs g hU ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
        (MvPolynomial.X k) = generatingLocus (s k) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hU.ge (show y ∈ (⊤ : Y.Opens) from trivial))
    have hx : (⟨y, hl⟩ : U l) ∈
        polynomialSectionsLocal s U hs g l ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
            (MvPolynomial.X k) := by
      rw [← polynomialSectionsHom_ι s U hs g hU l]
      exact hy
    rw [polynomialSectionsLocal, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _
      Nat.one_pos (MvPolynomial.isHomogeneous_X A k)] at hx
    simp only [polynomialSectionsEval, MvPolynomial.eval₂Hom_X'] at hx
    have hx' : y ∈ Y.basicOpen (sectionRatio s U hs l k) := by
      rw [← (U l).ι_image_basicOpen_topIso_inv]
      exact ⟨⟨y, hl⟩, hx, rfl⟩
    exact generatesAt_of_mem_basicOpen (hs l) (sectionRatio_smul s U hs l k).symm hx'
  · intro y hy
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hU.ge (show y ∈ (⊤ : Y.Opens) from trivial))
    have hx : y ∈ Y.basicOpen (sectionRatio s U hs l k) :=
      mem_basicOpen_of_generatesAt (hs l) (sectionRatio_smul s U hs l k).symm hl hy
    rw [← (U l).ι_image_basicOpen_topIso_inv] at hx
    obtain ⟨z, hz, hzy⟩ := hx
    have hzy' : z = (⟨y, hl⟩ : U l) := Subtype.ext hzy
    subst z
    have hz' : (⟨y, hl⟩ : U l) ∈
        polynomialSectionsLocal s U hs g l ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
            (MvPolynomial.X k) := by
      rw [polynomialSectionsLocal, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _
        Nat.one_pos (MvPolynomial.isHomogeneous_X A k)]
      simp only [polynomialSectionsEval, MvPolynomial.eval₂Hom_X', localSections]
      convert hz using 1
      rfl
    rw [← polynomialSectionsHom_ι s U hs g hU l] at hz'
    exact hz'

private lemma polynomialSectionsHom_le_preimage (k : Fin (m + 1)) :
    U k ≤ polynomialSectionsHom s U hs g hU ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
        (MvPolynomial.X k) := by
  rw [polynomialSectionsHom_preimage]
  exact fun _ hx ↦ ⟨U k, hx, hs k⟩

private lemma polynomialSectionsHom_ratio (k l : Fin (m + 1)) :
    (polynomialSectionsHom s U hs g hU).appLE
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
        (MvPolynomial.X k)) (U k) (polynomialSectionsHom_le_preimage s U hs g hU k)
      (Proj.awayToSection _ (MvPolynomial.X k) (MvPolynomial.awayXRatio A k l)) =
        sectionRatio s U hs k l := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A
  obtain ⟨q, hq, hq'⟩ := Proj.exists_comp_awayι_eq_fromOfGlobalSections 𝒜
    (polynomialSectionsEval s U hs g k) (polynomialSectionsEval_irrelevant s U hs g k)
    Nat.one_pos (MvPolynomial.isHomogeneous_X A k)
    (by simp [polynomialSectionsEval, localSections, sectionRatio_self])
  have ht : (U k).topIso.inv
      ((polynomialSectionsHom s U hs g hU).appLE
        (Proj.basicOpen 𝒜 (MvPolynomial.X k)) (U k)
        (polynomialSectionsHom_le_preimage s U hs g hU k)
        (Proj.awayToSection _ (MvPolynomial.X k) (MvPolynomial.awayXRatio A k l))) =
      localSections s U hs k l := by
    have ht := Proj.comp_awayι_appLE_awayToSection 𝒜
      (MvPolynomial.isHomogeneous_X A k) Nat.one_pos q
      (by rw [← Proj.opensRange_awayι 𝒜 _ (MvPolynomial.isHomogeneous_X A k) Nat.one_pos];
          intro x _; exact ⟨q x, rfl⟩)
      (MvPolynomial.awayXRatio A k l)
    have hcomp : (U k).ι ≫ polynomialSectionsHom s U hs g hU =
        q ≫ Proj.awayι 𝒜 (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X A k)
          Nat.one_pos := (polynomialSectionsHom_ι s U hs g hU k).trans hq.symm
    have htop (f : Y ⟶ Proj 𝒜) (V : (Proj 𝒜).Opens) (x : Γ(Proj 𝒜, V))
        (e : U k ≤ f ⁻¹ᵁ V) :
        (U k).topIso.inv (f.appLE V (U k) e x) =
          ((U k).ι ≫ f).appLE V ⊤ (fun y _ ↦ e y.2) x := by
      rw [Scheme.Hom.comp_appLE, Scheme.Opens.ι_appLE]
      simp only [Scheme.Hom.appLE, Scheme.Opens.topIso_inv]
      rw [← ConcreteCategory.comp_apply, Category.assoc, ← Functor.map_comp]
      rfl
    rw [htop]
    have hh : ∀ (f f' : (U k).toScheme ⟶ Proj 𝒜) (h : f = f') (e),
        f.appLE (Proj.basicOpen 𝒜 (MvPolynomial.X k)) ⊤ e =
          f'.appLE (Proj.basicOpen 𝒜 (MvPolynomial.X k)) ⊤ (h ▸ e) := by
      rintro f f' rfl e
      rfl
    rw [hh _ _ hcomp]
    exact ht.trans ((hq' 1 (MvPolynomial.X l) (MvPolynomial.isHomogeneous_X A l)).trans
      (MvPolynomial.eval₂Hom_X' _ _ l))
  apply (ConcreteCategory.bijective_of_isIso (U k).topIso.inv).1
  exact ht

private noncomputable def polynomialProjBase :
    Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) ⟶ Spec (.of A) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom
    (MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin (m + 1)) A).toRingHom)

private lemma polynomialProjBase_chart (k : Fin (m + 1)) :
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) (MvPolynomial.X k)
        (MvPolynomial.isHomogeneous_X A k) Nat.one_pos ≫ polynomialProjBase (A := A) =
      Spec.map (CommRingCat.ofHom (algebraMap A
        (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
          (MvPolynomial.X k)))) := by
  dsimp [polynomialProjBase]
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  congr 1

private lemma polynomialSectionsHom_over :
    polynomialSectionsHom s U hs g hU ≫ polynomialProjBase (A := A) = g := by
  apply Scheme.Opens.hom_ext_of_iSup_eq_top U hU
  intro k
  rw [polynomialSectionsHom_ι_assoc]
  dsimp only [polynomialSectionsLocal, polynomialProjBase]
  rw [Proj.fromOfGlobalSections_toSpecZero_assoc, ← Spec.map_comp]
  have he : CommRingCat.ofHom
      (MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin (m + 1)) A).toRingHom ≫
        CommRingCat.ofHom
          ((polynomialSectionsEval s U hs g k).comp (algebraMap _ _)) =
      (Scheme.ΓSpecIso (.of A)).inv ≫ ((U k).ι ≫ g).appTop := by
    ext a
    simp [polynomialSectionsEval]
  rw [he, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
  simp

private noncomputable def polynomialPullbackBasis (k : Fin (m + 1)) :
    Γ((pullback (polynomialSectionsHom s U hs g hU)).obj
      (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) 1), U k) :=
  ((pullback (polynomialSectionsHom s U hs g hU)).obj
    (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) 1)).presheaf.map
      (homOfLE (polynomialSectionsHom_le_preimage s U hs g hU k)).op
      (pullbackSection (polynomialSectionsHom s U hs g hU)
        (Proj.twistPowSection 1 (MvPolynomial.isHomogeneous_X A k)))

private lemma polynomialPullbackBasis_free (k : Fin (m + 1)) :
    IsFreeGenerator (polynomialPullbackBasis s U hs g hU k) := by
  exact ((Proj.isFreeGenerator_twistPowSection 1
    (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
    (MvPolynomial.isHomogeneous_X A k)).pullback_unit_app (polynomialSectionsHom s U hs g hU)).map
      (polynomialSectionsHom_le_preimage s U hs g hU k)

private lemma polynomialPullbackBasis_transition (k l : Fin (m + 1))
    (W : Y.Opens) (hk : W ≤ U k) (hl : W ≤ U l) :
    ((pullback (polynomialSectionsHom s U hs g hU)).obj
      (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) 1)).presheaf.map
        (homOfLE hl).op (polynomialPullbackBasis s U hs g hU l) =
      Y.presheaf.map (homOfLE hk).op (sectionRatio s U hs k l) •
        ((pullback (polynomialSectionsHom s U hs g hU)).obj
          (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) 1)).presheaf.map
            (homOfLE hk).op (polynomialPullbackBasis s U hs g hU k) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A
  let j := polynomialSectionsHom s U hs g hU
  let N := (pullback j).obj (Proj.twist 𝒜 1)
  let B (i : Fin (m + 1)) := Proj.basicOpen 𝒜 (MvPolynomial.X i)
  have hW : W ≤ j ⁻¹ᵁ (B k ⊓ B l) :=
    le_inf (hk.trans (polynomialSectionsHom_le_preimage s U hs g hU k))
      (hl.trans (polynomialSectionsHom_le_preimage s U hs g hU l))
  have ht := (proj_polynomial_twist_chart A m).2.2.2.2.1 k l
  have hp := congrArg (pullbackSection j) ht
  rw [pullbackSection_smul, pullbackSection_map, pullbackSection_map] at hp
  have hp' := congrArg (N.presheaf.map (homOfLE hW).op) hp
  change N.presheaf.map (homOfLE hW).op
      (N.presheaf.map (homOfLE (j.preimage_mono inf_le_right)).op
        (pullbackSection j (Proj.twistPowSection 1 (MvPolynomial.isHomogeneous_X A l)))) =
    N.presheaf.map (homOfLE hW).op
      (j.app (B k ⊓ B l)
          ((Proj 𝒜).presheaf.map (homOfLE inf_le_left).op
            (Proj.awayToSection 𝒜 (MvPolynomial.X k) (MvPolynomial.awayXRatio A k l))) •
        N.presheaf.map (homOfLE (j.preimage_mono inf_le_left)).op
          (pullbackSection j (Proj.twistPowSection 1 (MvPolynomial.isHomogeneous_X A k))))
      at hp'
  dsimp only [N, j, 𝒜, B] at hp'
  simp only [map_smul, Scheme.Modules.presheaf_map_homOfLE_map_homOfLE] at hp'
  dsimp only [polynomialPullbackBasis]
  simp only [presheaf_map_homOfLE_map_homOfLE]
  refine hp'.trans ?_
  congr 1
  rw [← polynomialSectionsHom_ratio s U hs g hU k l]
  change Y.presheaf.map (homOfLE hW).op
      (j.app (B k ⊓ B l)
        ((Proj 𝒜).presheaf.map (homOfLE inf_le_left).op
          (Proj.awayToSection 𝒜 (MvPolynomial.X k) (MvPolynomial.awayXRatio A k l)))) =
    Y.presheaf.map (homOfLE hk).op
      (j.appLE (B k) (U k) (polynomialSectionsHom_le_preimage s U hs g hU k)
        (Proj.awayToSection 𝒜 (MvPolynomial.X k) (MvPolynomial.awayXRatio A k l)))
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_map, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  exact (congrArg (fun f : Γ(Proj 𝒜, B k) ⟶ Γ(Y, W) ↦
    f (Proj.awayToSection 𝒜 (MvPolynomial.X k) (MvPolynomial.awayXRatio A k l)))
      (j.appLE_map (polynomialSectionsHom_le_preimage s U hs g hU k)
        (homOfLE hk).op)).symm

private lemma polynomialPullbackBasis_compat (k l : Fin (m + 1))
    (W : Y.Opens) (hk : W ≤ U k) (hl : W ≤ U l) (a b : Γ(Y, W))
    (hab : a • ((pullback (polynomialSectionsHom s U hs g hU)).obj
        (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) 1)).presheaf.map
          (homOfLE hk).op (polynomialPullbackBasis s U hs g hU k) =
      b • ((pullback (polynomialSectionsHom s U hs g hU)).obj
        (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) 1)).presheaf.map
          (homOfLE hl).op (polynomialPullbackBasis s U hs g hU l)) :
    a • M.presheaf.map (homOfLE hk).op
        (M.presheaf.map (homOfLE (le_top : U k ≤ ⊤)).op (s k)) =
      b • M.presheaf.map (homOfLE hl).op
        (M.presheaf.map (homOfLE (le_top : U l ≤ ⊤)).op (s l)) := by
  rw [polynomialPullbackBasis_transition s U hs g hU l k W hl hk, smul_smul] at hab
  have hc := ((polynomialPullbackBasis_free s U hs g hU l).map hl).smul_left_injective hab
  simp only [presheaf_map_homOfLE_map_homOfLE]
  rw [← hc, mul_smul, sectionRatio_map_smul s U hs l k hl]

private noncomputable def polynomialSectionsModuleHom :
    (pullback (polynomialSectionsHom s U hs g hU)).obj
      (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) 1) ⟶ M :=
  glueHom hU (polynomialPullbackBasis_free s U hs g hU)
    (polynomialPullbackBasis_compat s U hs g hU)

private lemma polynomialSectionsModuleHom_basis (k : Fin (m + 1)) :
    (polynomialSectionsModuleHom s U hs g hU).app (U k)
      (polynomialPullbackBasis s U hs g hU k) =
        M.presheaf.map (homOfLE (le_top : U k ≤ ⊤)).op (s k) := by
  have hg := isGlueValue_glueHom_app hU (polynomialPullbackBasis_free s U hs g hU)
    (polynomialPullbackBasis_compat s U hs g hU) (polynomialPullbackBasis s U hs g hU k)
  have ht := hg k (U k) le_rfl le_rfl 1 (by rw [one_smul])
  simp only [Scheme.Modules.presheaf_map_id_apply, one_smul] at ht
  unfold polynomialSectionsModuleHom
  exact ht

private lemma polynomialSectionsModuleHom_isIso :
    IsIso (polynomialSectionsModuleHom s U hs g hU) := by
  apply Scheme.Modules.Hom.isIso_of_forall_bijective_app
  intro y
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (hU.ge (show y ∈ (⊤ : Y.Opens) from trivial))
  refine ⟨U k, hk, fun W hW ↦ ?_⟩
  refine (Function.Bijective.of_comp_iff _
    (polynomialPullbackBasis_free s U hs g hU k W hW)).1 ?_
  have ht := (polynomialSectionsModuleHom_basis s U hs g hU k).symm ▸ hs k
  convert ht W hW using 1
  ext r
  simp only [Function.comp_apply, Scheme.Modules.Hom.app_smul,
    Scheme.Modules.Hom.app_presheaf_map]

private lemma ratio_relation_transport {X Z : Scheme.{u}} (f : X ⟶ Z)
    (N : X.Modules) (V : Z.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ V)
    (hW : W = f ⁻¹ᵁ V) (r : Γ(Z, V)) (t t' : Γ(N, ⊤))
    (hr : N.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t' =
      f.appLE V W h r • N.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t) :
    N.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)).op t' =
      f.app V r • N.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)).op t := by
  subst W
  simpa only [Scheme.Hom.appLE, CommRingCat.comp_apply,
    Scheme.presheaf_map_id_apply] using hr

private lemma module_basis_transport {X Z : Scheme.{u}} (f : X ⟶ Z)
    (N : Z.Modules) (M' : X.Modules) (φ : (pullback f).obj N ⟶ M')
    (V : Z.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ V) (hW : W = f ⁻¹ᵁ V)
    (e' : Γ(N, V)) (t : Γ(M', ⊤))
    (hb : φ.app W (((pullback f).obj N).presheaf.map (homOfLE h).op
      (pullbackSection f e')) = M'.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t) :
    φ.app (f ⁻¹ᵁ V) (pullbackSection f e') =
      M'.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)).op t := by
  subst W
  simpa only [Scheme.Modules.presheaf_map_id_apply] using hb

end Construction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Global sections of an invertible module which generate it define a morphism to Proj,
with the twisting module pulled back to the given module.
Source: Constructions, Lemma 01N8 (specialized to `A[x₀,…,xₘ]`).
(blueprint: lem-weil-pbc-sections-morphism-to-proj-polynomial-ring).

Proof:
1. On the generating locus of `s_k`, its restriction is a free generator. The
   nonvanishing/generation equivalence identifies these opens with the loci in the
   hypothesis. Use the free-generator coefficient map to define `s_l/s_k` and prove
   the reciprocal and cocycle identities by cancellation.
2. Evaluate polynomials in these ratios, using `g` on coefficients. Since `s_k/s_k = 1`,
   the irrelevant ideal generates the unit ideal. `Proj.fromOfGlobalSections` gives
   the local morphisms. The ratio cocycle makes their evaluations differ on overlaps
   by a unit raised to the homogeneous degree, so the local morphisms agree.
3. Glue the local morphisms. The basic-open formula for `fromOfGlobalSections` and
   the free-generator criterion identify the inverse image of each chart with the
   generating locus of `s_k`. The local fraction formula proves the ratio clause.
4. Pull back each standard twisting-module basis. It remains a free generator, and
   its transition is the pullback of `e_l = (x_l/x_k)e_k`. The ratio formula makes the
   assignments of these bases to `s_k` compatible. `Scheme.Modules.glueHom` glues
   them; the resulting map is locally bijective, hence an isomorphism.
5. Compare the ordinary module pullback with the stated tensor pullback by uniqueness
   of left adjoints. Compatibility of their adjunction units gives exactly the
   asserted basis-image formula for the chosen tensor-pullback adjunction.
6. Define `q` using `Proj.toSpecZero` and the degree-zero identification with `A`.
   Its chart maps are the constant-ring maps. Naturality of `toSpecΓ` shows that
   `j ≫ q` and `g` agree on every generating open, hence globally.

The chart characterization pins down q uniquely; together with j ≫ q = g it also
expresses the A-algebra requirement in clause (iii). The unit of the canonical tensor
pullback adjunction sends e_k to its pullback section, so the last equation is clause (iv).
-/
theorem sections_morphism_to_proj_polynomial_ring (A : Type u) [CommRing A] (m : ℕ)
    (Y : Scheme.{u}) (g : Y ⟶ Spec (.of A)) (M : Y.Modules) [M.IsInvertible]
    (s : Fin (m + 1) → Γ(M, ⊤))
    (hcover : ((⊤ : Y.Opens) : Set Y) =
      ⋃ k : Fin (m + 1), Scheme.Modules.nonvanishingLocus M (s k)) :
    ∃ j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A),
      ∃ α : Scheme.Modules.tensorPullbackObj j
          (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) 1) ≅ M,
      ∃ q : Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) ⟶ Spec (.of A),
      (∀ k : Fin (m + 1),
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) (MvPolynomial.X k)
            (MvPolynomial.isHomogeneous_X A k) Nat.one_pos ≫ q =
          Spec.map (CommRingCat.ofHom (algebraMap A
            (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
              (MvPolynomial.X k))))) ∧
      j ≫ q = g ∧
      (∀ k : Fin (m + 1),
        (j ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
          (MvPolynomial.X k) : Set Y) = Scheme.Modules.nonvanishingLocus M (s k)) ∧
      (∀ k l : Fin (m + 1),
        ∃! a : Γ(Y, j ⁻¹ᵁ Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) (MvPolynomial.X k)),
          a = (j.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
            (MvPolynomial.X k))).hom
            ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
              (MvPolynomial.X k)).hom (MvPolynomial.awayXRatio A k l)) ∧
          (M.presheaf.map (homOfLE (le_top :
            (j ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
              (MvPolynomial.X k)) ≤ ⊤)).op (s l)) =
            a • M.presheaf.map (homOfLE (le_top :
              (j ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
                (MvPolynomial.X k)) ≤ ⊤)).op (s k)) ∧
      (∀ k : Fin (m + 1),
        α.hom.val.app (op (j ⁻¹ᵁ Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) (MvPolynomial.X k)))
          (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)).unit.app
            (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) 1)).val.app
              (op (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
                (MvPolynomial.X k)))
              (Proj.twistPowSection 1 (MvPolynomial.isHomogeneous_X A k))) =
          M.presheaf.map (homOfLE (le_top :
            (j ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A)
              (MvPolynomial.X k)) ≤ ⊤)).op (s k)) := by
  classical
  let U (k : Fin (m + 1)) := Scheme.Modules.generatingLocus (s k)
  have hs (k : Fin (m + 1)) : Scheme.Modules.IsFreeGenerator
      (M.presheaf.map (homOfLE (le_top : U k ≤ ⊤)).op (s k)) :=
    Scheme.Modules.isFreeGenerator_generatingLocus (s k)
  have hU : ⨆ k, U k = ⊤ := by
    apply top_unique
    intro y hy
    have hy' : y ∈ ⋃ k : Fin (m + 1), Scheme.Modules.nonvanishingLocus M (s k) :=
      hcover ▸ hy
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy'
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨k, (Scheme.Modules.mem_nonvanishingLocus_iff_generatesAt M (s k) y).mp hk⟩
  let j := polynomialSectionsHom s U hs g hU
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A
  let B (k : Fin (m + 1)) := Proj.basicOpen 𝒜 (MvPolynomial.X k)
  let L := Proj.twist 𝒜 1
  have hjU (k : Fin (m + 1)) : j ⁻¹ᵁ B k = U k :=
    polynomialSectionsHom_preimage s U hs g hU k
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction j)
  let e := (adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction j)).app L
  have hε : IsIso (polynomialSectionsModuleHom s U hs g hU) :=
    polynomialSectionsModuleHom_isIso s U hs g hU
  let α : Scheme.Modules.tensorPullbackObj j L ≅ M :=
    (show Scheme.Modules.tensorPullbackObj j L ≅ (Scheme.Modules.pullback j).obj L from e) ≪≫
      asIso (polynomialSectionsModuleHom s U hs g hU)
  refine ⟨j, α, polynomialProjBase (A := A), polynomialProjBase_chart,
    polynomialSectionsHom_over s U hs g hU, ?_, ?_, ?_⟩
  · intro k
    rw [hjU]
    exact Set.ext fun y ↦
      (Scheme.Modules.mem_nonvanishingLocus_iff_generatesAt M (s k) y).symm
  · intro k l
    let r := Proj.awayToSection 𝒜 (MvPolynomial.X k) (MvPolynomial.awayXRatio A k l)
    refine ⟨(j.app (B k)).hom r, ⟨rfl, ?_⟩, fun a ha ↦ ha.1⟩
    have hr := (sectionRatio_smul s U hs k l).symm
    rw [← polynomialSectionsHom_ratio s U hs g hU k l] at hr
    exact ratio_relation_transport j M (B k) (U k)
      (polynomialSectionsHom_le_preimage s U hs g hU k) (hjU k).symm r (s k) (s l) hr
  · intro k
    have he : e.hom.app (j ⁻¹ᵁ B k)
        ((adj.unit.app L).val.app (op (B k))
          (Proj.twistPowSection 1 (MvPolynomial.isHomogeneous_X A k))) =
      Scheme.Modules.pullbackSection j
        (Proj.twistPowSection 1 (MvPolynomial.isHomogeneous_X A k)) := by
      exact congrArg (fun t ↦ t.val.app (op (B k))
        (Proj.twistPowSection 1 (MvPolynomial.isHomogeneous_X A k)))
        (adj.unit_leftAdjointUniq_hom_app
          (Scheme.Modules.pullbackPushforwardAdjunction j) L)
    change (polynomialSectionsModuleHom s U hs g hU).app (j ⁻¹ᵁ B k)
      (e.hom.app (j ⁻¹ᵁ B k) _) = _
    simp only [Functor.leftUnitor_inv_app]
    change (polynomialSectionsModuleHom s U hs g hU).app (j ⁻¹ᵁ B k)
      (e.hom.app (j ⁻¹ᵁ B k)
        ((adj.unit.app L).val.app (op (B k))
          (Proj.twistPowSection 1 (MvPolynomial.isHomogeneous_X A k)))) = _
    rw [he]
    have hb := polynomialSectionsModuleHom_basis s U hs g hU k
    dsimp only [polynomialPullbackBasis] at hb
    exact module_basis_transport j L M (polynomialSectionsModuleHom s U hs g hU)
      (B k) (U k) (polynomialSectionsHom_le_preimage s U hs g hU k) (hjU k).symm
      (Proj.twistPowSection 1 (MvPolynomial.isHomogeneous_X A k)) (s k) hb

end AlgebraicGeometry
