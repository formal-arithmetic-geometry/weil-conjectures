/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.CompleteLinearSystemClosed
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
import WeilConjectures.DeligneLaumon.BertiniProductCoordinates

/-!
# The product-of-sections immersion criterion

The geometric chart argument in Stacks Project, Varieties, Tag 0FD5.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules

private lemma appLE_eq_of_eq {X Z : Scheme.{u}} {f g : X ⟶ Z} (h : f = g)
    (U V e) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

private lemma ratio_factor {S X P : Scheme.{u}} [IsAffine S] {B : Type u}
    (g : P ⟶ S) (f : X ⟶ P) (j : X ⟶ ℙ(B; S)) (Q : P.Opens)
    (a : B → Γ(P, Q)) (b : B)
    (hle : f ⁻¹ᵁ P.basicOpen (a b) ≤ j ⁻¹ᵁ ProjectiveSpace.standardOpen B S b)
    (hbase : j ≫ ℙ(B; S) ↘ S = f ≫ g)
    (hrel : ∀ c,
      j.appLE (ProjectiveSpace.standardOpen B S b) (f ⁻¹ᵁ P.basicOpen (a b)) hle
          (ProjectiveSpace.coordRatio B S b c) *
        f.appLE Q (f ⁻¹ᵁ P.basicOpen (a b)) (f.preimage_mono (P.basicOpen_le _)) (a b) =
      f.appLE Q (f ⁻¹ᵁ P.basicOpen (a b)) (f.preimage_mono (P.basicOpen_le _)) (a c)) :
    ∃ h : (P.basicOpen (a b)).toScheme ⟶ ℙ(B; S),
      f.resLE (P.basicOpen (a b)) (f ⁻¹ᵁ P.basicOpen (a b)) le_rfl ≫ h =
        (f ⁻¹ᵁ P.basicOpen (a b)).ι ≫ j := by
  classical
  let W := P.basicOpen (a b)
  let V := f ⁻¹ᵁ W
  let F := f.resLE W V le_rfl
  let z (c : B) : Γ(W, ⊤) :=
    W.topIso.inv (P.presheaf.map (homOfLE (P.basicOpen_le (a b))).op (a c))
  have hu : IsUnit (z b) :=
    (P.toRingedSpace.isUnit_res_basicOpen (a b)).map W.topIso.inv.hom
  let d (c : B) : Γ(W, ⊤) := (↑hu.unit⁻¹ : Γ(W, ⊤)) * z c
  have hdb : d b = 1 := by
    dsimp only [d]
    calc
      _ = (↑hu.unit⁻¹ : Γ(W, ⊤)) * ↑hu.unit :=
        congrArg (fun t : Γ(W, ⊤) ↦ (↑hu.unit⁻¹ : Γ(W, ⊤)) * t) hu.unit_spec.symm
      _ = 1 := Units.inv_mul hu.unit
  have hd : Ideal.span (Set.range d) = ⊤ :=
    (Ideal.eq_top_iff_one _).mpr (hdb ▸ Ideal.subset_span (Set.mem_range_self b))
  let h := ProjectiveSpace.homOfSections (W.ι ≫ g) d hd
  have hhb : h ⁻¹ᵁ ProjectiveSpace.standardOpen B S b = ⊤ := by
    rw [ProjectiveSpace.homOfSections_preimage_standardOpen, hdb]
    exact W.toScheme.basicOpen_one
  have hFb : (F ≫ h) ⁻¹ᵁ ProjectiveSpace.standardOpen B S b = ⊤ := by
    rw [Scheme.Hom.comp_preimage, hhb, Scheme.Hom.preimage_top]
  have hjb : (V.ι ≫ j) ⁻¹ᵁ ProjectiveSpace.standardOpen B S b = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ hle x.2
  have hz (c : B) : F.appTop (z c) = V.topIso.inv
      (f.appLE Q V (f.preimage_mono (P.basicOpen_le (a b))) (a c)) := by
    dsimp only [F, z]
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    congr 1
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  refine ⟨h, ?_⟩
  apply ProjectiveSpace.hom_ext_of_preimage_standardOpen_eq_top b hFb hjb
  · dsimp only [h]
    rw [Category.assoc, ProjectiveSpace.homOfSections_over,
      ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, ← hbase, Category.assoc]
  · intro c
    have eh (e) : (F ≫ h).appLE (ProjectiveSpace.standardOpen B S b) ⊤ e
        (ProjectiveSpace.coordRatio B S b c) = F.appTop (d c) := by
      erw [← Scheme.Hom.appLE_comp_appLE F h _ ⊤ ⊤ hhb.ge le_top,
        CommRingCat.comp_apply]
      rw [ProjectiveSpace.homOfSections_appLE_coordRatio (W.ι ≫ g) d hd hdb]
      simp only [Scheme.Hom.appLE, CommRingCat.comp_apply]
      exact Scheme.presheaf_map_id_apply _ _
    have ej (e) : (V.ι ≫ j).appLE (ProjectiveSpace.standardOpen B S b) ⊤ e
        (ProjectiveSpace.coordRatio B S b c) = V.topIso.inv
          (j.appLE (ProjectiveSpace.standardOpen B S b) V hle
            (ProjectiveSpace.coordRatio B S b c)) := by
      erw [← Scheme.Hom.appLE_comp_appLE V.ι j _ V ⊤ hle V.ι_preimage_self.ge,
        CommRingCat.comp_apply, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
      rfl
    rw [eh, ej]
    have heq := congrArg V.topIso.inv (hrel c)
    rw [map_mul] at heq
    rw [← hz, ← hz] at heq
    have hdrel : d c * z b = z c := by
      calc
        _ = d b * z c := by dsimp only [d]; ring
        _ = z c := by rw [hdb, one_mul]
    apply (hu.map F.appTop.hom).mul_right_cancel
    rw [← map_mul, hdrel]
    exact heq.symm

private lemma coordinate_chart_data {I : Type u} [Finite I] {X S : Scheme.{u}}
    (g : X ⟶ S) (N : X.Modules) [N.IsInvertible]
    (s : I → N.sections) (hs : Epi (N.freeHomEquiv.symm s)) :
    let f := ProjectiveSpace.homOfGeneratingSections I g N s hs
    (∀ q, generatingLocus ((s q).val (op ⊤)) =
      f ⁻¹ᵁ ProjectiveSpace.standardOpen I S q) ∧
    (∀ q, IsFreeGenerator (N.presheaf.map (homOfLE
      (le_top : f ⁻¹ᵁ ProjectiveSpace.standardOpen I S q ≤ ⊤)).op ((s q).val (op ⊤)))) ∧
    ∀ q l, N.presheaf.map (homOfLE
      (le_top : f ⁻¹ᵁ ProjectiveSpace.standardOpen I S q ≤ ⊤)).op ((s l).val (op ⊤)) =
        f.app (ProjectiveSpace.standardOpen I S q) (ProjectiveSpace.coordRatio I S q l) •
          N.presheaf.map (homOfLE
            (le_top : f ⁻¹ᵁ ProjectiveSpace.standardOpen I S q ≤ ⊤)).op ((s q).val (op ⊤)) := by
  obtain ⟨ε, hε⟩ := generatingSections_pair g N s hs
  refine ⟨?_, ?_, ?_⟩
  · exact ProjectiveSpace.generatingLocus_eq_preimage_standardOpen ε.hom hε
  · exact ProjectiveSpace.isFreeGenerator_of_twistRestrict_iso ε.hom hε
  · exact ProjectiveSpace.map_eq_coordRatio_smul_of_twistRestrict_iso ε.hom hε

private lemma appLE_eq_map_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) :
    f.appLE U V e x = X.presheaf.map (homOfLE e).op (f.app U x) := by
  rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

private theorem immersion_of_coordinate_products
    {X S : Scheme.{u}} [IsAffine S] (g : X ⟶ S)
    (N : X.Modules) [N.IsInvertible] {I : Type u} [Finite I] [Fintype I]
    (s : I → N.sections) (hs : Epi (N.freeHomEquiv.symm s))
    {A B : Type u} (j : X ⟶ ℙ(B; S)) [IsImmersion j]
    (hj : j ≫ ℙ(B; S) ↘ S = g) (w : A → B → Γ(N, ⊤))
    (c : A → B → I → Γ(S, ⊤))
    (hsum : ∀ a b, w a b = ∑ q, g.appTop (c a b q) • (show Γ(N, ⊤) from (s q).val (op ⊤)))
    (hcover : ∀ x : X, ∃ a b, GeneratesAt (w a b) x)
    (hrelations : ∀ a b, ∃ hle : generatingLocus (w a b) ≤
        j ⁻¹ᵁ ProjectiveSpace.standardOpen B S b,
      ∀ d, N.presheaf.map (homOfLE (le_top : generatingLocus (w a b) ≤ ⊤)).op (w a d) =
        j.appLE (ProjectiveSpace.standardOpen B S b) (generatingLocus (w a b)) hle
          (ProjectiveSpace.coordRatio B S b d) •
            N.presheaf.map (homOfLE
              (le_top : generatingLocus (w a b) ≤ ⊤)).op (w a b)) :
    IsImmersion (ProjectiveSpace.homOfGeneratingSections I g N s hs) := by
  classical
  let f := ProjectiveSpace.homOfGeneratingSections I g N s hs
  have hf : f ≫ ℙ(I; S) ↘ S = g :=
    (ProjectiveSpace.homOfGeneratingSections_spec I g N s hs).1
  obtain ⟨_, hgen, hcoords⟩ := coordinate_chart_data g N s hs
  have hlinear (a : A) (q : I) (b : B) :
      N.presheaf.map (homOfLE
        (le_top : f ⁻¹ᵁ ProjectiveSpace.standardOpen I S q ≤ ⊤)).op (w a b) =
      f.app (ProjectiveSpace.standardOpen I S q) (ProjectiveSpace.linearRatio (c a) q b) •
        N.presheaf.map (homOfLE
          (le_top : f ⁻¹ᵁ ProjectiveSpace.standardOpen I S q ≤ ⊤)).op ((s q).val (op ⊤)) := by
    rw [hsum, map_sum, ProjectiveSpace.linearRatio, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [Scheme.Modules.map_smul, hcoords q l, smul_smul, map_mul]
    congr 2
    conv_rhs => rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply]
    erw [Scheme.Hom.appLE_comp_appLE]
    rw [appLE_eq_of_eq hf]
    exact (appLE_eq_map_app g ⊤ _ _ _).symm
  apply IsZariskiLocalAtTarget.of_forall_source_exists_preimage (P := @IsImmersion) f
  intro x
  obtain ⟨a, b, hx⟩ := hcover x
  obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((ProjectiveSpace.iSup_standardOpen I S).ge (Set.mem_univ (f x)))
  let W := (ℙ(I; S)).basicOpen (ProjectiveSpace.linearRatio (c a) q b)
  let V := f ⁻¹ᵁ W
  have hVq : V ≤ f ⁻¹ᵁ ProjectiveSpace.standardOpen I S q :=
    f.preimage_mono ((ℙ(I; S)).basicOpen_le _)
  have hVw : V ≤ generatingLocus (w a b) := by
    intro y hy
    apply generatesAt_of_mem_basicOpen (hgen q) (hlinear a q b)
    change y ∈ f ⁻¹ᵁ W at hy
    dsimp only [W] at hy
    rwa [Scheme.preimage_basicOpen] at hy
  obtain ⟨hle, hrel⟩ := hrelations a b
  have hVj : V ≤ j ⁻¹ᵁ ProjectiveSpace.standardOpen B S b := hVw.trans hle
  have hlinV (d : B) :
      N.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (w a d) =
        f.appLE (ProjectiveSpace.standardOpen I S q) V hVq
            (ProjectiveSpace.linearRatio (c a) q d) •
          N.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ((s q).val (op ⊤)) := by
    have h := congrArg (N.presheaf.map (homOfLE hVq).op) (hlinear a q d)
    rw [Scheme.Modules.map_smul, presheaf_map_homOfLE_map_homOfLE,
      presheaf_map_homOfLE_map_homOfLE] at h
    exact h
  have hprodV (d : B) :
      N.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (w a d) =
        j.appLE (ProjectiveSpace.standardOpen B S b) V hVj
            (ProjectiveSpace.coordRatio B S b d) •
          N.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (w a b) := by
    have h := congrArg (N.presheaf.map (homOfLE hVw).op) (hrel d)
    rw [Scheme.Modules.map_smul, presheaf_map_homOfLE_map_homOfLE,
      presheaf_map_homOfLE_map_homOfLE] at h
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map] at h
    exact h
  have hratio (d : B) :
      j.appLE (ProjectiveSpace.standardOpen B S b) V hVj
          (ProjectiveSpace.coordRatio B S b d) *
        f.appLE (ProjectiveSpace.standardOpen I S q) V hVq
          (ProjectiveSpace.linearRatio (c a) q b) =
        f.appLE (ProjectiveSpace.standardOpen I S q) V hVq
          (ProjectiveSpace.linearRatio (c a) q d) := by
    apply ((hgen q).map hVq).smul_left_injective
    dsimp only
    simp only [presheaf_map_homOfLE_map_homOfLE]
    rw [mul_smul, ← hlinV b, ← hlinV d]
    exact (hprodV d).symm
  refine ⟨W, ?_, ?_⟩
  · change x ∈ f ⁻¹ᵁ W
    rw [Scheme.preimage_basicOpen]
    exact mem_basicOpen_of_generatesAt (hgen q) (hlinear a q b) hq hx
  · obtain ⟨h, hfac⟩ := ratio_factor (ℙ(I; S) ↘ S) f j
      (ProjectiveSpace.standardOpen I S q)
      (fun d ↦ ProjectiveSpace.linearRatio (c a) q d) b hVj (hj.trans hf.symm) hratio
    have : IsImmersion (f.resLE W V le_rfl ≫ h) := by
      rw [hfac]
      infer_instance
    have : IsImmersion (f.resLE W V le_rfl) := IsImmersion.of_comp _ h
    rw [← Scheme.Hom.resLE_comp_ι f (U := W) (V := V) le_rfl]
    infer_instance

-- Preserve the original names of proof hypotheses quantified in the result.
set_option linter.unusedVariables false in
/-- Suppose the ideal twist in degree `n-r` is globally generated, and the power in degree
`r` is very ample. Any finite linear system in degree `n` containing the restriction kernel
and generating on the complement defines an immersion there.

Source: Stacks Project, varieties.tex, Tag 0FD5, proof of lemma-generate-over-complement,
from “Say L to the power n₂ is very ample” through the final affine-chart argument.
(blueprint: lem-zl-bertini-product-system-immersion).

Proof: Write U for the complement of Z. At x in U choose an ideal-twist generator a nonzero
at x, and a coordinate t_j of the very ample embedding nonzero at x. Multiplication under
L^(n-r) tensor L^r = L^n gives products a*t_l vanishing on Z; they are therefore constant
linear combinations of the chosen system. The product a*t_j is nonzero at x. On the target
open where its corresponding linear form is nonzero, the ratios (a*t_l)/(a*t_j) define a
morphism to the j-th affine chart of the fixed very ample projective space. Pulling back
these ratios cancels a, so the composite is the restriction of the fixed closed immersion.
Immersion cancellation proves the original morphism an immersion over this target open.
The opens so obtained cover its image, so target locality for immersions finishes. This
argument also handles an empty complement: the family covers its empty image. -/
theorem vanishing_linear_system_isImmersion
    (k : Type u) [Field k] {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    {Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (L : Y.Modules) [L.IsInvertible] (n r : ℕ) (hrn : r ≤ n)
    (hvery : IsVeryAmple (Y ↘ Spec (.of k)) (L.tensorPow r))
    (σ : SheafOfModules.GeneratingSections
      (i.ker.toModules ⊗ₘ L.tensorPow (n - r))) :
    letI : Module k Γ(L.tensorPow n, ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Y ↘ Spec (CommRingCat.of k)).appTop).hom
    ∀ (I : Type u) [Finite I] (s : I → (L.tensorPow n).sections)
      (t : I → ((Scheme.Modules.pullback
        (show Y.Opens from i.ker.support.compl).ι).obj (L.tensorPow n)).sections)
      (hspan : ∀ v : Γ(L.tensorPow n, ⊤), pullbackΓ i (L.tensorPow n) v = 0 →
        v ∈ Submodule.span k
          (Set.range (fun j ↦ (s j).val (op ⊤)) : Set Γ(L.tensorPow n, ⊤)))
      (hvalue : ∀ j, (t j).val (op ⊤) = pullbackΓ
        (show Y.Opens from i.ker.support.compl).ι (L.tensorPow n) ((s j).val (op ⊤)))
      (ht : Epi ((SheafOfModules.freeHomEquiv ((Scheme.Modules.pullback
        (show Y.Opens from i.ker.support.compl).ι).obj (L.tensorPow n))).symm t)),
      IsImmersion (@ProjectiveSpace.homOfGeneratingSections I _
        (show Y.Opens from i.ker.support.compl).toScheme (Spec (.of k))
        ((show Y.Opens from i.ker.support.compl).ι ≫ (Y ↘ Spec (.of k)))
        ((Scheme.Modules.pullback
          (show Y.Opens from i.ker.support.compl).ι).obj (L.tensorPow n))
        inferInstance t ht) := by
  classical
  let : Module k Γ(L.tensorPow n, ⊤) :=
    Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Y ↘ Spec (CommRingCat.of k)).appTop).hom
  intro I _ s t hspan hvalue ht
  let _ := Fintype.ofFinite I
  obtain ⟨B, j, hB, hj, hjbase, ⟨e⟩⟩ := hvery
  have := hB
  have := hj
  let U : Y.Opens := i.ker.support.compl
  let N := (Scheme.Modules.pullback U.ι).obj (L.tensorPow n)
  let μ : i.ker.toModules ⊗ₘ L.tensorPow (n - r) ⟶ L.tensorPow (n - r) :=
    i.ker.toModulesι ▷ L.tensorPow (n - r) ≫ (λ_ _).hom
  let E : L.tensorPow (n - r) ⊗ₘ L.tensorPow r ≅ L.tensorPow n :=
    (L.tensorPowAddIso (n - r) r).symm ≪≫
      eqToIso (congrArg L.tensorPow (Nat.sub_add_cancel hrn))
  let v : σ.I → B → Γ(L.tensorPow n, ⊤) := fun a b ↦ E.hom.app ⊤
    (tmulSection (μ.app ⊤ ((σ.s a).val (op ⊤)))
      (e.hom.app ⊤ (pullbackSection j (ProjectiveSpace.twistOneSection B _ b))))
  let w : σ.I → B → Γ(N, ⊤) := fun a b ↦ pullbackΓ U.ι (L.tensorPow n) (v a b)
  obtain ⟨hz, hcover, hrelations⟩ :=
    bertini_product_coordinate_relations i L n r hrn σ B j e
  have hcoeff (a : σ.I) (b : B) : ∃ c : I → k,
      ∑ q, c q • (show Γ(L.tensorPow n, ⊤) from (s q).val (op ⊤)) = v a b :=
    (Submodule.mem_span_range_iff_exists_fun k).mp (hspan (v a b) (hz a b))
  choose c hc using hcoeff
  let C : σ.I → B → I → Γ(Spec (.of k), ⊤) :=
    fun a b q ↦ (Scheme.ΓSpecIso (CommRingCat.of k)).inv (c a b q)
  have hsum (a : σ.I) (b : B) :
      w a b = ∑ q, (U.ι ≫ (Y ↘ Spec (.of k))).appTop (C a b q) •
        (show Γ(N, ⊤) from (t q).val (op ⊤)) := by
    change pullbackΓ U.ι (L.tensorPow n) (v a b) = _
    rw [← hc, map_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [hvalue]
    change pullbackΓ U.ι (L.tensorPow n)
        (((Y ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv
          (c a b q))) • (show Γ(L.tensorPow n, ⊤) from (s q).val (op ⊤))) = _
    rw [pullbackΓ_apply, pullbackΓ_apply]
    exact pullbackSection_smul U.ι _ _
  apply immersion_of_coordinate_products (U.ι ≫ (Y ↘ Spec (.of k))) N t ht
    (U.ι ≫ j) (by rw [Category.assoc, hjbase]) w C hsum hcover hrelations

end AlgebraicGeometry
