/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module
public import Sheaf.AlgebraicGeometry.VectorProjectiveCompletionData
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
/-! # Frame charts for a presented vector-bundle completion

Source: Stacks Project, Constructions, Tags 01OA, 01OE and 01NG.
(blueprint: lem-amb-vector-projective-frame-model). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Pointwise
noncomputable section
namespace AlgebraicGeometry.VectorProjectiveCompletion
open VectorBundleZeroSection
private def freeSectionEquivAt (T : Scheme.{u}) (I : Type u) [Fintype I] [DecidableEq I]
    (U : T.Opens) :
    Γ(SheafOfModules.free (R := T.ringCatSheaf) I, U) ≃ₗ[Γ(T, U)] (I → Γ(T, U)) where
  toFun x i := (Scheme.Modules.freeπ i).val.app (op U) x
  map_add' x y := by ext i; exact map_add _ _ _
  map_smul' r x := by ext i; exact (Scheme.Modules.freeπ i).val.app (op U) |>.hom.map_smul r x
  invFun c := ∑ i, (SheafOfModules.ιFree (R := T.ringCatSheaf) i).val.app (op U) (c i)
  left_inv x := by
    change ∑ i : I, (Scheme.Modules.Hom.app
      (Scheme.Modules.freeπ i ≫ SheafOfModules.ιFree i) U) x = x
    rw [← Scheme.Modules.Hom.sum_app_apply, Scheme.Modules.sum_freeπ_ιFree]
    rfl
  right_inv c := by
    ext j
    change (Scheme.Modules.freeπ j).val.app (op U) (∑ i,
      (SheafOfModules.ιFree (R := T.ringCatSheaf) i).val.app (op U) (c i)) = c j
    rw [map_sum, Finset.sum_eq_single j _ (by simp)]
    · have h := congrArg (fun f ↦ f.val.app (op U) (c j))
        (Scheme.Modules.ιFree_freeπ (X := T) j j)
      rw [if_pos rfl] at h
      exact h
    · intro i _ hij
      have h := congrArg (fun f ↦ f.val.app (op U) (c i))
        (Scheme.Modules.ιFree_freeπ (X := T) i j)
      rw [if_neg hij] at h
      exact h


private local instance restrictedSectionsModule (S : Scheme.{u}) (F : S.Modules) (V : S.Opens)
    (U : V.toScheme.Opens) : Module Γ(V.toScheme, U) Γ(F, V.ι ''ᵁ U) := by
  change Module Γ(S, V.ι ''ᵁ U) Γ(F, V.ι ''ᵁ U)
  infer_instance

private def restrictedSectionsEquiv (S : Scheme.{u}) (F : S.Modules) (V : S.Opens)
    (U : V.toScheme.Opens) :
    Γ(F.restrict V.ι, U) ≃ₗ[Γ(V.toScheme, U)] Γ(F, V.ι ''ᵁ U) where
  toFun := (F.restrictAppIso V.ι U).hom
  invFun := (F.restrictAppIso V.ι U).inv
  left_inv := Iso.hom_inv_id_apply _
  right_inv := Iso.inv_hom_id_apply _
  map_add' := map_add _
  map_smul' r x := by
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl

private def frameBasisAt (S : Scheme.{u}) (d : ℕ) (F : S.Modules) (V : S.Opens)
    (e : Trivialization S d F V) (U : V.toScheme.Opens) :
    Module.Basis (ULift.{u} (Fin d)) Γ(S, V.ι ''ᵁ U) Γ(F, V.ι ''ᵁ U) := by
  classical
  change Module.Basis (ULift.{u} (Fin d)) Γ(V.toScheme, U) Γ(F, V.ι ''ᵁ U)
  exact (((Pi.basisFun Γ(V.toScheme, U) (ULift.{u} (Fin d))).map
    (freeSectionEquivAt V.toScheme (ULift.{u} (Fin d)) U).symm).map
      (Scheme.Modules.appLinearEquivOfIso e.symm U)).map (restrictedSectionsEquiv S F V U)

private theorem frameBasisAt_apply (S : Scheme.{u}) (d : ℕ) (F : S.Modules) (V : S.Opens)
    (e : Trivialization S d F V) (U : V.toScheme.Opens) (i : ULift.{u} (Fin d)) :
    frameBasisAt S d F V e U i = (F.restrictAppIso V.ι U).hom
      (e.inv.val.app (op U)
        ((SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) i).val.app (op U)
          (1 : Γ(V.toScheme, U)))) := by
  classical
  unfold frameBasisAt
  erw [Module.Basis.map_apply, Module.Basis.map_apply, Module.Basis.map_apply,
    Pi.basisFun_apply]
  change (F.restrictAppIso V.ι U).hom
    (e.inv.val.app (op U) (∑ j : ULift.{u} (Fin d),
      (SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) j).val.app (op U)
        ((Pi.single i 1 : ULift.{u} (Fin d) → Γ(V.toScheme, U)) j))) = _
  congr 2
  simp only [Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

set_option backward.isDefEq.respectTransparency false in

private def castBasis (S : Scheme.{u}) (F : S.Modules) {U V : S.Opens} (h : U = V)
    {I : Type u} (b : Module.Basis I Γ(S, U) Γ(F, U)) : Module.Basis I Γ(S, V) Γ(F, V) :=
  h ▸ b
private theorem castBasis_apply (S : Scheme.{u}) (F : S.Modules) {U V : S.Opens}
    (h : U = V) {I : Type u} (b : Module.Basis I Γ(S, U) Γ(F, U)) (i : I) :
    castBasis S F h b i = F.presheaf.map (eqToHom h.symm).op (b i) := by
  subst V
  simp [castBasis]
private def sectionBasis (S : Scheme.{u}) (d : ℕ) (F : S.Modules) (V : S.Opens)
    (e : Trivialization S d F V) : Module.Basis (Fin d) Γ(S, V) Γ(F, V) :=
  (castBasis S F V.ι_image_top (frameBasisAt S d F V e ⊤)).reindex Equiv.ulift
private theorem sectionBasis_apply (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    (V : S.Opens) (e : Trivialization S d F V) (i : Fin d) :
    sectionBasis S d F V e i = frameSection S d F V e i := by
  rw [sectionBasis, Module.Basis.reindex_apply, castBasis_apply, frameBasisAt_apply]
  rfl
private def plusBasis (S : Scheme.{u}) (d : ℕ) (F : S.Modules) (V : S.Opens)
    (e : Trivialization S d F V) : Module.Basis (Fin (d + 1)) Γ(S, V) (Γ(S, V) × Γ(F, V)) :=
  ((Module.Basis.singleton (Fin 1) Γ(S, V)).prod (sectionBasis S d F V e)).reindex
    (finSumFinEquiv.trans (finCongr (Nat.add_comm 1 d)))
private theorem plusBasis_zero (S : Scheme.{u}) (d : ℕ) (F : S.Modules) (V : S.Opens)
    (e : Trivialization S d F V) : plusBasis S d F V e 0 = (1,0) := by
  rw [plusBasis, Module.Basis.reindex_apply]
  have h0 : (finSumFinEquiv.trans (finCongr (Nat.add_comm 1 d))).symm
      (0 : Fin (d + 1)) = Sum.inl (0 : Fin 1) := by
    apply (finSumFinEquiv.trans (finCongr (Nat.add_comm 1 d))).symm_apply_eq.mpr
    apply Fin.ext
    rfl
  rw [h0, Module.Basis.prod_apply]
  simp
private theorem plusBasis_succ (S : Scheme.{u}) (d : ℕ) (F : S.Modules) (V : S.Opens)
    (e : Trivialization S d F V) (i : Fin d) :
    plusBasis S d F V e i.succ = (0,frameSection S d F V e i) := by
  rw [plusBasis, Module.Basis.reindex_apply]
  have hi : (finSumFinEquiv.trans (finCongr (Nat.add_comm 1 d))).symm i.succ =
      Sum.inr i := by
    apply (finSumFinEquiv.trans (finCongr (Nat.add_comm 1 d))).symm_apply_eq.mpr
    apply Fin.ext
    change i.val + 1 = 1 + i.val
    omega
  rw [hi, Module.Basis.prod_apply]
  simp [sectionBasis_apply]
private def framePolynomial (S : Scheme.{u}) (d : ℕ) (F : S.Modules) (V : S.affineOpens)
    (e : Trivialization S d F V.1) (P : Presentation S F) :
    MvPolynomial (Fin (d + 1)) Γ(S, V.1) ≃ₐ[Γ(S, V.1)] P.algebra.obj V :=
  (SymmetricAlgebra.equivMvPolynomial (plusBasis S d F V.1 e)).symm.trans (P.equiv V)
private theorem framePolynomial_zero (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    (V : S.affineOpens) (e : Trivialization S d F V.1) (P : Presentation S F) :
    framePolynomial S d F V e P (MvPolynomial.X 0) = t P V := by
  simp only [framePolynomial, AlgEquiv.trans_apply, SymmetricAlgebra.equivMvPolynomial_symm_X,
    plusBasis_zero]
  rfl
private theorem framePolynomial_succ (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    (V : S.affineOpens) (e : Trivialization S d F V.1) (P : Presentation S F) (i : Fin d) :
    framePolynomial S d F V e P (MvPolynomial.X i.succ) = x P V (frameSection S d F V.1 e i) := by
  simp only [framePolynomial, AlgEquiv.trans_apply, SymmetricAlgebra.equivMvPolynomial_symm_X,
    plusBasis_succ]
  rfl
set_option backward.isDefEq.respectTransparency false in
private theorem framePolynomial_grade (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    (V : S.affineOpens) (e : Trivialization S d F V.1) (P : Presentation S F)
    (n : ℕ) (f : MvPolynomial (Fin (d + 1)) Γ(S, V.1)) :
    framePolynomial S d F V e P f ∈ P.algebra.grading V n ↔
      f ∈ MvPolynomial.homogeneousSubmodule (Fin (d + 1)) Γ(S, V.1) n := by
  let q := framePolynomial S d F V e P
  let b := plusBasis S d F V.1 e
  have h1 : (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) Γ(S, V.1) 1).map
      q.toLinearMap = (SymmetricAlgebra.ι Γ(S, V.1) (Γ(S, V.1) × Γ(F, V.1))).range.map
        (P.equiv V).toLinearMap := by
    rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X]
    have hb := b.span_eq
    have he : (Submodule.span Γ(S, V.1) (Set.range b)).map
        ((P.equiv V).toLinearMap.comp
          (SymmetricAlgebra.ι Γ(S, V.1) (Γ(S, V.1) × Γ(F, V.1)))) =
        (SymmetricAlgebra.ι Γ(S, V.1) (Γ(S, V.1) × Γ(F, V.1))).range.map
          (P.equiv V).toLinearMap := by
      rw [hb, Submodule.map_top, LinearMap.range_comp]
    rw [← he, Submodule.map_span, Submodule.map_span]
    congr 1
    rw [← Set.range_comp, ← Set.range_comp]
    congr 1
    funext i
    exact congrArg (P.equiv V) (SymmetricAlgebra.equivMvPolynomial_symm_X b i)
  have hn : (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) Γ(S, V.1) n).map
      q.toLinearMap = P.algebra.grading V n := by
    rw [← MvPolynomial.homogeneousSubmodule_one_pow]
    change ((MvPolynomial.homogeneousSubmodule (Fin (d + 1)) Γ(S, V.1) 1)^n).map
      q.toAlgHom.toLinearMap = _
    rw [Submodule.map_pow]
    change ((MvPolynomial.homogeneousSubmodule (Fin (d + 1)) Γ(S, V.1) 1).map
      q.toLinearMap)^n = _
    rw [h1, P.grade_eq]
    exact (Submodule.map_pow _ (P.equiv V).toAlgHom n).symm
  rw [← hn, Submodule.mem_map]
  constructor
  · rintro ⟨g,hg,hgf⟩
    exact q.injective hgf ▸ hg
  · intro hf
    exact ⟨f,hf,rfl⟩
private def frameRingEquiv (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    (V : S.affineOpens) (e : Trivialization S d F V.1) (P : Presentation S F) :
    (RelativeProjectiveSpace.algebra V.1.toScheme d).sections (affineTop V) ≃+*
      P.algebra.obj V :=
  (RelativeProjectiveSpace.affinePolynomialEquiv V.1.toScheme d (affineTop V)).symm.trans
    ((MvPolynomial.mapEquiv (Fin (d + 1)) (V.1.topIso.commRingCatIsoToRingEquiv)).trans
      (framePolynomial S d F V e P).toRingEquiv)
private theorem frameRingEquiv_coordinate (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    (V : S.affineOpens) (e : Trivialization S d F V.1) (P : Presentation S F)
    (i : Fin (d + 1)) : frameRingEquiv S d F V e P
      (RelativeProjectiveSpace.coordinate V.1.toScheme d (affineTop V) i) =
      framePolynomial S d F V e P (MvPolynomial.X i) := by
  have hi := (RelativeProjectiveSpace.existsUnique_affinePolynomialEquiv
    V.1.toScheme d (affineTop V)).exists.choose_spec.2 i
  change framePolynomial S d F V e P
    (MvPolynomial.mapEquiv (Fin (d + 1)) V.1.topIso.commRingCatIsoToRingEquiv
      ((RelativeProjectiveSpace.affinePolynomialEquiv V.1.toScheme d (affineTop V)).symm
        (RelativeProjectiveSpace.coordinate V.1.toScheme d (affineTop V) i))) = _
  change RelativeProjectiveSpace.affinePolynomialEquiv V.1.toScheme d (affineTop V)
    (MvPolynomial.X i) = _ at hi
  rw [← hi, RingEquiv.symm_apply_apply]
  simp
private theorem frameRingEquiv_scalar (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    (V : S.affineOpens) (e : Trivialization S d F V.1) (P : Presentation S F)
    (r : Γ(V.1.toScheme, ⊤)) : frameRingEquiv S d F V e P
      ((RelativeProjectiveSpace.algebra V.1.toScheme d).algebra.obj.hom.hom.app (op ⊤) r) =
      algebraMap Γ(S, V.1) (P.algebra.obj V) (V.1.topIso.hom r) := by
  let C := RelativeProjectiveSpace.affinePolynomialEquiv V.1.toScheme d (affineTop V)
  have hr : C (MvPolynomial.C r) =
      (RelativeProjectiveSpace.algebra V.1.toScheme d).algebra.obj.hom.hom.app
        (op (affineTop V).1) r :=
    (RelativeProjectiveSpace.existsUnique_affinePolynomialEquiv
      V.1.toScheme d (affineTop V)).exists.choose_spec.1 r
  have hinv : C.symm ((RelativeProjectiveSpace.algebra V.1.toScheme d).algebra.obj.hom.hom.app
      (op (affineTop V).1) r) = MvPolynomial.C r := by
    exact C.symm_apply_eq.mpr hr.symm
  change framePolynomial S d F V e P
    (MvPolynomial.mapEquiv (Fin (d + 1)) V.1.topIso.commRingCatIsoToRingEquiv
      (C.symm ((RelativeProjectiveSpace.algebra V.1.toScheme d).algebra.obj.hom.hom.app
        (op (affineTop V).1) r))) = _
  rw [hinv, MvPolynomial.mapEquiv_apply, MvPolynomial.map_C]
  change framePolynomial S d F V e P (MvPolynomial.C (V.1.topIso.hom r)) = _
  exact (framePolynomial S d F V e P).commutes (V.1.topIso.hom r)
private theorem frameRingEquiv_grade (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    (V : S.affineOpens) (e : Trivialization S d F V.1) (P : Presentation S F)
    (n : ℕ) (z : (RelativeProjectiveSpace.algebra V.1.toScheme d).sections (affineTop V)) :
    frameRingEquiv S d F V e P z ∈ P.algebra.grading V n ↔
      z ∈ (RelativeProjectiveSpace.algebra V.1.toScheme d).sectionGrade (affineTop V) n := by
  obtain ⟨f, rfl⟩ := (RelativeProjectiveSpace.affinePolynomialEquiv V.1.toScheme d
    (affineTop V)).surjective z
  simp only [frameRingEquiv, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
  change framePolynomial S d F V e P
    (MvPolynomial.mapEquiv (Fin (d + 1)) V.1.topIso.commRingCatIsoToRingEquiv f) ∈
    P.algebra.grading V n ↔ _
  rw [framePolynomial_grade, RelativeProjectiveSpace.affinePolynomial_homogeneous]
  change (MvPolynomial.mapEquiv (Fin (d + 1)) V.1.topIso.commRingCatIsoToRingEquiv
    f).IsHomogeneous n ↔ f.IsHomogeneous n
  constructor
  · intro h
    have h' : ((MvPolynomial.mapEquiv (Fin (d + 1))
        V.1.topIso.commRingCatIsoToRingEquiv).symm
          (MvPolynomial.mapEquiv (Fin (d + 1))
            V.1.topIso.commRingCatIsoToRingEquiv f)).IsHomogeneous n :=
      MvPolynomial.IsHomogeneous.map h V.1.topIso.commRingCatIsoToRingEquiv.symm.toRingHom
    simpa only [RingEquiv.symm_apply_apply] using h'
  · intro h
    exact MvPolynomial.IsHomogeneous.map h V.1.topIso.commRingCatIsoToRingEquiv.toRingHom
private def frameGradedMap (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    (V : S.affineOpens) (e : Trivialization S d F V.1) (P : Presentation S F) :
    (RelativeProjectiveSpace.algebra V.1.toScheme d).sectionGrade (affineTop V) →+*ᵍ
      P.algebra.grading V where
  toRingHom := (frameRingEquiv S d F V e P).toRingHom
  map_mem {n z} h := (frameRingEquiv_grade S d F V e P n z).mpr h
private def frameGradedInv (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    (V : S.affineOpens) (e : Trivialization S d F V.1) (P : Presentation S F) :
    P.algebra.grading V →+*ᵍ
      (RelativeProjectiveSpace.algebra V.1.toScheme d).sectionGrade (affineTop V) where
  toRingHom := (frameRingEquiv S d F V e P).symm.toRingHom
  map_mem {n z} h := (frameRingEquiv_grade S d F V e P n _).mp
    (by change frameRingEquiv S d F V e P ((frameRingEquiv S d F V e P).symm z) ∈ _
        rwa [RingEquiv.apply_symm_apply])
private def frameProjIso (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    (V : S.affineOpens) (e : Trivialization S d F V.1) (P : Presentation S F) :
    Proj (P.algebra.grading V) ≅
      (RelativeProjectiveSpace.algebra V.1.toScheme d).localProj (affineTop V) where
  hom := Proj.map (frameGradedMap S d F V e P)
    (GradedRingHom.irrelevant_le_map_of_surjective (frameRingEquiv S d F V e P).surjective)
  inv := Proj.map (frameGradedInv S d F V e P)
    (GradedRingHom.irrelevant_le_map_of_surjective (frameRingEquiv S d F V e P).symm.surjective)
  hom_inv_id := by
    rw [← Proj.map_comp]
    have h : (frameGradedMap S d F V e P).comp (frameGradedInv S d F V e P) =
        GradedRingHom.id (P.algebra.grading V) := by
      ext z
      exact (frameRingEquiv S d F V e P).apply_symm_apply z
    rw [Proj.map_congr h _ (by simp), Proj.map_id]
  inv_hom_id := by
    rw [← Proj.map_comp]
    have h : (frameGradedInv S d F V e P).comp (frameGradedMap S d F V e P) =
        GradedRingHom.id _ := by
      ext z
      exact (frameRingEquiv S d F V e P).symm_apply_apply z
    rw [Proj.map_congr h _ (by simp), Proj.map_id]
    rfl
private instance projectiveChart_isIso (S : Scheme.{u}) (V : S.affineOpens) (d : ℕ) :
    IsIso (projectiveChart V d) := by
  unfold projectiveChart
  have htop : RelativeProjectiveSpace.π V.1.toScheme d ⁻¹ᵁ ⊤ = ⊤ := rfl
  have : IsIso (RelativeProjectiveSpace.π V.1.toScheme d ⁻¹ᵁ ⊤).ι := by
    rw [htop]
    exact (RelativeProjectiveSpace.scheme V.1.toScheme d).topIso.isIso_hom
  infer_instance
private theorem projectiveChart_standardOpen (S : Scheme.{u}) (V : S.affineOpens) (d : ℕ)
    (i : Fin (d + 1)) : projectiveChart V d ⁻¹ᵁ
      RelativeProjectiveSpace.standardOpen V.1.toScheme d i =
      RelativeProjectiveSpace.localStandardOpen V.1.toScheme d (affineTop V) i := by
  have h := RelativeProjectiveSpace.standardOpen_restrict V.1.toScheme d (affineTop V) i
  change (RelativeProjectiveSpace.π V.1.toScheme d ⁻¹ᵁ ⊤).ι ⁻¹ᵁ _ =
    ((RelativeProjectiveSpace.construction V.1.toScheme d).restrictionIso (affineTop V)).hom
      ⁻¹ᵁ _ at h
  unfold projectiveChart
  rw [Scheme.Hom.comp_preimage]
  rw [h, ← Scheme.Hom.comp_preimage, Iso.inv_hom_id]
  rfl
private theorem projectiveChart_over (S : Scheme.{u}) (V : S.affineOpens) (d : ℕ) :
    projectiveChart V d ≫ RelativeProjectiveSpace.π V.1.toScheme d =
      (RelativeProjectiveSpace.algebra V.1.toScheme d).localBase (affineTop V) ≫
        (affineTop V).1.ι := by
  unfold projectiveChart
  rw [Category.assoc]
  have h := (RelativeProjectiveSpace.construction V.1.toScheme d).restriction_over (affineTop V)
  exact (Iso.inv_comp_eq _).mpr h.symm
private theorem affineTop_spec (S : Scheme.{u}) (V : S.affineOpens) :
    Spec.map V.1.topIso.hom ≫ (affineTop V).2.isoSpec.inv ≫ (affineTop V).1.ι =
      V.2.isoSpec.inv := by
  rw [IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.fromSpec_top]
  rfl
set_option backward.isDefEq.respectTransparency false in
private theorem frameProj_over (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    (V : S.affineOpens) (e : Trivialization S d F V.1) (P : Presentation S F) :
    (frameProjIso S d F V e P).hom ≫ projectiveChart V d ≫
      RelativeProjectiveSpace.π V.1.toScheme d = P.algebra.toOpen V := by
  let A := RelativeProjectiveSpace.algebra V.1.toScheme d
  let g := frameGradedMap S d F V e P
  have h0 : g.gradeZeroRingHom.comp (A.unitZero (affineTop V)) =
      (algebraMap Γ(S, V.1) (P.algebra.grading V 0)).comp V.1.topIso.hom.hom := by
    apply RingHom.ext
    intro r
    apply Subtype.ext
    exact frameRingEquiv_scalar S d F V e P r
  rw [projectiveChart_over]
  change Proj.map g _ ≫ (A.localBase (affineTop V) ≫ (affineTop V).1.ι) = _
  rw [RelativeProjAlgebra.localBase, ← Category.assoc, ← Category.assoc,
    Proj.map_toSpecZero]
  simp only [Category.assoc]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, h0,
    CommRingCat.ofHom_comp, Spec.map_comp_assoc]
  change Proj.toSpecZero (P.algebra.grading V) ≫
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) (P.algebra.grading V 0))) ≫
      Spec.map V.1.topIso.hom ≫ (affineTop V).2.isoSpec.inv ≫ (affineTop V).1.ι = _
  rw [affineTop_spec]
  rfl
/-- A frame of F identifies every presented projective bundle with projective space,
with the fixed homogeneous coordinates and structural map.
Source: Stacks Project, Constructions, Tags 01OA, 01OE and 01NG.
(blueprint: lem-amb-vector-projective-frame-model).

Proof: evaluation of the frame on the free module basis gives a basis of F(V).
Adjoin the distinguished vector (1,0) to obtain a basis of R times F(V). The universal
property identifies its symmetric algebra with the polynomial ring, sending the first
variable to t and each later variable to its frame section. The grading is preserved:
degree one is the span of these basis generators and degree n is its nth power.
Compose with the canonical polynomial identification of relative projective space,
transporting coefficients through V.topIso. This gives inverse graded ring maps.
Their Proj maps are inverse by Proj functoriality. The local relative-Proj embedding on
the whole affine base is an isomorphism. Its restriction and structural-map equations
prove the displayed base compatibility; the preimage formula for a Proj basic open
identifies the first standard open with D_+(t). Empty frames and zero rings are included. -/
theorem exists_frameModel (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    (P : Presentation S F) :
    ∀ (V : S.affineOpens) (e : VectorBundleZeroSection.Trivialization S d F V.1),
        ∃ q : MvPolynomial (Fin (d + 1)) Γ(S, V.1) ≃ₐ[Γ(S, V.1)] P.algebra.obj V,
          q (MvPolynomial.X 0) = t P V ∧
          (∀ i : Fin d, q (MvPolynomial.X i.succ) =
            x P V (VectorBundleZeroSection.frameSection S d F V.1 e i)) ∧
          (∀ (n : ℕ) (f : MvPolynomial (Fin (d + 1)) Γ(S, V.1)),
            q f ∈ P.algebra.grading V n ↔
              f ∈ MvPolynomial.homogeneousSubmodule (Fin (d + 1)) Γ(S, V.1) n) ∧
          ∃ (g : (RelativeProjectiveSpace.algebra V.1.toScheme d).sectionGrade
                (affineTop V) →+*ᵍ P.algebra.grading V) (hg : Function.Bijective g)
              (b : Proj (P.algebra.grading V) ≅ RelativeProjectiveSpace.scheme V.1.toScheme d),
            (∀ r : Γ(V.1.toScheme, ⊤),
              g ((RelativeProjectiveSpace.algebra V.1.toScheme d).algebra.obj.hom.hom.app
                (op ⊤) r) = algebraMap Γ(S, V.1) (P.algebra.obj V) (V.1.topIso.hom r)) ∧
            (∀ i : Fin (d + 1),
              g (RelativeProjectiveSpace.coordinate V.1.toScheme d (affineTop V) i) =
                q (MvPolynomial.X i)) ∧
            b.hom = Proj.map g (GradedRingHom.irrelevant_le_map_of_surjective hg.surjective) ≫
              projectiveChart V d ∧
            b.hom ≫ RelativeProjectiveSpace.π V.1.toScheme d = P.algebra.toOpen V ∧
            b.hom ⁻¹ᵁ RelativeProjectiveSpace.standardOpen V.1.toScheme d 0 =
              Proj.basicOpen (P.algebra.grading V) (t P V) := by
  intro V e
  let q := framePolynomial S d F V e P
  let g := frameGradedMap S d F V e P
  have hg : Function.Bijective g := (frameRingEquiv S d F V e P).bijective
  let b := frameProjIso S d F V e P ≪≫ asIso (projectiveChart V d)
  refine ⟨q, framePolynomial_zero S d F V e P,
    framePolynomial_succ S d F V e P, framePolynomial_grade S d F V e P,
    g, hg, b, frameRingEquiv_scalar S d F V e P,
    frameRingEquiv_coordinate S d F V e P, rfl,
    frameProj_over S d F V e P, ?_⟩
  change (Proj.map g _ ≫ projectiveChart V d) ⁻¹ᵁ
    RelativeProjectiveSpace.standardOpen V.1.toScheme d 0 = _
  rw [Scheme.Hom.comp_preimage, projectiveChart_standardOpen]
  change Proj.map g _ ⁻¹ᵁ
    Proj.basicOpen ((RelativeProjectiveSpace.algebra V.1.toScheme d).sectionGrade
      (affineTop V)) (RelativeProjectiveSpace.coordinate V.1.toScheme d (affineTop V) 0) = _
  rw [Proj.map_preimage_basicOpen]
  change Proj.basicOpen (P.algebra.grading V)
    (frameRingEquiv S d F V e P (RelativeProjectiveSpace.coordinate
      V.1.toScheme d (affineTop V) 0)) = _
  rw [frameRingEquiv_coordinate, framePolynomial_zero]

end AlgebraicGeometry.VectorProjectiveCompletion
