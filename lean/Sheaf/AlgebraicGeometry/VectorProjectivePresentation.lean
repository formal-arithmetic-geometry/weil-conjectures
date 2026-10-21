/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module
public import Sheaf.AlgebraicGeometry.VectorProjectiveCompletionData
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
/-! # Presented projective bundle for O plus F

Source: Stacks Project, Constructions, Tags 01OA, 01OB and 01OE.
(blueprint: lem-amb-vector-projective-presentation). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.VectorProjectiveCompletion
private def augmentedModule (S : Scheme.{u}) (F : S.Modules) : S.Modules :=
  SheafOfModules.unit S.ringCatSheaf ⨯ F
private def augmentedSections (S : Scheme.{u}) (F : S.Modules) (U : S.Opens) :
    (augmentedModule S F).val.obj (op U) ≃ₗ[Γ(S, U)] (Γ(S, U) × F.val.obj (op U)) :=
  ((PreservesLimitPair.iso (SheafOfModules.evaluation S.ringCatSheaf (op U))
      (SheafOfModules.unit S.ringCatSheaf) F) ≪≫
    (limit.isoLimitCone (ModuleCat.binaryProductLimitCone
      ((SheafOfModules.evaluation S.ringCatSheaf (op U)).obj
        (SheafOfModules.unit S.ringCatSheaf))
      ((SheafOfModules.evaluation S.ringCatSheaf (op U)).obj F)))).toLinearEquiv
private theorem augmentedSections_fst (S : Scheme.{u}) (F : S.Modules) (U : S.Opens)
    (m : (augmentedModule S F).val.obj (op U)) :
    (augmentedSections S F U m).1 =
      (prod.fst : augmentedModule S F ⟶ SheafOfModules.unit S.ringCatSheaf).val.app (op U) m := by
  let E := SheafOfModules.evaluation S.ringCatSheaf (op U)
  let L := ModuleCat.binaryProductLimitCone
    (E.obj (SheafOfModules.unit S.ringCatSheaf)) (E.obj F)
  change ((PreservesLimitPair.iso E _ _).hom ≫ (limit.isoLimitCone L).hom ≫
    L.cone.π.app ⟨WalkingPair.left⟩).hom m = _
  rw [limit.isoLimitCone_hom_π, PreservesLimitPair.iso_hom, prodComparison_fst]
  rfl
private theorem augmentedSections_snd (S : Scheme.{u}) (F : S.Modules) (U : S.Opens)
    (m : (augmentedModule S F).val.obj (op U)) :
    (augmentedSections S F U m).2 =
      (prod.snd : augmentedModule S F ⟶ F).val.app (op U) m := by
  let E := SheafOfModules.evaluation S.ringCatSheaf (op U)
  let L := ModuleCat.binaryProductLimitCone
    (E.obj (SheafOfModules.unit S.ringCatSheaf)) (E.obj F)
  change ((PreservesLimitPair.iso E _ _).hom ≫ (limit.isoLimitCone L).hom ≫
    L.cone.π.app ⟨WalkingPair.right⟩).hom m = _
  rw [limit.isoLimitCone_hom_π, PreservesLimitPair.iso_hom, prodComparison_snd]
  rfl
private theorem augmentedSections_restriction (S : Scheme.{u}) (F : S.Modules)
    {U V : S.Opensᵒᵖ} (h : U ⟶ V) (m : (augmentedModule S F).val.obj U) :
    augmentedSections S F V.unop ((augmentedModule S F).val.map h m) =
      (S.presheaf.map h (augmentedSections S F U.unop m).1,
        F.val.map h (augmentedSections S F U.unop m).2) := by
  apply Prod.ext
  · rw [augmentedSections_fst, augmentedSections_fst]
    exact PresheafOfModules.naturality_apply (prod.fst : augmentedModule S F ⟶
      SheafOfModules.unit S.ringCatSheaf).val h m
  · rw [augmentedSections_snd, augmentedSections_snd]
    exact PresheafOfModules.naturality_apply (prod.snd : augmentedModule S F ⟶ F).val h m
private theorem augmentedModule_rank (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] :
    (augmentedModule S F).IsFiniteLocallyFreeOfRank (d + 1) := by
  obtain ⟨I, U, hU, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := d)
  apply Scheme.Modules.isFiniteLocallyFreeOfRank_of_restrict_iso_free
    (augmentedModule S F) (fun i ↦ (U i).ι) (by simpa using hU)
  intro i
  let T := (U i).toScheme
  let f := U i |>.ι
  let G := Scheme.Modules.restrictFunctor f
  have : PreservesFiniteColimits G := by
    exact preservesFiniteColimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback f).symm
  have : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBinaryCoproducts G
  have : PreservesLimitsOfShape (Discrete WalkingPair) G :=
    preservesBinaryProducts_of_preservesBinaryBiproducts G
  let eqv : (ULift.{u} (Fin 1) ⊕ ULift.{u} (Fin d)) ≃ ULift.{u} (Fin (d + 1)) :=
    (Equiv.sumCongr (Equiv.ulift : ULift.{u} (Fin 1) ≃ Fin 1)
      (Equiv.ulift : ULift.{u} (Fin d) ≃ Fin d)).trans
      ((finSumFinEquiv).trans ((finCongr (Nat.add_comm 1 d)).trans
        (Equiv.ulift : ULift.{u} (Fin (d + 1)) ≃ Fin (d + 1)).symm))
  exact ⟨PreservesLimitPair.iso G _ _ ≪≫
    prod.mapIso ((Scheme.Modules.restrictUnitIso f) ≪≫
      (SheafOfModules.freeUniqueIso (R := T.ringCatSheaf) (ULift.{u} (Fin 1))).symm)
      (e i).some ≪≫ biprodIso _ _ ≪≫ SheafOfModules.freeSumIso _ _ ≪≫
      (SheafOfModules.freeFunctor (R := T.ringCatSheaf)).mapIso eqv.toIso⟩
private def symmetricCongr {R M N : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    SymmetricAlgebra R M ≃ₐ[R] SymmetricAlgebra R N :=
  AlgEquiv.ofAlgHom
    (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp e.toLinearMap))
    (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R M).comp e.symm.toLinearMap))
    (by ext m; simp) (by ext m; simp)
private theorem symmetricCongr_ι {R M N : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (m : M) :
    symmetricCongr e (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R N (e m) := by
  exact SymmetricAlgebra.lift_ι_apply _ _

private theorem symmetricDegree_eq (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) : Scheme.symmetricDegree R M n = (SymmetricAlgebra.ι R M).range ^ n := by
  have h := SymmetricAlgebra.graded_span_pure_tensors R M n
  simp only [Submodule.map_pow, ← LinearMap.range_comp] at h
  change (SymmetricAlgebra.ι R M).range ^ n = _ at h
  simpa only [Scheme.symmetricDegree, List.prod_ofFn] using h.symm

private def presentationEquiv (S : Scheme.{u}) (F : S.Modules)
    (A : S.SymmetricGradedAlgebraData (augmentedModule S F)) (V : S.affineOpens) :
    SymmetricAlgebra Γ(S, V.1) (Γ(S, V.1) × F.val.obj (op V.1)) ≃ₐ[Γ(S, V.1)] A.data.obj V :=
  (symmetricCongr (augmentedSections S F V.1).symm).trans (A.sectionEquiv V)
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem presentationEquiv_grade (S : Scheme.{u}) (F : S.Modules)
    (A : S.SymmetricGradedAlgebraData (augmentedModule S F)) (V : S.affineOpens) (n : ℕ) :
    A.data.grading V n =
      ((SymmetricAlgebra.ι Γ(S, V.1) (Γ(S, V.1) × F.val.obj (op V.1))).range ^ n).map
        (presentationEquiv S F A V).toLinearMap := by
  have hgrade : A.data.grading V n =
      ((SymmetricAlgebra.ι Γ(S, V.1) ((augmentedModule S F).val.obj (op V.1))).range ^ n).map
        (A.sectionEquiv V).toLinearMap := by
    ext z
    rw [Submodule.mem_map]
    constructor
    · intro hz
      refine ⟨(A.sectionEquiv V).symm z, ?_, (A.sectionEquiv V).apply_symm_apply z⟩
      rw [← symmetricDegree_eq]
      exact (A.sectionEquiv_grade V n _).mpr (by simpa using hz)
    · rintro ⟨z,hz,rfl⟩
      exact (A.sectionEquiv_grade V n z).mp (by rwa [symmetricDegree_eq])
  rw [hgrade]
  change (((SymmetricAlgebra.ι Γ(S, V.1)
    ((augmentedModule S F).val.obj (op V.1))).range)^n).map
      (A.sectionEquiv V).toAlgHom.toLinearMap =
    (((SymmetricAlgebra.ι Γ(S, V.1) (Γ(S, V.1) × F.val.obj (op V.1))).range)^n).map
      (presentationEquiv S F A V).toAlgHom.toLinearMap
  rw [Submodule.map_pow, Submodule.map_pow, ← LinearMap.range_comp,
    ← LinearMap.range_comp]
  congr 1
  change ((A.sectionEquiv V).toLinearMap.comp
    (SymmetricAlgebra.ι Γ(S, V.1) ((augmentedModule S F).val.obj (op V.1)))).range =
    ((presentationEquiv S F A V).toLinearMap.comp
      (SymmetricAlgebra.ι Γ(S, V.1) (Γ(S, V.1) × F.val.obj (op V.1)))).range
  have hcomp : (presentationEquiv S F A V).toLinearMap.comp
      (SymmetricAlgebra.ι Γ(S, V.1) (Γ(S, V.1) × F.val.obj (op V.1))) =
      ((A.sectionEquiv V).toLinearMap.comp
        (SymmetricAlgebra.ι Γ(S, V.1) ((augmentedModule S F).val.obj (op V.1)))).comp
          (augmentedSections S F V.1).symm.toLinearMap := by
    apply LinearMap.ext
    intro m
    exact congrArg (A.sectionEquiv V) (symmetricCongr_ι _ m)
  rw [hcomp, LinearMap.range_comp_of_range_eq_top _
    (augmentedSections S F V.1).symm.range]
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private def makePresentation (S : Scheme.{u}) (F : S.Modules)
    (A : S.SymmetricGradedAlgebraData (augmentedModule S F)) : Presentation S F where
  algebra := A.data
  equiv := presentationEquiv S F A
  grade_eq := presentationEquiv_grade S F A
  restriction U V h a m := by
    dsimp only [presentationEquiv, AlgEquiv.trans_apply]
    rw [symmetricCongr_ι, A.sectionEquiv_restriction,
      SymmetricAlgebraSheaf.restriction_ι, symmetricCongr_ι]
    congr 2
    apply (augmentedSections S F U.1).injective
    have hres := augmentedSections_restriction S F (homOfLE h).op
      ((augmentedSections S F V.1).symm (a,m))
    convert hres using 1 <;> simp only [LinearEquiv.apply_symm_apply]
    all_goals rfl
/-- The actual symmetric algebra of the unit module plus F has the affine presentations,
a proper relative Proj, and an isomorphic structural map when F has rank zero.
Source: Stacks Project, Constructions, Tags 01OA, 01OB, 01OE, 01NG.
(blueprint: lem-amb-vector-projective-presentation).

Proof: products of sheaves of modules are finite direct sums. Evaluation preserves them,
so the section module is R times F(V), compatibly with restriction. A frame of F and
the unit frame give rank d+1. Apply the existing projective-bundle realization to this
module. Transport its symmetric-algebra section equivalence along the product equivalence.
The symmetric degree-n piece is the nth power of the degree-one image; the transported
map preserves this description and the prescribed restrictions on generators.
Properness and the rank-zero structural isomorphism are the corresponding assertions
of the chosen realization. No arbitrary scheme witness is selected in a definition. -/
theorem exists_projectivePresentation (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] : ∃ P : Presentation S F,
    IsProper P.algebra.relProjHom ∧ (d = 0 → IsIso P.algebra.relProjHom) := by
  let := augmentedModule_rank S d F
  have hF : projectiveBundleRank S d (augmentedModule S F) := augmentedModule_rank S d F
  obtain ⟨D⟩ := exists_projectiveBundleTautologicalGeometry S d (augmentedModule S F)
  refine ⟨makePresentation S F D.realization.A, ?_, ?_⟩
  · change IsProper D.realization.A.data.relProjHom
    rw [D.selected]
    exact D.system.proper S (augmentedModule S F) hF
  · intro hd
    change IsIso D.realization.A.data.relProjHom
    rw [D.selected]
    exact (D.system.rank_zero S (augmentedModule S F) hF hd).choose_spec
end AlgebraicGeometry.VectorProjectiveCompletion
