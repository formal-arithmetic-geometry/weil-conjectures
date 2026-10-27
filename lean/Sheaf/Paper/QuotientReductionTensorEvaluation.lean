/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.QuotientDiagramProjectionData
import all Sheaf.Paper.SystemCochainTensorReduction
import all Sheaf.Paper.SystemTensorReductionFormula

/-! # Evaluation of normalized scalar tensor comparisons

The two routes are fixed on the same flat-term K-flat representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open WeilConjectures.SemilinearSections
namespace SheafOfModules.QuotientDiagramProjection
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{max c v r}}
  {B : ℕ → Sheaf J CommRingCat.{max c v r}} {τ : ∀ n, B (n + 1) ⟶ B n}
  {q : ∀ n, R ⟶ B n}

attribute [local irreducible] HasDerivedCategory.standard DerivedCategory
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  CoefficientClosedStructure.tensor SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem reductionTensorChain
    (s : Reduction.{c, v, r} J R B τ q) (a : Data.{c, v, r} J B τ)
    (t : TensorReduction.{c, v, r} s a) (n : ℕ)
    (P Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ) :
    (a.tensorEvaluationModel n).chain
        ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj P)
        ((s.ordinary.mapHomologicalComplex (.up ℤ)).obj Q) ≫
      ((SemilinearSections.evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex
        (.up ℤ)).map (t.chain P Q) ≫
      (s.ordinaryComplexEvaluation n).hom.app ((totalTensor.{c, v, r} J R).obj (P, Q)) =
    (totalTensor.{c, v, r} J (B n)).map
        (Prod.mkHom ((s.ordinaryComplexEvaluation n).hom.app P)
          ((s.ordinaryComplexEvaluation n).hom.app Q)) ≫
      (t.finiteModel n).chain P Q := by
  let := abelianSheafify.{c, v, max c v r} J
  let := locallyBijective.{c, v, max c v r} J
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} (B n)
  let := SheafOfModules.monoidalCategory.{v, c, max c v r} (B n)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients (B n)
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients (B n)
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp only [HomologicalComplex.comp_f]
  change tensorSummand.{c, v, r} J (B n) _ _ i j k h ≫ _ =
    tensorSummand.{c, v, r} J (B n) _ _ i j k h ≫ _
  erw [reassoc_of% ((a.tensorEvaluationModel n).summand _ _ i j k h)]
  dsimp only [Functor.mapHomologicalComplex_obj_X, Functor.mapHomologicalComplex_map_f]
  erw [Category.assoc]
  erw [← (SemilinearSections.evaluation.{c, v, max c v r} J B τ n).map_comp_assoc, t.summand]
  rw [(SemilinearSections.evaluation.{c, v, max c v r} J B τ n).map_comp]
  have hn := (s.ordinaryEvaluation n).hom.naturality (tensorSummand.{c, v, r} J R P Q i j k h)
  dsimp only [Functor.comp_map] at hn
  rw [s.ordinaryComplexEvaluation_component]
  erw [Category.assoc, hn]
  erw [reassoc_of% (tensorSummand_map.{c, v, r} J (B n)
    ((s.ordinaryComplexEvaluation n).hom.app P)
    ((s.ordinaryComplexEvaluation n).hom.app Q) i j k h)]
  erw [(t.finiteModel n).summand P Q i j k h]
  simp only [s.ordinaryComplexEvaluation_component]
  have ho := t.ordinary_evaluation n (P.X i) (Q.X j)
  rw [← a.tensorEvaluationModel_ordinary] at ho
  -- Cancel the ordinary comparison maps to orient the summand identity.
  have hi := congrArg (fun f ↦
    ((a.tensorEvaluationModel n).ordinary (s.ordinary.obj (P.X i))
      (s.ordinary.obj (Q.X j))).inv ≫
      (SemilinearSections.evaluation.{c, v, max c v r} J B τ n).map
        (t.ordinary (P.X i) (Q.X j)).inv ≫ f ≫
      ((t.finiteModel n).ordinary (P.X i) (Q.X j)).inv) ho
  simp only [Category.assoc,
    ← (SemilinearSections.evaluation.{c, v, max c v r} J B τ n).map_comp_assoc,
    Iso.inv_hom_id] at hi
  erw [(SemilinearSections.evaluation.{c, v, max c v r} J B τ n).map_id] at hi
  have hi' := congrArg
    (fun f ↦ f ≫ (s.levels n).model.E.map
      (tensorSummand.{c, v, r} J R P Q i j k h)) hi
  simp only [Category.assoc, Category.id_comp, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id] at hi'
  erw [hi']
  rfl



set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem reductionTensorOnRepresentatives
    (s : Reduction.{c, v, r} J R B τ q) (a : Data.{c, v, r} J B τ)
    (t : TensorReduction.{c, v, r} s a) (n : ℕ)
    (P Q : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q)
    (fP : flatTerms.{c, v, r} J R P) (fQ : flatTerms.{c, v, r} J R Q) :
    (s.evaluation n).hom.app (t.ambient.tensor.obj
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        (t.finiteBalance n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      (e.{c, v, max c v r} J B τ n).map
          (t.balance.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        (a.tensorEvaluation n).hom.app
          (s.functor.obj (DerivedCategory.Q.obj P), s.functor.obj (DerivedCategory.Q.obj Q)) ≫
        (a.levelClosed n).tensor.map
          (Prod.mkHom ((s.evaluation n).hom.app (DerivedCategory.Q.obj P))
            ((s.evaluation n).hom.app (DerivedCategory.Q.obj Q))) := by
  let F := SemilinearSections.evaluation.{c, v, max c v r} J B τ n
  let FH := F.mapHomologicalComplex (.up ℤ)
  let S := s.ordinary.mapHomologicalComplex (.up ℤ)
  let E := (s.levels n).model.E.mapHomologicalComplex (.up ℤ)
  let Tot := (totalTensor.{c, v, r} J R).obj (P, Q)
  let TotS := (totalTensor.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ)).obj (S.obj P, S.obj Q)
  have hSP := t.kflat P hP fP
  have hSQ := t.kflat Q hQ fQ
  have hEP := (t.finiteModel n).kflat P hP fP
  have hEQ := (t.finiteModel n).kflat Q hQ fQ
  have hFP := (a.tensorEvaluationModel n).kflat (S.obj P) hSP (t.flatTerms P fP)
  have hFQ := (a.tensorEvaluationModel n).kflat (S.obj Q) hSQ (t.flatTerms Q fQ)
  have hTot := coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ
  let i := tensorModelIso.{c, v, r} J R t.ambient t.ambientModels P Q hP hQ
  let k := tensorModelIso.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ) a.closed a.tensorModels
    (S.obj P) (S.obj Q) hSP hSQ
  let j := tensorModelIso.{c, v, r} J (B n) (a.levelClosed n) (a.levelTensorModels n)
    (E.obj P) (E.obj Q) hEP hEQ
  let kE := tensorModelIso.{c, v, r} J (B n) (a.levelClosed n) (a.levelTensorModels n)
    (FH.obj (S.obj P)) (FH.obj (S.obj Q)) hFP hFQ
  let fp := @asIso _ _ _ _ (s.epsilon.app P) (s.computes P hP)
  let fq := @asIso _ _ _ _ (s.epsilon.app Q) (s.computes Q hQ)
  let gp := scalarEpsilonIso.{c, v, r} (q n) (s.levels n) P hP
  let gq := scalarEpsilonIso.{c, v, r} (q n) (s.levels n) Q hQ
  let ep := F.mapDerivedCategoryFactors.app (S.obj P)
  let eq := F.mapDerivedCategoryFactors.app (S.obj Q)
  let eT := F.mapDerivedCategoryFactors.app (S.obj Tot)
  let eZ := F.mapDerivedCategoryFactors.app TotS
  let vm := t.balance.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
  let vn := (t.finiteBalance n).app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)
  let um := s.functor.mapIso i.symm ≪≫
    @asIso _ _ _ _ (s.epsilon.app Tot) (s.computes Tot hTot)
  let un := (s.levels n).T.mapIso i.symm ≪≫
    scalarEpsilonIso.{c, v, r} (q n) (s.levels n) Tot hTot
  let cm := k ≪≫ a.closed.tensor.mapIso (fp.symm.prod fq.symm) ≪≫ vm.symm ≪≫ um
  let cn := j ≪≫ (a.levelClosed n).tensor.mapIso (gp.symm.prod gq.symm) ≪≫ vn.symm ≪≫ un
  have hcm : cm.hom = DerivedCategory.Q.map (t.chain P Q) := by
    simpa only [cm, um, fp, fq, k, vm, i, S, Tot, Iso.trans_hom,
      Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom, Iso.app_inv, asIso_hom,
      Category.assoc] using t.representative P Q hP hQ fP fQ hTot
  have hcn : cn.hom = DerivedCategory.Q.map ((t.finiteModel n).chain P Q) := by
    simpa only [cn, un, gp, gq, j, vn, i, E, Tot, scalarEpsilonIso, Iso.trans_hom,
      Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom, Iso.app_inv, asIso_hom,
      Category.assoc] using (t.finiteModel n).derived P Q hP hQ fP fQ hTot
  refine tensor_reduction_from_model_squares
    (e.{c, v, max c v r} J B τ n) a.closed.tensor (a.levelClosed n).tensor
    (a.tensorEvaluation n) vm vn um un k j kE fp fq gp gq ep eq eT eZ cm cn
    ((s.evaluation n).hom.app (t.ambient.tensor.obj
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)))
    ((s.evaluation n).hom.app (DerivedCategory.Q.obj P))
    ((s.evaluation n).hom.app (DerivedCategory.Q.obj Q))
    (DerivedCategory.Q.map ((s.ordinaryComplexEvaluation n).hom.app Tot))
    (DerivedCategory.Q.map ((s.ordinaryComplexEvaluation n).hom.app P))
    (DerivedCategory.Q.map ((s.ordinaryComplexEvaluation n).hom.app Q))
    (DerivedCategory.Q.map ((a.tensorEvaluationModel n).chain (S.obj P) (S.obj Q)))
    (DerivedCategory.Q.map (FH.map (t.chain P Q)))
    (DerivedCategory.Q.map ((totalTensor.{c, v, r} J (B n)).map
      (Prod.mkHom ((s.ordinaryComplexEvaluation n).hom.app P)
        ((s.ordinaryComplexEvaluation n).hom.app Q))))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [cm, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom]
  · simp only [cn, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.symm_hom]
  · exact (a.tensorEvaluationModel n).derived (S.obj P) (S.obj Q) hSP hSQ
      (t.flatTerms P fP) (t.flatTerms Q fQ)
  · have hn := (s.evaluation n).hom.naturality i.inv
    have ht := s.evaluation_model n Tot
    have hr₀ := congrArg (fun f ↦ f ≫ (s.levels n).model.ε.app Tot) hn
    simp only [Functor.comp_map, Category.assoc] at hr₀
    have hr₁ := congrArg
      (fun f ↦ (e.{c, v, max c v r} J B τ n).map (s.functor.map i.inv) ≫ f) ht
    simpa only [um, un, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Iso.app_hom, scalarEpsilonIso, asIso_hom, Functor.map_comp, Category.assoc,
      F, eT] using hr₀.symm.trans hr₁
  · exact s.evaluation_model n P
  · exact s.evaluation_model n Q
  · rw [hcm]
    exact F.mapDerivedCategoryFactors.hom.naturality (t.chain P Q)
  · exact (tensorModelIso_naturality.{c, v, r} J (B n) (a.levelClosed n)
      (a.levelTensorModels n) (FH.obj (S.obj P)) (E.obj P)
      (FH.obj (S.obj Q)) (E.obj Q) hFP hEP hFQ hEQ
      ((s.ordinaryComplexEvaluation n).hom.app P)
      ((s.ordinaryComplexEvaluation n).hom.app Q)).symm
  · rw [hcn]
    simpa only [← Functor.map_comp, Category.assoc] using congrArg
      (fun f ↦ DerivedCategory.Q.map f) (reductionTensorChain s a t n P Q)

private def tensorEvaluationLeft
    (s : Reduction.{c, v, r} J R B τ q) (a : Data.{c, v, r} J B τ)
    (t : TensorReduction.{c, v, r} s a) (n : ℕ) :
    t.ambient.tensor ⋙ s.functor ⋙ e.{c, v, max c v r} J B τ n ⟶
      ((s.levels n).T.prod (s.levels n).T) ⋙ (a.levelClosed n).tensor :=
  Functor.whiskerLeft t.ambient.tensor (s.evaluation n).hom ≫ (t.finiteBalance n).hom

private def tensorEvaluationRight
    (s : Reduction.{c, v, r} J R B τ q) (a : Data.{c, v, r} J B τ)
    (t : TensorReduction.{c, v, r} s a) (n : ℕ) :
    t.ambient.tensor ⋙ s.functor ⋙ e.{c, v, max c v r} J B τ n ⟶
      ((s.levels n).T.prod (s.levels n).T) ⋙ (a.levelClosed n).tensor :=
  Functor.whiskerRight t.balance.hom (e.{c, v, max c v r} J B τ n) ≫
    Functor.whiskerLeft (s.functor.prod s.functor) (a.tensorEvaluation n).hom ≫
    Functor.whiskerRight ((s.evaluation n).hom.prod (s.evaluation n).hom)
      (a.levelClosed n).tensor

/-- Evaluation commutes with the normalized tensor balancing of a scalar reduction.
Source: Stacks, sites-cohomology.tex, lemma-pullback-tensor-product (Tag 07A4),
proof on flat K-flat representatives; Zheng Construction 4.1.
(blueprint: lem-pur-quotient-reduction-tensor-evaluation).

Proof: resolve each input by a flat-term K-flat complex P and Q. Scalar extension,
ordinary reduction and exact evaluation carry these representatives to K-flat
complexes. On the total tensor of their ordinary images, compare the two chain
maps using the summand equations of the three tensor comparison models. Each
summand square is exactly TensorReduction.ordinary_evaluation, with the degreewise
ordinaryComplexEvaluation isomorphisms inserted. Thus the chain maps agree, by
the coproduct universal property in each total degree. Localize this equality.
Replace the three localized chain maps by their representative equations, and
replace the reduction/evaluation comparison by Reduction.evaluation_model.
Cancel the invertible computation arrows for P, Q and their total tensor. This
gives the displayed identity on the two resolved inputs. Naturality of all
comparisons and the two resolution isomorphisms gives it on arbitrary inputs.
The argument uses flat-term resolutions, not flatness of the coefficient rings. -/
theorem reductionTensorEvaluation
    (s : Reduction.{c, v, r} J R B τ q) (a : Data.{c, v, r} J B τ)
    (t : TensorReduction.{c, v, r} s a) (n : ℕ)
    (M N : D.{c, v, max c v r} J R) :
    (e.{c, v, max c v r} J B τ n).map (t.balance.hom.app (M, N)) ≫
        (a.tensorEvaluation n).hom.app (s.functor.obj M, s.functor.obj N) ≫
        (a.levelClosed n).tensor.map
          (Prod.mkHom ((s.evaluation n).hom.app M) ((s.evaluation n).hom.app N)) =
      (s.evaluation n).hom.app (t.ambient.tensor.obj (M, N)) ≫
        (t.finiteBalance n).hom.app (M, N) := by
  obtain ⟨P, hP, fP, ⟨iP⟩⟩ := exists_kflat_representative.{c, v, r} J R M
  obtain ⟨Q, hQ, fQ, ⟨iQ⟩⟩ := exists_kflat_representative.{c, v, r} J R N
  let L := tensorEvaluationLeft s a t n
  let U := tensorEvaluationRight s a t n
  have hrep : L.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      U.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
    reductionTensorOnRepresentatives s a t n P Q hP hQ fP fQ
  change U.app (M, N) = L.app (M, N)
  apply (cancel_epi
    ((t.ambient.tensor ⋙ s.functor ⋙ e.{c, v, max c v r} J B τ n).map
      (iP.prod iQ).hom)).1
  rw [U.naturality, L.naturality, hrep]

end SheafOfModules.QuotientDiagramProjection
