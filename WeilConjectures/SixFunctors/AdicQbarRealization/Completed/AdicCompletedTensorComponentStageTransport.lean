/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorStageComponent
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorFiniteScalarSquare
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorStageNaturality

/-! # Naturality of the explicit completed tensor components

Source: BS Remark 6.8.15; HRS Lemma 7.9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.AdicQbarRealization.ordinary
  WeilConjectures.rationalDerivedTensor
  WeilConjectures.commonStageTensorComparison WeilConjectures.operationStageTransitionIso
  WeilConjectures.sfRationalScalarExtension
  WeilConjectures.sfConstructibleIntegralScalarExtension
  WeilConjectures.AdicQbarRealization.stageTensor
  WeilConjectures.AdicQbarRealization.completedTensorStageComponent
  CategoryTheory.ScalarLocalization.category

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  (R : LocallyFiniteAdicRealization.Realization l X)
  [∀ x : X, Invertible (l : X.residueField x)]
  (closed : CoefficientClosedStructure (ambientHom l X R))
  (models : CoefficientTensorModels.{u + 1, u + 1, u}
    (ProEt.topology X) (ring l X R) closed)

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.pairCategory
  generalAlgebraicallyClosedConstructibleCategory GeneralAlgebraicallyClosedCoefficients.Pair
  commonStageDerivedTensor
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5

private theorem whisker_app
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {F G : A ⥤ B} (e : F ≅ G) (H : B ⥤ C) (x : A) :
    (Functor.isoWhiskerRight e H).app x = H.mapIso (e.app x) := rfl

private theorem inclusion_comparison_app
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K L : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    (commonInclusionTensorComparison l (PadicAlgCl l) X E).app (K, L) =
      (commonInclusionTensorModel l (PadicAlgCl l) X E K L ≪≫
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E).mapIso
          ((rationalDerivedTensor l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).mapIso
            (Iso.prod
              ((operationStageTransitionIso l (PadicAlgCl l) X E E le_rfl ≪≫
                GeneralAlgebraicallyClosedCoefficients.unitor l (PadicAlgCl l) X E).app K)
              ((operationStageTransitionIso l (PadicAlgCl l) X E E le_rfl ≪≫
                GeneralAlgebraicallyClosedCoefficients.unitor l (PadicAlgCl l) X E).app
                  L)))).symm := by
  unfold commonInclusionTensorComparison
  rfl

private theorem inclusion_comparison_eq
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K L : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    (commonInclusionTensorComparison l (PadicAlgCl l) X E).app (K, L) =
      stageTensor l X (PadicAlgCl l) E K L := by
  rw [inclusion_comparison_app]
  apply (stageTensor_existsUnique l X (PadicAlgCl l) E K L).unique
  · unfold stageTensorFormula
    refine heq_of_eq ?_
    unfold commonInclusionTensorModel
    simp only [Functor.mapIso_trans, Iso.trans_assoc]
    dsimp only [Functor.id_obj, Functor.comp_obj, Functor.prod_obj]
    unfold commonStageDerivedTensor
    rfl
  · unfold stageTensor
    exact (stageTensor_existsUnique l X (PadicAlgCl l) E K L).exists.choose_spec

private theorem stage_component_formula
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (NE : CompletedTensorFiniteModel l X R closed models E)
    (K L : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    completedTensorStageComponent l X R closed models E NE K L =
      completedTensorIntegralComponent l X R closed models E NE K.obj L.obj ≪≫
        (ordinary l X R).mapIso (stageTensor l X (PadicAlgCl l) E K L) := by
  unfold completedTensorStageComponent
  rw [whisker_app, inclusion_comparison_eq]
  rfl

private theorem stage_component_hom_assoc
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (NE : CompletedTensorFiniteModel l X R closed models E)
    (K L : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    {Z : DerivedCategory (modules l X R)}
    (f : (ordinary l X R).obj ((commonStageDerivedTensor l (PadicAlgCl l) X).obj
      ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K,
       (GeneralAlgebraicallyClosedCoefficients.inclusion E).obj L)) ⟶ Z) :
    (completedTensorStageComponent l X R closed models E NE K L).hom ≫ f =
      (completedTensorIntegralComponent l X R closed models E NE K.obj L.obj).hom ≫
        (ordinary l X R).map (stageTensor l X (PadicAlgCl l) E K L).hom ≫ f := by
  rw [stage_component_formula]
  exact Category.assoc _ _ _

private theorem stage_iso_trans
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)] (S : StageSystem C)
    (A : S.PairCategory) {M N : I} (hA : A.stage ≤ M) (h : M ≤ N) :
    S.isoToStage A hA ≪≫ S.isoToStage ((S.ι M).obj (A.toStage hA)) h ≪≫
        (S.ι N).mapIso ((S.assoc hA h).app A.obj) =
      S.isoToStage A (hA.trans h) := by
  apply Iso.ext
  have hu : (S.T h).map ((S.assoc hA (le_refl M)).inv.app A.obj) =
      (S.assoc (le_refl M) h).inv.app (A.toStage hA) := by
    apply (cancel_epi ((S.assoc hA h).inv.app A.obj)).mp
    exact S.cocycle_inv hA (le_refl M) h A.obj
  change (StageSystem.PairCategory.mkHom M hA (le_refl M)
      ((S.assoc hA (le_refl M)).inv.app A.obj) : A ⟶ ⟨M, A.toStage hA⟩) ≫
    (StageSystem.PairCategory.mkHom N h (le_refl N)
      ((S.assoc h (le_refl N)).inv.app (A.toStage hA)) :
        (⟨M, A.toStage hA⟩ : S.PairCategory) ⟶ ⟨N, (S.T h).obj (A.toStage hA)⟩) ≫
    (StageSystem.PairCategory.mkHom N (le_refl N) (le_refl N)
      ((S.T (le_refl N)).map ((S.assoc hA h).hom.app A.obj)) :
        (⟨N, (S.T h).obj (A.toStage hA)⟩ : S.PairCategory) ⟶
          ⟨N, A.toStage (hA.trans h)⟩) =
    StageSystem.PairCategory.mkHom (X := A) (Y := ⟨N, A.toStage (hA.trans h)⟩)
      N (hA.trans h) (le_refl N)
      ((S.assoc (hA.trans h) (le_refl N)).inv.app A.obj)
  rw [← StageSystem.PairCategory.mkHom_tr (X := A) (Y := ⟨M, A.toStage hA⟩)
    (hX := hA) (hY := le_refl M) h ((S.assoc hA (le_refl M)).inv.app A.obj),
    StageSystem.PairCategory.mkHom_comp_mkHom,
    StageSystem.PairCategory.mkHom_comp_mkHom]
  congr 1
  simp only [StageSystem.tr, hu, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← S.cocycle_inv_assoc hA h (le_refl N)]
  simp [← Functor.map_comp]

private theorem transport_of_square
    {C D : Type*} [Category* C] [Category* D] (F G : C ⥤ D)
    {A B : C} (a : A ≅ B) (s : F.obj A ⟶ G.obj A) (t : F.obj B ⟶ G.obj B)
    (h : F.map a.hom ≫ t = s ≫ G.map a.hom) :
    s = F.map a.hom ≫ t ≫ G.map a.inv := by
  rw [← Category.assoc, h, Category.assoc, ← G.map_comp, a.hom_inv_id, G.map_id,
    Category.comp_id]

private theorem conjugated_transport
    {C D : Type*} [Category* C] [Category* D] (F G : C ⥤ D)
    {A B C₀ D₀ : C} (a : A ≅ B) (t : B ≅ C₀) (c : C₀ ≅ D₀)
    (s : F.obj B ⟶ G.obj B) (s' : F.obj C₀ ⟶ G.obj C₀)
    (s'' : F.obj D₀ ⟶ G.obj D₀)
    (ht : F.map t.hom ≫ s' = s ≫ G.map t.hom)
    (hc : F.map c.hom ≫ s'' = s' ≫ G.map c.hom) :
    F.map a.hom ≫ s ≫ G.map a.inv =
      F.map (a ≪≫ t ≪≫ c).hom ≫ s'' ≫ G.map (a ≪≫ t ≪≫ c).inv := by
  have htc : F.map (t.hom ≫ c.hom) ≫ s'' = s ≫ G.map (t.hom ≫ c.hom) := by
    rw [F.map_comp, G.map_comp, Category.assoc, hc, ← Category.assoc, ht]
    simp only [Category.assoc]
  have htci : s = F.map (t.hom ≫ c.hom) ≫ s'' ≫ G.map (c.inv ≫ t.inv) := by
    rw [← Category.assoc, htc, Category.assoc, ← G.map_comp]
    simp
  rw [htci]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.map_comp, Category.assoc]

set_option linter.unusedVariables false in
/-- The component computed at the compositum agrees with its computation at any
larger coefficient field, conjugated by the actual isoToStage maps.
Source: BS Definition 3.4.10 and Remark 6.8.15; HRS Proposition 5.2 and Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-component-stage-transport).

Proof: let E be the compositum of the input fields and enlarge E to L. Choose good
K-flat representatives of the two integral objects at E. Expand the representative
clauses of the finite models at E and L, replacing their completion comparisons by
the normalized cochain completion maps. The scalar counits on these representatives
are invertible. Cancel them using the K-flat model normalization. In bidegree (p,q)
the balance_sections equations identify both scalar tensor comparisons on the pure
section s tensor (x tensor y): both send it to the tensor of s tensor x and 1 tensor y.
The coefficient_scalar equation identifies the composite coefficient maps. The tensor
universal property and sheafification give equality in each bidegree; the totalization
coproduct injections then give equality of complex maps. Pass to the derived category
and transport by the good representative isomorphisms. The common_field equation of
R identifies its boundary comparisons with ordinary.map of the actual isoToStage
maps. Naturality and tower compatibility of the integral scalar tensor comparison,
and the normalized formula of stageTensor, identify the output comparison. The
existing natural inclusion comparison has that same formula: expand its component,
use functoriality of mapIso and associativity of isomorphism composition, and apply
uniqueness in stageTensor_existsUnique. Thus its component is precisely stageTensor.
Pasting with the two endpoint isoToStage maps in the definition of the common component gives
the displayed equation. Reflexive extensions retain their normalized scalar unit;
no nonzero object, nonempty scheme, or faithful coefficient extension is required. -/
theorem completedTensorCommonComponent_stage_transport
    (symmetry : @SymmetricCategory _ _ closed.monoidal)
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry)
    (P Q : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (hP : P.stage ≤ E) (hQ : Q.stage ≤ E) :
    let a := (GeneralAlgebraicallyClosedCoefficients.stageSystem l
      (PadicAlgCl l) X).isoToStage P hP
    let b := (GeneralAlgebraicallyClosedCoefficients.stageSystem l
      (PadicAlgCl l) X).isoToStage Q hQ
    (completedTensorCommonComponent l X R closed models N P Q).hom =
      (((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor).map
          (Prod.mkHom a.hom b.hom) ≫
        (completedTensorStageComponent l X R closed models E (N E)
          (P.toStage hP) (Q.toStage hQ)).hom ≫
        (commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R).map
          (Prod.mkHom a.inv b.inv) := by
  classical
  by_cases hPQ : P.stage = Q.stage
  · rcases P with ⟨D, K⟩
    rcases Q with ⟨D', L⟩
    dsimp only at hPQ
    subst D'
    let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X
    let G := commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R
    let a := Iso.prod (S.isoToStage ⟨D, K⟩ hP) (S.isoToStage ⟨D, L⟩ hQ)
    have ht := completedTensorStageComponent_scalar l X R closed models D E hP
      (N D) (N E) K L
    let F := ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor
    have ht' : F.map a.hom ≫
        (completedTensorStageComponent l X R closed models E (N E)
          ((⟨D, K⟩ : S.PairCategory).toStage hP)
          ((⟨D, L⟩ : S.PairCategory).toStage hQ)).hom =
        (completedTensorStageComponent l X R closed models D (N D) K L).hom ≫
          G.map a.hom := ht
    have heq := transport_of_square F G a
      (completedTensorStageComponent l X R closed models D (N D) K L).hom
      (completedTensorStageComponent l X R closed models E (N E)
        ((⟨D, K⟩ : S.PairCategory).toStage hP)
        ((⟨D, L⟩ : S.PairCategory).toStage hQ)).hom ht'
    rw [stage_component_formula] at heq
    rw [completedTensorCommonComponent]
    simp only [dite_true]
    exact heq
  · let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X
    let F := ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor
    let G := commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R
    let E₀ := Padic.finiteCoefficientCompositum l (PadicAlgCl l) P.stage Q.stage
    have hP₀ : P.stage ≤ E₀ :=
      ((Padic.finiteCoefficientFields_properties l (PadicAlgCl l)).1 P.stage Q.stage).1
    have hQ₀ : Q.stage ≤ E₀ :=
      ((Padic.finiteCoefficientFields_properties l (PadicAlgCl l)).1 P.stage Q.stage).2
    have h : E₀ ≤ E := by
      change P.stage.val ⊔ Q.stage.val ≤ E.val
      exact sup_le hP hQ
    let K := P.toStage hP₀
    let L := Q.toStage hQ₀
    let I₀ := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E₀
    let I := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E
    let a := Iso.prod (S.isoToStage P hP₀) (S.isoToStage Q hQ₀)
    let t := Iso.prod (S.isoToStage (I₀.obj K) h) (S.isoToStage (I₀.obj L) h)
    let c := (I.prod I).mapIso
      (Iso.prod ((S.assoc hP₀ h).app P.obj) ((S.assoc hQ₀ h).app Q.obj))
    have he : a ≪≫ t ≪≫ c = Iso.prod (S.isoToStage P hP) (S.isoToStage Q hQ) := by
      apply Iso.ext
      apply Prod.ext
      · exact congrArg Iso.hom (stage_iso_trans S P hP₀ h)
      · exact congrArg Iso.hom (stage_iso_trans S Q hQ₀ h)
    have ht := completedTensorStageComponent_scalar l X R closed models E₀ E h
      (N E₀) (N E) K L
    have hc := completedTensorStageComponent_naturality l X R closed models E (N E)
      (Prod.mkHom ((S.assoc hP₀ h).hom.app P.obj) ((S.assoc hQ₀ h).hom.app Q.obj))
    have heq := conjugated_transport F G a t c
      (completedTensorStageComponent l X R closed models E₀ (N E₀) K L).hom
      (completedTensorStageComponent l X R closed models E (N E)
        ((I₀.obj K).toStage h) ((I₀.obj L).toStage h)).hom
      (completedTensorStageComponent l X R closed models E (N E)
        (P.toStage hP) (Q.toStage hQ)).hom ht hc
    rw [he] at heq
    change (completedTensorCommonComponent l X R closed models N P Q).hom = _
    rw [completedTensorCommonComponent]
    simp only [dif_neg hPQ]
    simp only [F, G, a, S, E₀, K, L, stage_component_hom_assoc] at heq ⊢
    dsimp only [Iso.trans, Functor.mapIso, Iso.prod, Iso.symm,
      Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.prod_obj] at heq ⊢
    exact heq

end WeilConjectures.AdicQbarRealization
