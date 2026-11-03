/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEtaleSourceReassociation
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineRankOneSourceRealization
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.OrderedCoefficientActionPullback
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.OrderedTensorReassociationRealization
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackNormalization
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineDiagonalTensorCoordinates
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.ComparisonPullbackDerivedCoherence

/-! # Recursion of the ordinary counit coordinates

Source: projection-purity agreement, final paragraph: normalized last-line evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

attribute [local semireducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] iteratedAffineLine iteratedAffineLineProj
  etaleCategory proCategory sourceEtale

attribute [local semireducible] sourceWitness
attribute [local implicit_reducible] sourceWitness

private theorem actual_action_generic
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u}) (M : C A T) (d : ℕ) :
    coefficientActionComparison A N hA T M d =
      WeilConjectures.PurityFiniteSetting.projectionTensorActionGeneric (C A T)
        (fun i ↦ (comparison A T).obj (Etale.affineLinearBaseCoefficient A N hA T i))
        ((comparison A T).obj ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧))
        (coefficientUnitIso (ModuleCat.{u + 1} A) T)
        (fun i ↦ tensorComparison A T (Etale.affineLinearBaseCoefficient A N hA T i)
          ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)) M d := by
  induction d with
  | zero =>
    unfold coefficientActionComparison moduleRightUnit coefficientRightUnit
    rfl
  | succ d ih =>
    simp only [coefficientActionComparison,
      WeilConjectures.PurityFiniteSetting.projectionTensorActionGeneric, ih]
    unfold reassociate ProEtale.projectionActionAssociator AffineSpacePurity.tensorIso
    simp only [Functor.mapIso_refl, Iso.trans_refl]
    rfl

private theorem ordered_action_natural
    {B : Type*} [Category B] [MonoidalCategory B]
    (L : ℕ → B) (W : B) (z : L 0 ≅ 𝟙_ B)
    (s : ∀ n, L (n + 1) ≅ L n ⊗ W) {M M' : B} (f : M ⟶ M') (n : ℕ) :
    f ▷ L n ≫
        (WeilConjectures.PurityFiniteSetting.projectionTensorActionGeneric B L W z s M' n).hom =
      (WeilConjectures.PurityFiniteSetting.projectionTensorActionGeneric B L W z s M n).hom ≫
        (action ((curriedTensor B).flip.obj W) n).map f := by
  induction n with
  | zero =>
    change f ▷ L 0 ≫ (M' ◁ z.hom ≫ (ρ_ M').hom) =
      (M ◁ z.hom ≫ (ρ_ M).hom) ≫ f
    rw [← whisker_exchange_assoc, rightUnitor_naturality, Category.assoc]
  | succ n ih =>
    change f ▷ L (n + 1) ≫ (M' ◁ (s n).hom ≫
      (α_ M' (L n) W).inv ≫
      (WeilConjectures.PurityFiniteSetting.projectionTensorActionGeneric
        B L W z s M' n).hom ▷ W) =
      (M ◁ (s n).hom ≫ (α_ M (L n) W).inv ≫
        (WeilConjectures.PurityFiniteSetting.projectionTensorActionGeneric
          B L W z s M n).hom ▷ W) ≫
        (action ((curriedTensor B).flip.obj W) n).map f ▷ W
    rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
      ← comp_whiskerRight, ih, comp_whiskerRight]
    simp only [Category.assoc]

private theorem actual_action_natural
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u})
    {M M' : C A T} (f : M ⟶ M') (n : ℕ) :
    f ▷ (comparison A T).obj (Etale.affineLinearBaseCoefficient A N hA T n) ≫
        (coefficientActionComparison A N hA T M' n).hom =
      (coefficientActionComparison A N hA T M n).hom ≫
        (action ((tensor A T).flip.obj
          ((comparison A T).obj ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧))) n).map f := by
  rw [actual_action_generic, actual_action_generic]
  exact ordered_action_natural
    (fun i ↦ (comparison A T).obj (Etale.affineLinearBaseCoefficient A N hA T i))
    ((comparison A T).obj ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧))
    (coefficientUnitIso (ModuleCat.{u + 1} A) T)
    (fun i ↦ tensorComparison A T (Etale.affineLinearBaseCoefficient A N hA T i)
      ((Etale.ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)) f n

private theorem pro_whisker_left
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (M : C A T) {V W : C A T} (v : V ⟶ W) :
    ((tensor A T).obj M).map v = M ◁ v := rfl

private theorem tensor_iso_trans
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {M M' M'' W W' W'' : C A X}
    (e : M ≅ M') (e' : M' ≅ M'') (w : W ≅ W') (w' : W' ≅ W'') :
    tensorIso A X e w ≪≫ tensorIso A X e' w' =
      tensorIso A X (e ≪≫ e') (w ≪≫ w') := by
  apply Iso.ext
  simp only [Iso.trans_hom, pro_tensor_iso_hom, tensorHom_comp_tensorHom]

private theorem tensor_iso_symm
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {M M' W W' : C A X} (e : M ≅ M') (w : W ≅ W') :
    (tensorIso A X e w).symm = tensorIso A X e.symm w.symm := by
  apply Iso.ext
  apply (cancel_epi (tensorIso A X e w).hom).1
  rw [Iso.symm_hom, Iso.hom_inv_id, ← Iso.trans_hom, tensor_iso_trans]
  simp only [Iso.self_symm_id]
  simp [AffineSpacePurity.tensorIso]

private theorem pro_action_reassociation
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA) {X B Y : Scheme.{u}}
    (f : X ⟶ B) (g : B ⟶ Y) (hB : IsUnit (N : Γ(B, ⊤)))
    (T : C A X)
    (eL : (comparison A X).obj ((Etale.ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) ≅ T)
    (K : C A Y) (n : ℕ) :
    coefficientActionComparison A N hA X ((inverseImage A (f ≫ g)).obj K) (n + 1) ≪≫
        tensorReassociation A f g
          ((comparison A B).obj ((Etale.ordinaryFiniteLine A N hA B)⟦(2 : ℤ)⟧))
          ((comparison A X).obj ((Etale.ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧))
          T (line_pullback_iso A N hA t f hB) eL K n =
      tensor_source_reassociation A f g
        (Etale.affineLinearBaseCoefficient A N hA B n)
        (Etale.affineLinearBaseCoefficient A N hA X n)
        ((Etale.ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) T
        (coefficient_pullback_iso A N hA t f hB n) eL K ≪≫
        tensorIso A X
          ((inverseImage A f).mapIso
            (coefficientActionComparison A N hA B ((inverseImage A g).obj K) n))
          (Iso.refl T) := by
  let M := (inverseImage A g).obj K
  let M₀ := (inverseImage A (f ≫ g)).obj K
  let W := (comparison A B).obj ((Etale.ordinaryFiniteLine A N hA B)⟦(2 : ℤ)⟧)
  let W' := (comparison A X).obj ((Etale.ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)
  let F := (tensor A X).flip.obj W'
  let i := (inverseImageComp A f g).app K
  let v := coefficient_pullback_iso A N hA t f hB n
  let δ := inverseImageTensorIso A f M
    ((comparison A B).obj (Etale.affineLinearBaseCoefficient A N hA B n))
  let a := coefficientActionComparison A N hA B M n
  let a' := coefficientActionComparison A N hA X ((inverseImage A f).obj M) n
  let a₀ := coefficientActionComparison A N hA X M₀ n
  let p := actionPullbackIso ((tensor A B).flip.obj W) F (inverseImage A f)
    (fun J ↦ inverseImageTensorIso A f J W ≪≫
      tensorIso A X (Iso.refl _) (line_pullback_iso A N hA t f hB)) M n
  have hn : tensorIso A X i (Iso.refl _) ≪≫ a' = a₀ ≪≫ (action F n).mapIso i := by
    apply Iso.ext
    have h := actual_action_natural A N hA X i.hom n
    simp only [Iso.trans_hom, pro_tensor_iso_hom, Iso.refl_hom, tensorHom_id,
      Functor.mapIso_hom, M, M₀, F, W', a', a₀, Functor.comp_obj] at h ⊢
    with_unfolding_all exact h
  have hp : a' ≪≫ p.symm =
      (tensorIso A X (Iso.refl _) v).symm ≪≫ δ.symm ≪≫ (inverseImage A f).mapIso a := by
    have h := congrArg
      (fun z ↦ (δ ≪≫ tensorIso A X (Iso.refl _) v).symm ≪≫ z ≪≫ p.symm)
      (AlgebraicGeometry.ProEtale.AffineOrderedIntegration.coefficient_action_pullback A N hA t f hB M n)
    simpa only [δ, v, p, a, a', F, W, W', Iso.trans_symm, Iso.trans_assoc,
      Iso.symm_self_id_assoc, Iso.self_symm_id, Iso.trans_refl, Iso.refl_trans] using h.symm
  rw [tensor_iso_symm] at hp
  have hi : a₀ ≪≫ (action F n).mapIso i ≪≫ p.symm =
      tensorIso A X i v.symm ≪≫ δ.symm ≪≫ (inverseImage A f).mapIso a := by
    rw [← Iso.trans_assoc, ← hn, Iso.trans_assoc, hp]
    rw [← Iso.trans_assoc, tensor_iso_trans]
    simp -implicitDefEqProofs only [Iso.refl_symm, Iso.refl_trans]
    erw [Iso.trans_refl]
  change _ = _
  simp only [coefficientActionComparison, tensorReassociation, tensor_source_reassociation,
    reassociate, ProEtale.projectionActionAssociator]
  simp only [Iso.trans_assoc, tensor_iso_trans, Iso.refl_trans, Iso.trans_refl]
  rw [hi]

private theorem realizedTensorComparison_trans
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K K' : C A Y)
    (Ke : Etale.DerivedCategoryModule A Y) (W : Etale.DerivedCategoryModule A X)
    (e : (comparison A Y).obj Ke ≅ K) (e' : K ≅ K') :
    realizedTensorComparison A f K' Ke W (e ≪≫ e') =
      realizedTensorComparison A f K Ke W e ≪≫
        tensorIso A X ((inverseImage A f).mapIso e') (Iso.refl _) := by
  apply Iso.ext
  simp only [realizedTensorComparison_hom, Iso.trans_hom, pro_tensor_iso_hom,
    Iso.refl_hom, tensorHom_id, Functor.mapIso_hom, Functor.map_comp,
    comp_whiskerRight, Category.assoc]

private theorem source_comparison_succ
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : D P Y) (n : ℕ) :
    sourceComparison P Y K (n + 1) =
      (coefficientActionComparison (AffineLinePurity.Ring P) (exponent P)
        (annihilates P) (iteratedAffineLine Y (n + 1))
        ((inverseImage (AffineLinePurity.Ring P)
          (iteratedAffineLineProj Y (n + 1))).obj K) (n + 1)).symm := by
  apply Iso.ext
  have h := (sourceComparison_existsUnique P Y K (n + 1)).exists.choose_spec
  unfold orderedSource projectionSourceObject twistAction at h ⊢
  exact eq_of_heq h

private theorem source_reassociation_succ
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) (K : D P Y) (n : ℕ) :
    sourceReassociation P Y aY K (n + 1) =
      tensorReassociation (AffineLinePurity.Ring P) (lastProjection Y (n + 1))
        (iteratedAffineLineProj Y (n + 1))
        (shiftedLine P (iteratedAffineLine Y (n + 1)))
        (shiftedLine P (iteratedAffineLine Y (n + 2)))
        (AffineLinePurity.coefficient P.coefficients.l P.extension (P.level - 1)
          (iteratedAffineLine Y (n + 1)) P.level (annihilates P))
        (shiftedLinePullback P (lastProjection Y (n + 1)) (towerBase aY (n + 1)))
        (lineCoefficientIso P (iteratedAffineLine Y (n + 1)) (towerBase aY (n + 1))).symm
        K (n + 1) := by
  unfold sourceReassociation
  apply Iso.ext
  have h := (sourceReassociation_existsUnique P Y aY K (n + 1)).exists.choose_spec
  unfold orderedSource lineSource twistAction at h ⊢
  exact eq_of_heq h

private theorem source_realization_succ
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : D P Y) (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K) (n : ℕ) :
    sourceRealization P Y K Ke eK (n + 1) =
      realizedTensorComparison (AffineLinePurity.Ring P) (iteratedAffineLineProj Y (n + 1))
        K Ke (etaleCoefficient P Y (n + 1)) eK ≪≫
      coefficientActionComparison (AffineLinePurity.Ring P) (exponent P)
        (annihilates P) (iteratedAffineLine Y (n + 1))
        ((inverseImage (AffineLinePurity.Ring P)
          (iteratedAffineLineProj Y (n + 1))).obj K) (n + 1) := by
  unfold sourceRealization realizeTensorSource
  rw [source_comparison_succ, Iso.symm_symm_eq]

/-- Realizing the ordinary last-line tensor reassociation gives the specified pro-etale
source reassociation. This is an equality before applying compact support or any counit.
Source: projection-purity agreement, final paragraph, canonical reassociations.
(blueprint: lem-pur-affine-ordered-source-reassociation-realization).

Proof: replace sourceReassociation by its uniquely specified raw tensor map, using its
HEq characterization. Expand sourceRealization into realizedTensorComparison followed
by inverse sourceComparison. Expand the last-line witness into sourceComparison for the
chart coefficient. The comparison of the ordered coefficient action with its tensor
source identifies the initial unit and each shifted-line factor. Naturality of the
pullback/tensor site comparison moves eK past these factors. Its composition law
identifies the total pullback with the two successive pullbacks. The recursive coefficient
pullback is compatible with the unit and each tensor step. Tensor associativity and its
naturality identify the remaining factors with etaleSourceReassociation, including
the inverse chart-coefficient comparison. Cancel the adjacent inverse comparison maps.
All these operations concern sources only; no trace or counit is used. -/
theorem sourceReassociation_realization
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    (sourceReassociation P Y aY K.obj (d + 1)).hom ≫
      (AffineLineEvaluation.lineWitness P (iteratedAffineLine Y (d + 1))
        ((orderedSource P Y (d + 1)).obj K.obj) (sourceEtale P Y Ke (d + 1))
        (source_applicability P Y aY K Ke hKe eK (d + 1)).2
        (sourceRealization P Y K.obj Ke eK (d + 1))).iso.inv =
    (sourceRealization P Y K.obj Ke eK (d + 2)).inv ≫
      (comparison (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 2))).map
        (etaleSourceReassociation P Y aY Ke d).hom := by
  let A := AffineLinePurity.Ring P
  let B := iteratedAffineLine Y (d + 1)
  let X := iteratedAffineLine Y (d + 2)
  let q := lastProjection Y (d + 1)
  let f := iteratedAffineLineProj Y (d + 1)
  let V := Etale.affineLinearBaseCoefficient A (exponent P) (annihilates P) B (d + 1)
  let V' := Etale.affineLinearBaseCoefficient A (exponent P) (annihilates P) X (d + 1)
  let L := (Etale.ordinaryFiniteLine A (exponent P) (annihilates P) X)⟦(2 : ℤ)⟧
  let J := AffineLinePurity.etaleCoefficient P.coefficients.l P.extension
    (P.level - 1) B P.level (annihilates P)
  have hB : IsUnit (exponent P : Γ(B, ⊤)) :=
    affineTracePullbackInvertible (exponent P) f (exponentUnit P Y aY)
  let eV := Etale.vectorIntegrationBaseCoefficientPullback A (exponent P) (annihilates P)
    (transport P) q hB (d + 1)
  let eL : L ≅ J :=
    (eqToIso (AffineLinePurity.etaleCoefficient_eq P.coefficients.l P.extension
      (P.level - 1) B P.level (annihilates P)) ≪≫
      Etale.ordinaryFiniteShiftedLinePullback A (exponent P) (annihilates P)
        (transport P) (ProjectiveLine.affineChart B)
        (affineTraceProjectiveInvertible (exponent P) B hB)).symm
  let R := realizedTensorComparison A f K.obj Ke V eK
  let a := coefficientActionComparison A (exponent P) (annihilates P) B
    ((inverseImage A f).obj K.obj) (d + 1)
  have hl : (lineCoefficientIso P B (towerBase aY (d + 1))).symm =
      (comparison A X).mapIso eL := by
    rw [line_coefficient_iso]
    simp only [eL, eqToIso_refl, Iso.refl_trans, Functor.mapIso_symm]
    rfl
  have hw : shiftedLinePullback P q (towerBase aY (d + 1)) =
      line_pullback_iso A (exponent P) (annihilates P) (transport P) q hB := by
    unfold shiftedLinePullback line_pullback_iso comparedLinePullback
    rfl
  have ho : etaleSourceReassociation P Y aY Ke d =
      AlgebraicGeometry.ProEtale.AffineOrderedIntegration.ordinary_tensor_reassociation A q f V V' L J eV eL Ke := by
    unfold etaleSourceReassociation ordinary_tensor_reassociation ordinary_binary_reassociation
    rfl
  have ha := pro_action_reassociation A (exponent P) (annihilates P) (transport P)
    q f hB ((comparison A X).obj J) ((comparison A X).mapIso eL) K.obj (d + 1)
  have ht := AlgebraicGeometry.ProEtale.AffineOrderedIntegration.realized_tensor_reassociation A q f V V' L J eV eL K.obj Ke eK
  have hs : sourceRealization P Y K.obj Ke eK (d + 2) ≪≫
      sourceReassociation P Y aY K.obj (d + 1) =
    (comparison A X).mapIso (etaleSourceReassociation P Y aY Ke d) ≪≫
      (AffineLineEvaluation.lineWitness P B ((orderedSource P Y (d + 1)).obj K.obj)
        (sourceEtale P Y Ke (d + 1))
        (source_applicability P Y aY K Ke hKe eK (d + 1)).2
        (sourceRealization P Y K.obj Ke eK (d + 1))).iso := by
    rw [source_realization_succ, source_reassociation_succ, line_witness_iso,
      source_realization_succ, hl, hw, ho]
    rw [realizedTensorComparison_trans]
    have hc := congrArg
      (fun z ↦ realizedTensorComparison A (q ≫ f) K.obj Ke (V' ⊗ L) eK ≪≫ z) ha
    simp -implicitDefEqProofs only [coefficient_pullback_iso, V, V', L, eV] at hc
    simp -implicitDefEqProofs only [← Iso.trans_assoc] at hc
    erw [ht] at hc
    simp only [Iso.trans_assoc] at hc ⊢
    with_unfolding_all exact hc
  have hh := congrArg
    (fun z ↦ (sourceRealization P Y K.obj Ke eK (d + 2)).symm ≪≫ z ≪≫
      (AffineLineEvaluation.lineWitness P B ((orderedSource P Y (d + 1)).obj K.obj)
        (sourceEtale P Y Ke (d + 1))
        (source_applicability P Y aY K Ke hKe eK (d + 1)).2
        (sourceRealization P Y K.obj Ke eK (d + 1))).iso.symm) hs
  have h' := congrArg Iso.hom hh
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id,
    Iso.trans_refl, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] using h'

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
