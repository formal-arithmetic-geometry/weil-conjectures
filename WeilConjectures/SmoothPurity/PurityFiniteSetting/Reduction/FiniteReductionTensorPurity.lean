/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionTensorSource
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionThetaFactor
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionPositiveLineComparison
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalOrientationReduction

/-! # Reduction of the tensor form of smooth purity

Source: blueprint/latest, thm-pur-finite-reduction-of-purity, Steps 2–3.
(blueprint: lem-pur-finite-reduction-tensor-purity)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension Etale.derivedTensor Etale.upperStar Etale.lowerStar
  Scheme.sfIntrinsicDerivedEquivalence ProEtale.upperStar

namespace WeilConjectures.PurityFiniteSetting
attribute [local irreducible] finiteTensorCore
  finiteTensorPullbackComparison finiteReductionTensorInputComparison diagonalDualizingObject
  smoothPurityPullback diagonalDualizing
attribute [local implicit_reducible] finiteTensorReduction
private theorem tensor_inverse_square
    {C D : Type*} [Category C] [MonoidalCategory C]
    [Category D] [MonoidalCategory D]
    (F : C ⥤ D) (c : F.CoreMonoidal)
    {W L : C} {W' L' : D} (a : W ≅ L) (b : W' ≅ L')
    (w : F.obj W ⟶ W') (l : F.obj L ⟶ L')
    (h : F.map a.hom ≫ l = w ≫ b.hom)
    (M : C) (M' : D) (p : F.obj M ⟶ M') :
    F.map (M ◁ a.inv) ≫ (c.μIso M W).inv ≫ (p ⊗ₘ w) =
      (c.μIso M L).inv ≫ (p ⊗ₘ l) ≫ M' ◁ b.inv := by
  have hi : F.map a.inv ≫ w = l ≫ b.inv := by
    apply (cancel_mono b.hom).1
    rw [Category.assoc, ← h, ← F.map_comp_assoc, a.inv_hom_id, F.map_id]
    simp
  have hn : F.map (M ◁ a.inv) ≫ (c.μIso M W).inv =
      (c.μIso M L).inv ≫ F.obj M ◁ F.map a.inv := by
    apply (cancel_epi (c.μIso M L).hom).1
    rw [← Category.assoc, ← c.μIso_hom_natural_right, Category.assoc]
    simp
  rw [← Category.assoc, hn, Category.assoc]
  congr 1
  simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp,
    Category.comp_id, hi]

section Morphism
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

omit [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))] [IsSeparated (X ↘ Spec (.of P.field.k))]
  [f.IsOver (Spec (.of P.field.k))] in
private theorem inverseOrientation_reduction (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteReduction m hm hmn X).map (P.finitePurityInverseOrientation f d K) ≫
        P.finiteReductionTensorOmegaComparison m hm hmn f K =
      (P.finiteReductionTensorSourceComparison m hm hmn f d K).hom ≫
        (P.finiteReductionSetting m hm).finitePurityInverseOrientation f d
          ((P.finiteReduction m hm hmn Y).obj K) := by
  let := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of P.field.k))
  let := isNoetherian_of_locallyOfFiniteType (f ≫ (Y ↘ Spec (.of P.field.k)))
  let : HasCompactification f := inferInstance
  obtain ⟨e, _, _, _, hd⟩ := FiniteDiagonalReduction.diagonalOrientationReduction
    P m hm hmn d f (Y ↘ Spec (.of P.field.k))
  rw [P.finiteReduction_positiveLineComparison m hm hmn X d e] at hd
  let Q := P.finiteReductionSetting m hm
  let R := P.finiteTensorReduction m hm hmn X
  let E := (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor
  let E' := (Scheme.sfIntrinsicDerivedEquivalence X Q.Ring).functor
  let S : E ⋙ P.finiteReduction m hm hmn X ≅ R ⋙ E' :=
    ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
      (P.finiteReductionRingHom m hm hmn) X
  let M := (P.smoothPurityPullback f).obj
    ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K)
  let p₀ := P.finiteTensorPullbackComparison m hm hmn f
    ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K)
  let p₁ := (Q.smoothPurityPullback f).map
    (P.finiteReductionTensorInputComparison m hm hmn Y K).hom
  let a := P.diagonalDualizingObject d f (Y ↘ Spec (.of P.field.k))
  let b := Q.diagonalDualizingObject d f (Y ↘ Spec (.of P.field.k))
  let w := FiniteDiagonalReduction.omegaMap P m hm hmn f (Y ↘ Spec (.of P.field.k))
  let l := (P.finiteTensorPositiveReduction m hm hmn X d).hom
  let M' := (Q.smoothPurityPullback f).obj
    ((Scheme.sfIntrinsicDerivedEquivalence Y Q.Ring).inverse.obj
      ((P.finiteReduction m hm hmn Y).obj K))
  let c := P.finiteTensorCore m hm hmn X
  have ht := tensor_inverse_square R c a b w l hd M M' (p₀.hom ≫ p₁)
  have hp : (p₀.hom ≫ p₁) ⊗ₘ l = (p₀.hom ⊗ₘ l) ≫ p₁ ▷ _ := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]
  have hs := S.hom.naturality (M ◁ a.inv)
  change (P.finiteReduction m hm hmn X).map (E.map (M ◁ a.inv)) ≫ S.hom.app _ =
    S.hom.app _ ≫ E'.map (R.map (M ◁ a.inv)) at hs
  simp only [finitePurityInverseOrientation, finiteReductionTensorOmegaComparison,
    finiteReductionTensorSourceComparison, finiteTensorPurityTargetComparison,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, tensorIso_hom,
    smoothPurityTensorSource, smoothPurityTensor, ProEtale.derivedTensor, Iso.app_hom,
    curriedTensor_obj_map, curriedTensor_obj_obj, curriedTensor_map_app]
  have hn := congrArg (fun z ↦ z ≫
    E'.map (c.μIso M (P.diagonalDualizing f)).inv ≫
      E'.map ((p₀.hom ≫ p₁) ⊗ₘ w)) hs
  simp only [Category.assoc] at hn
  have hte := congrArg E'.map ht
  rw [hp] at hte
  simp only [Functor.map_comp, Category.assoc] at hte
  have hf := congrArg (fun z ↦ S.hom.app (M ⊗ P.diagonalTwist X d) ≫ z) hte
  simp only [Functor.map_comp, Category.assoc]
  exact hn.trans hf

/-- Reduction of the tensor form, before the twist reassociation.
Source: blueprint reduction Steps 2–3, inverse diagonal orientation and tensor mate
(blueprint: lem-pur-finite-reduction-tensor-purity).
Proof: use a bounded etale origin of K and a bounded flat representative. The
finite-adjoint-mate tensor equation identifies reduced theta with theta at level m;
its coefficient-unit map is the scalar-unit normalization. The last equation of
diagonalOrientationReduction identifies the reduced diagonal orientation through
the exceptional-unit and root-line comparisons. Its line comparison agrees with
finiteTensorPositiveReduction: on compatible primitive-root generators both are
the quotient root-power map, and their scalar-counit normalization determines the
derived map. Invert this orientation equation and tensor with the reduced pullback
of K. Naturality of the binary scalar tensorator gives the square for
1 tensor Pi inverse. Paste it with the theta square. The scalar and site comparison
units cancel by their triangle identities; uniqueness of the counit-normalized
exceptional comparison identifies the final map with the one displayed here.
Finally the characterization of smoothPurityTensorMap in every etale presentation
identifies these composites independently of the chosen origin. This proof concerns
only (1 tensor Pi inverse) followed by theta; it does not use tau or the full purity
reduction statement. -/
theorem finiteReduction_tensorPurity (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    (P.finiteReduction m hm hmn X).map (P.smoothPurityTensorMap f d K hK) ≫
        P.finiteReductionExceptionalComparison m hm hmn f d K hK =
      (P.finiteReductionTensorSourceComparison m hm hmn f d K).hom ≫
        (P.finiteReductionSetting m hm).smoothPurityTensorMap f d
          ((P.finiteReduction m hm hmn Y).obj K)
          (P.finiteReduction_preserves_ctf m hm hmn Y K hK) := by
  let Q := P.finiteReductionSetting m hm
  let K' := (P.finiteReduction m hm hmn Y).obj K
  have hK' := P.finiteReduction_preserves_ctf m hm hmn Y K hK
  obtain ⟨J, _, ⟨e⟩⟩ := (P.compositionInput_bounded K hK).plusEtaleOrigin
  obtain ⟨J', _, ⟨e'⟩⟩ := (Q.compositionInput_bounded K' hK').plusEtaleOrigin
  have hp : P.smoothPurityTensorMap f d K hK =
      P.finitePurityInverseOrientation f d K ≫ P.finitePurityTheta f K J e := by
    unfold smoothPurityTensorMap
    rw [(P.existsUnique_smoothPurityTensorMap f d K hK).exists.choose_spec J e]
    exact Functor.map_comp _ _ _
  have hq : Q.smoothPurityTensorMap f d K' hK' =
      Q.finitePurityInverseOrientation f d K' ≫ Q.finitePurityTheta f K' J' e' := by
    unfold smoothPurityTensorMap
    rw [(Q.existsUnique_smoothPurityTensorMap f d K' hK').exists.choose_spec J' e']
    exact Functor.map_comp _ _ _
  rw [hp, hq, Functor.map_comp, Category.assoc,
    P.finiteReduction_thetaFactor m hm hmn f d K hK J e J' e']
  rw [← Category.assoc,
    inverseOrientation_reduction P m hm hmn f d K, Category.assoc]

end Morphism
end WeilConjectures.PurityFiniteSetting
