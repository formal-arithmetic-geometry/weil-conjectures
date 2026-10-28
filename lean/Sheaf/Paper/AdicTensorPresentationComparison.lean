/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicIntegralTensorCoordinates
public import Sheaf.Algebra.Homology.CochainTensorModelRigidity

/-! # Comparing normalized ordinary integral tensor presentations

Source: Stacks 07A4, 06YS; Bhatt--Scholze Definition 3.4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The unique comparison obtained by descending the two signed total-tensor models.
It is constructed by fully faithful restriction, without choosing an unproved witness.
Source: Stacks 07A4 and 06YS.
(blueprint: def-sf-adic-tensor-presentation-comparison). -/
def tensorPresentationComparison (N : ConstructibleTensorCompletionPresentation l E X) :
    N.tensor ≅ (pullbackTensorCalculus l E X).integralClosed.tensor := by
  let G := integralOperationsGoodComplex l E X
  let q := integralOperationsGoodLocalization l E X
  let i := ObjectProperty.lift
    (CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X) (R := completedIntegralCommRingSheafUnrestricted l E X) :
        ObjectProperty (CochainComplex (integralTowerModules l E X) ℤ)) G.ι
    (fun P ↦ P.property.1)
  let r := Functor.isoWhiskerLeft (i.prod i)
    (pullbackTensorCalculus l E X).integralTensorModel.comparison
  let T := (Functor.whiskeringLeft _ _
    (DerivedCategory (integralTowerModules l E X))).obj (q.prod q)
  let h := (SheafOfModules.cochain_tensor_model_rigidity (ProEt.topology X)
    (completedIntegralCommRingSheafUnrestricted l E X)).choose_spec.2.2
  let ff : T.FullyFaithful :=
    ((Functor.FullyFaithful.nonempty_iff_map_bijective T).2
      (fun U V ↦ h _ inferInstance U V)).some
  exact ff.preimageIso (N.model.symm ≪≫ r)

attribute [local irreducible] tensorPresentationComparison

/-- The quotient-completion map expressed on the fixed ambient ordinary tensor.
Source: Bhatt--Scholze Definition 3.4.10.
(blueprint: def-sf-adic-tensor-presentation-comparison). -/
def tensorPresentationCompletion (N : ConstructibleTensorCompletionPresentation l E X) :
    (pullbackTensorCalculus l E X).integralClosed.tensor ⟶ integralCompletedTensor l E X :=
  (tensorPresentationComparison l E X N).inv ≫ N.comparison

/-- Balanced scalar extension expressed on the fixed ambient ordinary tensor.
Source: BS Proposition 6.8.14 and Remark 6.8.15.
(blueprint: def-sf-adic-tensor-presentation-comparison). -/
def finiteAmbientScalarTensor (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : At l X R)
    (I : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : FiniteNormalization l X R A I) :
    (pullbackTensorCalculus l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) I) X).integralClosed.tensor
        ⋙
        pbcDerivedExtend (coefficientMap l X R I) ≅
    ((pbcDerivedExtend (coefficientMap l X R I)).prod
      (pbcDerivedExtend (coefficientMap l X R I))) ⋙ A.closed.tensor :=
  Functor.isoWhiskerRight (tensorPresentationComparison l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) I) X N.completion).symm
      (pbcDerivedExtend (coefficientMap l X R I)) ≪≫ N.ordinary

private theorem map_iso_cancellation {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {a b c : C} {d : D} (e : a ≅ b) (t : a ⟶ c)
    (s : d ⟶ F.obj a) :
    s ≫ F.map t = (s ≫ F.map e.hom) ≫ F.map (e.inv ≫ t) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc, e.hom_inv_id, F.map_id, Category.id_comp]

/-- Factor the finite tensor map into ordinary scalar tensor and integral completion.
Source: BS Definition 3.4.10 and Remark 6.8.15.
(blueprint: def-sf-adic-tensor-presentation-comparison). -/
theorem finiteIntegralTensorMap_factor (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : At l X R)
    (I : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : FiniteNormalization l X R A I)
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) I) X) :
    finiteIntegralTensorMap l X R A I N K L =
      (finiteAmbientScalarTensor l X R A I N).inv.app (K.obj, L.obj) ≫
        (pbcDerivedExtend (coefficientMap l X R I)).map
          ((tensorPresentationCompletion l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) I) X
              N.completion).app (K.obj, L.obj)) := by
  exact map_iso_cancellation (pbcDerivedExtend (coefficientMap l X R I))
    ((tensorPresentationComparison l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) I) X
        N.completion).app (K.obj, L.obj))
    (N.completion.comparison.app (K.obj, L.obj)) (N.ordinary.inv.app (K.obj, L.obj))

end WeilConjectures.AdicQbarRealization
