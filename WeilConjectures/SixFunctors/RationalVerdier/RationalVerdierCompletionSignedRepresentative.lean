/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierTensorRoosSignedModel
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierCompletionChainNaturality

/-! # The signed completion square on good cochain representatives

Source: blueprint thm-coef-rational-verdier, paragraph 3, signed transposition.
(blueprint: lem-coef-rational-verdier-completion-signed-representative). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

attribute [local implicit_reducible] integralOperationsGoodLocalization
  integralOperationsTensorOnGood integralOperationsTensorComplexFunctor
  pullbackTensorSwap IntegralAmbient.tensorTower
  IntegralOnSlice.Site IntegralOnSlice.topology IntegralOnSlice.restrict IntegralOnSlice.ring
  PurCompactSupport.completed pullbackTensorReferenceTensor
attribute [local irreducible] IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso
  strictTensorSignedSwap pullbackTensorCalculus
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  pullbackTensorIntegralTensorModel pullbackTensorReferenceTensorModel
  integralCompletedTensorComparison integralCompletedTensor
  integralOperationsTensorTowerFunctor Functor.mapDerivedCategory
  coefficientSequenceLimit pullbackTensorBraiding

/-- The ambient completed swap is the strict-system signed swap transported through
its recorded completed tensor model. This construction uses no constructibility or
choice of ordinary tensor presentation.
Source: Stacks 06YL and 08TC; blueprint signed transposition paragraph.
(blueprint: lem-coef-rational-verdier-completion-signed-representative). -/
def completedSignedSwap (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    integralCompletedTensor l E X ≅ pullbackTensorSwap _ ⋙ integralCompletedTensor l E X :=
  (pullbackTensorIntegralTensorModel l E X) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((pullbackTensorCalculus l E X).reduction.prod
          (pullbackTensorCalculus l E X).reduction)
        (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X)
          (pullbackTensorCalculus l E X).systemClosed
          (pullbackTensorCalculus l E X).systemTensorModel))
      (coefficientSequenceLimit l E X) ≪≫
    Functor.isoWhiskerLeft (pullbackTensorSwap _)
      (pullbackTensorIntegralTensorModel l E X).symm

private theorem completedSignedSwap_hom_app
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (A B : DerivedCategory (integralTowerModules l E X)) :
    (completedSignedSwap l E X).hom.app (A, B) =
      (pullbackTensorIntegralTensorModel l E X).hom.app (A, B) ≫
        (coefficientSequenceLimit l E X).map
          ((pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology X))
            (coefficientSequenceCommRingSheaf l E X)
            (pullbackTensorCalculus l E X).systemClosed
            (pullbackTensorCalculus l E X).systemTensorModel).hom.app
              ((pullbackTensorCalculus l E X).reduction.obj A,
               (pullbackTensorCalculus l E X).reduction.obj B)) ≫
        (pullbackTensorIntegralTensorModel l E X).inv.app (B, A) := by
  rfl

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem conjugate_square
    {C : Type*} [Category* C] {A B A' B' U V : C}
    (c : A ≅ B) (c' : A' ≅ B') (r : U ≅ B) (r' : V ≅ B')
    (e : A ≅ U) (e' : A' ≅ V) (f : B ⟶ B') (b : U ⟶ V)
    (he : e = c ≪≫ r.symm) (he' : e' = c' ≪≫ r'.symm)
    (hf : f ≫ r'.inv = r.inv ≫ b) :
    f = c.inv ≫ (e.hom ≫ b ≫ e'.inv) ≫ c'.hom := by
  subst e e'
  have h := congrArg (fun k ↦ k ≫ r'.hom) hf
  simpa only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Iso.hom_inv_id, Category.comp_id, Category.id_comp] using h

-- Retain the existing theorem parameters although the proof needs no finite-type assumption.
set_option linter.unusedSectionVars false in
/-- On two flat-term K-flat complexes, the quotient-normalized completion map
intertwines a chain map with the Koszul pure-section formula and the actual ambient
completed signed swap. No ordinary derived presentation, datum, naturality hypothesis,
constructibility, scalar extension or inverse completion map occurs in this assertion.
Source: Stacks 06YL, 08TC; blueprint thm-coef-rational-verdier paragraph 3.
(blueprint: lem-coef-rational-verdier-completion-signed-representative).

Proof: the homogeneous formula determines s by the pure tensor generators and the
summand inclusions of direct-sum totalization. At every positive quotient the same
formula determines the strict-system braiding. The quotient coordinate of completion
sends x tensor y to their two quotient images, hence intertwines these signed swaps;
the coefficient sign is (-1)^(ij) on both sides. The shifted mapping-fiber coordinate
of completion is zero on both sides. The two mapping-fiber coordinates, and then all
product projections, jointly detect equality. The equalities commute with the strict
quotient transitions, so they give the whole Roos complex square. Localize this square;
the recorded tensor-model comparisons and reduction/limit adjunction identify its
completed side with completedSignedSwap. Zero complexes and the empty site obey the
same generator and zero-coordinate equations. -/
theorem completion_signed_representative
    (P Q : (integralOperationsGoodComplex l E X).FullSubcategory)
    (s : (constructibleTensorTotal l E X).obj (P.obj, Q.obj) ⟶
      (constructibleTensorTotal l E X).obj (Q.obj, P.obj))
    (hs : ∀ (i j : ℤ) (U : X.ProEtᵒᵖ)
      (x : (P.obj.X i).val.obj U) (y : (Q.obj.X j).val.obj U),
      (s.f (i + j)).val.app U (IntegralHom.totalPair.{u, u}
        X (completedIntegralCommRingSheafUnrestricted l E X) P.obj Q.obj i j U x y) =
        (i * j).negOnePow •
          (eqToHom (congrArg
            (fun k : ℤ ↦ ((constructibleTensorTotal l E X).obj (Q.obj, P.obj)).X k)
              (add_comm j i))).val.app U
            (IntegralHom.totalPair.{u, u} X
              (completedIntegralCommRingSheafUnrestricted l E X) Q.obj P.obj j i U y x)) :
    DerivedCategory.Q.map s ≫
        DerivedCategory.Q.map ((completionChain D l hl X E).app (Q.obj, P.obj)) =
      DerivedCategory.Q.map ((completionChain D l hl X E).app (P.obj, Q.obj)) ≫
        (integralCompletedTensorComparison l E X).inv.app (P, Q) ≫
        (completedSignedSwap l E X).hom.app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (integralCompletedTensorComparison l E X).hom.app (Q, P) := by
  have ht : (IntegralOnSlice.tower l E X none).map s ≫
      (IntegralAmbient.tensorTowerIso l E X).hom.app (Q.obj, P.obj) =
    (IntegralAmbient.tensorTowerIso l E X).hom.app (P.obj, Q.obj) ≫
      strictTensorSignedSwap l E X P.obj Q.obj := by
    apply NatTrans.ext
    funext n
    exact tensor_tower_signed_coordinate l E X P.obj Q.obj s hs n.unop
  have hc := completion_natural_of_tower_square D l hl X E P.obj Q.obj s
    (strictTensorSignedSwap l E X P.obj Q.obj) ht
  have hd := congrArg DerivedCategory.Q.map hc
  simp only [Functor.map_comp] at hd
  have hm := tensor_roos_signed_model l E X P Q
  have hnorm : pullbackTensorIntegralTensorNormalization l E X
      (pullbackTensorIntegralTensorModel l E X) := by
    unfold pullbackTensorIntegralTensorModel pullbackTensorUniqueChoice
    exact (pullbackTensorIntegralTensorModel_existsUnique l E X).exists.choose_spec
  have hPQ := hnorm P Q
  have hQP := hnorm Q P
  have hb := conjugate_square
    ((integralCompletedTensorComparison l E X).app (P, Q))
    ((integralCompletedTensorComparison l E X).app (Q, P))
    (pullbackTensorReferenceTensorModel l E X P Q)
    (pullbackTensorReferenceTensorModel l E X Q P)
    ((pullbackTensorIntegralTensorModel l E X).app
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
    ((pullbackTensorIntegralTensorModel l E X).app
      (DerivedCategory.Q.obj Q.obj, DerivedCategory.Q.obj P.obj))
    _ _ hPQ hQP hm
  rw [hd]
  apply congrArg (fun f ↦
    DerivedCategory.Q.map ((completionChain D l hl X E).app (P.obj, Q.obj)) ≫ f)
  rw [completedSignedSwap_hom_app]
  simp only [integralOperationsTensorOnGood, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.ι_obj, Iso.app_hom, Iso.app_inv, Category.assoc] at hb ⊢
  convert hb using 1
  rfl

end WeilConjectures.RationalVerdier
