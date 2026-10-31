/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothOperationIdentificationSpecification

/-! # Shift and exactness data for common-stage smooth operations

Source: smooth-purity transport, Step 2, shift and exactness compatibility
(blueprint: lem-pur-common-stage-smooth-operation-shift).

This intermediate statement isolates the shift structures and all additive,
triangulated, transformation, and shift comparison equations required by the
full common-stage result.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CommonStageSmoothOperationIdentification

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]
  (S : ConstructibleExceptionalCoefficients.System.{u, v} l Ω D hl (f := f))
  [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (JX : FdCoefficientComparison l Ω X) (JY : FdCoefficientComparison l Ω Y)

/-- The shift, triangulated, and compatible-transformation equations for given
common-stage operation witnesses.
Source: smooth-purity transport Step 2, shift compatibility paragraph
(blueprint: lem-pur-common-stage-smooth-operation-identification).
The proof obtains the canonical commutation structures from the localized
operations and transports their equations through the comparison isomorphisms.
-/
theorem commonStageSmoothOperationShift
    (H G : StageSystem.CoherentExactMorphism
      (pbcScalarSystem l Ω Y dY.out iY.out) (pbcScalarSystem l Ω X dX.out iX.out))
    (RH : commonOperation.{u, v} l Ω D hl f d S false ⋙ JX.equivalence.functor ≅
      JY.equivalence.functor ⋙ H.base.functor)
    (RG : commonOperation.{u, v} l Ω D hl f d S true ⋙ JX.equivalence.functor ≅
      JY.equivalence.functor ⋙ G.base.functor) :
    ∃ (hS : (commonOperation.{u, v} l Ω D hl f d S false).CommShift ℤ)
      (gS : (commonOperation.{u, v} l Ω D hl f d S true).CommShift ℤ)
      (hP : H.base.functor.CommShift ℤ) (gP : G.base.functor.CommShift ℤ),
      (fun [_hs : (commonOperation.{u, v} l Ω D hl f d S false).CommShift ℤ]
        [_gs : (commonOperation.{u, v} l Ω D hl f d S true).CommShift ℤ]
        [_hp : H.base.functor.CommShift ℤ] [_gp : G.base.functor.CommShift ℤ] ↦
        (commonOperation.{u, v} l Ω D hl f d S false).Additive ∧
        (commonOperation.{u, v} l Ω D hl f d S true).Additive ∧
        (commonOperation.{u, v} l Ω D hl f d S false).IsTriangulated ∧
        (commonOperation.{u, v} l Ω D hl f d S true).IsTriangulated ∧
        H.base.functor.IsTriangulated ∧ G.base.functor.IsTriangulated ∧
        RH.hom.CommShift ℤ ∧ RG.hom.CommShift ℤ ∧
        (∀ θ : StageSystem.Morphism.Hom H.base G.base,
          (∀ E, @NatTrans.CommShift _ _ _ _ (H.base.Φ E) (G.base.Φ E)
            (θ.τ E) ℤ _ _ _ (H.commShift E) (G.commShift E)) →
          (StageSystem.Morphism.descNatTrans θ).CommShift ℤ ∧
          ∃ θs : commonOperation.{u, v} l Ω D hl f d S false ⟶
              commonOperation.{u, v} l Ω D hl f d S true,
            θs.CommShift ℤ ∧
            (∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
              JX.equivalence.functor.map (θs.app K) = RH.hom.app K ≫
                (StageSystem.Morphism.descNatTrans θ).app
                  (JY.equivalence.functor.obj K) ≫ RG.inv.app K)) ∧
        (∀ E (K : pbcStageCategory l Ω Y E) (n : ℤ),
          HEq (H.base.functor.map
              ((((pbcScalarSystem l Ω Y dY.out iY.out).ι E).commShiftIso n).hom.app K) ≫
            (H.base.functor.commShiftIso n).hom.app
              (((pbcScalarSystem l Ω Y dY.out iY.out).ι E).obj K))
            (((pbcScalarSystem l Ω X dX.out iX.out).ι E).map
              ((Functor.commShiftIso (H.base.Φ E) (self := H.commShift E) n).hom.app K) ≫
              (((pbcScalarSystem l Ω X dX.out iX.out).ι E).commShiftIso n).hom.app
                ((H.base.Φ E).obj K))) ∧
        (∀ E (K : pbcStageCategory l Ω Y E) (n : ℤ),
          HEq (G.base.functor.map
              ((((pbcScalarSystem l Ω Y dY.out iY.out).ι E).commShiftIso n).hom.app K) ≫
            (G.base.functor.commShiftIso n).hom.app
              (((pbcScalarSystem l Ω Y dY.out iY.out).ι E).obj K))
            (((pbcScalarSystem l Ω X dX.out iX.out).ι E).map
              ((Functor.commShiftIso (G.base.Φ E) (self := G.commShift E) n).hom.app K) ≫
              (((pbcScalarSystem l Ω X dX.out iX.out).ι E).commShiftIso n).hom.app
                ((G.base.Φ E).obj K))))
        (_hs := hS) (_gs := gS) (_hp := hP) (_gp := gP) := by
  sorry

end WeilConjectures.CommonStageSmoothOperationIdentification
