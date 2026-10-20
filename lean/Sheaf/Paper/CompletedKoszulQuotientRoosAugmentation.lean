/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W6
-/
module

public import Sheaf.Paper.KoszulReconstructionModels
public import Sheaf.Algebra.Homology.ExactProductsRoosComparison

/-! # The strict completed Koszul-to-quotient Roos augmentation

Source: Stacks Project, Tags 091N and 099M
(blueprint: lem-weil-pbc-completed-koszul-quotient-roos-augmentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The coefficient augmentation induces a natural chain map of the explicit Roos
models. It is a quasi-isomorphism on unbounded K-flat complexes and preserves the actual
zero-second-coordinate quotient unit.

Source: Stacks Project, Tags 091N, 099M; the strict augmentation part of blueprint
sec-proper-base-change/sk-thm-properbasechange, order 1248
(blueprint: lem-weil-pbc-completed-koszul-quotient-roos-augmentation).
Proof: augment the exterior Koszul complex on the powers a_i^(m+1) to A/I^(m+1).
Its degree-zero component is the quotient map and its negative components vanish.
These maps commute with the inverse diagonal Koszul transitions and quotient maps.
Sheafify and extend scalars to the completed ring. Finite coefficient identification
identifies the targets with the recorded finite coefficient module sheaves. Tensor
with C, form the maps of products, and take the induced maps of mapping fibres of
minus one-minus-transition; this constructs the stated natural chain map. The strict
augmentation cone is pro-zero in the derived category by Noetherian Koszul pro-zero
and the cofinality of generator-power ideals with I-powers. Constant sheafification is
exact and completed scalar extension is flat. Tensor by K-flat C preserves these
quasi-isomorphisms and derived-zero transition maps. Exact countable products identify
its Roos fibre with the derived inverse limit, which kills a pro-zero tower; the fibre
map is therefore a quasi-isomorphism. Every augmentation sends the exterior degree-zero
unit to the quotient of one. Taking products preserves this equation; the second
coordinate is zero throughout. This gives the asserted chain-level unit equation. -/
theorem completedKoszulQuotientRoosAugmentation
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    ∃ α : reconstructionKoszulFiberFunctor T d r a ⟶
        (completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ) ⋙
          ExactProductsRoos.fibre,
      (∀ (P : CochainComplex (CompletedAdicModules T d) ℤ),
        CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P →
          QuasiIso (α.app P)) ∧
      (∀ P : CochainComplex (CompletedAdicModules T d) ℤ,
        completedAdicKoszulUnitComplex T d r a P ≫ α.app P =
          (NatTrans.mapHomologicalComplex (reconstructionOrdinaryUnit T d) (.up ℤ)).app P ≫
            ExactProductsRoos.comparison.app
              (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj P)) := by
  sorry

end AlgebraicGeometry.Scheme
