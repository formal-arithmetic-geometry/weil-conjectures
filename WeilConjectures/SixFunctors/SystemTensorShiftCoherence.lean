/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOperationShiftData
import WeilConjectures.SixFunctors.DiagramPullbackMonoidalShiftModels
import WeilConjectures.Algebra.Homology.DerivedTensorAdditiveConstraints

/-! # Coherence of the prescribed system tensor shifts

Source: Stacks 011G, 014E, 06YU, 0FPQ and 0FNH; the maps-used sentence of
blueprint sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open CategoryTheory.Functor

namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Zero/addition laws, associativity and Koszul symmetry for the fixed tensor.
Source: Stacks 0FPQ and 0FNH; the parent proof, Steps 4 and 6.
(blueprint: lem-pur-system-tensor-prescribed-shift-coherence).

Proof: specialize the diagram tensor model theorem to the quotient rings
R/t^(n+1) and their quotient transitions. On flat-term K-flat representatives
its first and second shift extractions have precisely the two generator
formulas characterizing tensorShifts. Full faithfulness of restriction to
resolving representatives identifies these natural comparisons with the
prescribed ones. Transport the diagram theorem's slotwise CommShift
structures along these equalities; this gives the two displayed families
and their zero/addition laws. Its extraction identity identifies the
simultaneous comparison with the expression t below. For reassociation,
use the unsigned chain associator; the two exponents agree by
bi+c(i+j)=cj+(b+c)i. Its normalization identifies the descended associator
with the actual systemClosed monoidal associator. For symmetry descend the
Koszul chain swap, with coefficient (-1)^(ij). The two shifted paths differ
by (-1)^(ab), since their remaining exponents differ by an even integer.
The chain formula commutes with every quotient transition. The fixed
K-flat comparisons and localization full faithfulness give the stated
model formula and the symmetry square for all derived objects. A further
flat-term K-flat resolution extends the model formula to arbitrary
K-flat representatives by cancellation of the resolving isomorphisms. -/
theorem systemTensorShiftCoherence (W : Scheme.{u}) :
    let t := fun a b : ℤ ↦
      isoWhiskerLeft (tensorShiftFirst (System l E W) a) ((tensorShifts l E).systemRight W b) ≪≫
        isoWhiskerRight ((tensorShifts l E).systemLeft W a) (shiftFunctor (System l E W) b) ≪≫
        isoWhiskerLeft (calculus l E W).systemClosed.tensor
          (shiftFunctorAdd (System l E W) a b).symm
    (∃ (s₁ : ∀ N : System l E W,
            ((Functor.curry.obj (calculus l E W).systemClosed.tensor).flip.obj N).CommShift ℤ)
          (s₂ : ∀ M : System l E W,
            ((Functor.curry.obj (calculus l E W).systemClosed.tensor).obj M).CommShift ℤ),
          (∀ (M N : System l E W) (r : ℤ),
            (Functor.commShiftIso _ (self := s₁ N) r).app M =
              ((tensorShifts l E).systemLeft W r).app (M, N)) ∧
          (∀ (M N : System l E W) (r : ℤ),
            (Functor.commShiftIso _ (self := s₂ M) r).app N =
              ((tensorShifts l E).systemRight W r).app (M, N))) ∧
        (∀ (M N H : System l E W) (a b c : ℤ),
        (calculus l E W).systemClosed.tensor.map
            (Prod.mkHom ((t a b).hom.app (M, N)) (𝟙 (H⟦c⟧))) ≫
          (t (a + b) c).hom.app
            ((calculus l E W).systemClosed.tensor.obj (M, N), H) ≫
          ((calculus l E W).systemClosed.monoidal.associator M N H).hom⟦(a + b) + c⟧' =
        ((calculus l E W).systemClosed.monoidal.associator (M⟦a⟧) (N⟦b⟧) (H⟦c⟧)).hom ≫
          (calculus l E W).systemClosed.tensor.map
            (Prod.mkHom (𝟙 (M⟦a⟧)) ((t b c).hom.app (N, H))) ≫
          (t a (b + c)).hom.app
            (M, (calculus l E W).systemClosed.tensor.obj (N, H)) ≫
          eqToHom (congrArg
            (fun n : ℤ ↦ ((calculus l E W).systemClosed.tensor.obj
              (M, (calculus l E W).systemClosed.tensor.obj (N, H)))⟦n⟧) (add_assoc a b c).symm)) ∧
        (∃ s : (calculus l E W).systemClosed.tensor ≅
      CategoryTheory.Prod.swap (System l E W) (System l E W) ⋙
        (calculus l E W).systemClosed.tensor,
    (∀ (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : systemKFlat l E W P) (hQ : systemKFlat l E W Q),
    ∃ α : (systemTotalTensor l E W).obj (P, Q) ≅
      (systemTotalTensor l E W).obj (Q, P),
      (∀ (i j : ℤ) (U : (ℕ × W.ProEt)ᵒᵖ)
        (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
        ((α.hom.f (i + j)).val.app U)
          (coefficientTensorGenerator.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf l E W) P Q i j (i + j) rfl U x y) =
        (i * j).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) Q P j i (i + j) (add_comm j i) U y x) ∧
      ((calculus l E W).systemTensorModel.iso
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
        P Q hP hQ).hom ≫ s.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      DerivedCategory.Q.map α.hom ≫
        ((calculus l E W).systemTensorModel.iso
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) (calculus l E W).systemClosed
          Q P hQ hP).hom) ∧
    ∀ (M N : System l E W) (a b : ℤ),
      (t a b).hom.app (M, N) ≫
          (s.hom.app (M, N))⟦a + b⟧' =
        (a * b).negOnePow • (s.hom.app (M⟦a⟧, N⟦b⟧) ≫
          (t b a).hom.app (N, M) ≫
          eqToHom (congrArg
            (fun n : ℤ ↦ ((calculus l E W).systemClosed.tensor.obj (N, M))⟦n⟧)
            (add_comm b a)))) := by
  sorry

end WeilConjectures.IntegralSystemRealization
