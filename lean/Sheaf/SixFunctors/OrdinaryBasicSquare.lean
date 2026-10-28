/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.IntegralOrdinaryExpressionReduction
import Sheaf.SixFunctors.IntegralOrdinaryCanonicalIsoSquare
import Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare
import Sheaf.SixFunctors.IntegralOrdinaryExchangeSquare
import Sheaf.SixFunctors.IntegralOrdinaryProjectionSquare
import Sheaf.SixFunctors.IntegralOrdinaryCompactificationSquares
import all Sheaf.SixFunctors.TensorAdjunctionReductionSquares
import all Sheaf.SixFunctors.OpenReconstructionEffectivity

/-! # Ordinary coefficient square for a basic pair

Ordinary coefficient compatibility for all basic structural generator pairs.
Source: blueprint `lem-sf-integral-basic-generator-square`.
(blueprint: lem-sf-integral-ordinary-basic-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem inverse_square {C D : Type*} [Category C] [Category D]
    (R : C ⥤ D) {K H : C} {M N : D} (r : K ≅ H) (s : M ≅ N)
    (q : R.obj K ⟶ M) (t : R.obj H ⟶ N)
    (h : q ≫ s.hom = R.map r.hom ≫ t) :
    t ≫ s.inv = R.map r.inv ≫ q := by
  apply (cancel_epi (R.map r.hom)).1
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [← R.map_comp_assoc, Iso.hom_inv_id, R.map_id, Category.id_comp]

/-- The ordinary coefficient square attached to any basic pair.

Source: blueprint `lem-sf-integral-basic-generator-square`; the square is obtained
by cases on the basic-pair witness. Canonical isomorphisms use their forward
square, and cancellation gives their inverse square. Proper units and counits
use the mate identities; open units and counits use the inverse-mate identities
and invertibility of the fixed open reduction. The remaining constructors use
the stated proper/open, exchange, projection and compactification squares.
The proof is independent of any
finite evaluation and works for the full basic-pair inductive family.
(blueprint: lem-sf-integral-ordinary-basic-square).
-/
theorem ordinaryBasicSquare
    (o : Operations l E) (a : AmbientModels l E o)
    {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    (K : ∀ i, Integral l E (X i).left)
    {W : Over B} {e t : Expression B I X W}
    {s : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K)}
    {r : e.ringedObj l E a.ringedModels K ⟶
      t.ringedObj l E a.ringedModels K}
    (h : BasicPair l E o a.compositors a.openComparisons a.canonicalBridge a.properOpen
      a.ringedModels a.ringedOpenComparisons a.ringedProperOpen
      ((inputReduction l E X).obj K) K e t s r) :
    e.ordinaryReduction l E o a K ≫ s =
      (calculus l E W.left).reduction.map r ≫ t.ordinaryReduction l E o a K := by
  cases h with
  | isoHom h => exact ordinaryCanonicalIsoSquare l E o a K _ _ _ _ h
  | isoInv h =>
    exact inverse_square _ _ _ _ _ (ordinaryCanonicalIsoSquare l E o a K _ _ _ _ h)
  | pullUnit f hf e =>
    exact GeneratorReduction.mate_unit_square (ringedAdj l E f.left)
      (o.direct f.left).adj (a.realizationModel.reductionPull f.left).symm
      (e.ordinaryReduction l E o a K)
  | pullCounit f hf _ =>
    have hm := GeneratorReduction.mate_counit_square (ringedAdj l E f.left)
      (o.direct f.left).adj (a.realizationModel.reductionPull f.left).symm
      (Expression.ordinaryReduction l E o a t K)
    simpa only [Expression.ordinaryReduction, ordinaryPushReduction, Category.assoc,
      Iso.symm_hom, Iso.symm_inv] using! hm
  | openUnit j qj e =>
    have hi : IsIso ((a.realizationModel.openReduction l E j.left).app
        (Expression.ringedObj l E e a.ringedModels K)) :=
      GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j.left _
    change IsIso (((mateEquiv (ringedOpenAdj l E j.left) (o.extension j.left).adj).symm
      (a.realizationModel.reductionPull j.left).hom).natTrans.app
        (Expression.ringedObj l E e a.ringedModels K)) at hi
    exact GeneratorReduction.inverse_mate_unit_square (ringedOpenAdj l E j.left)
      (o.extension j.left).adj (a.realizationModel.reductionPull j.left).hom
      (Expression.ordinaryReduction l E o a e K)
  | openCounit j qj _ =>
    have hi : IsIso ((a.realizationModel.openReduction l E j.left).app
        ((ringedPull l E j.left).obj (Expression.ringedObj l E t a.ringedModels K))) :=
      GeneratorReduction.fixedOpenReduction_isIso l E o a.realizationModel j.left _
    change IsIso (((mateEquiv (ringedOpenAdj l E j.left) (o.extension j.left).adj).symm
      (a.realizationModel.reductionPull j.left).hom).natTrans.app
        ((ringedPull l E j.left).obj
          (Expression.ringedObj l E t a.ringedModels K))) at hi
    have hm := GeneratorReduction.inverse_mate_counit_square (ringedOpenAdj l E j.left)
      (o.extension j.left).adj (a.realizationModel.reductionPull j.left).hom
      (Expression.ordinaryReduction l E o a t K)
    simpa only [Expression.ordinaryReduction, RealizationModel.openReduction,
      ringedOpenAdj, Operations.shriek, TwoSquare.natTrans, Functor.comp_obj,
      Functor.id_obj, Category.assoc] using! hm
  | properOpen k r p i w e => exact ordinaryProperOpenSquare l E o a K k r p i w e
  | exchange k r p i hr hp w e =>
    exact (ordinaryExchangeSquare l E o a K) k r p i hr hp w e
  | projection f hf e t => exact (ordinaryProjectionSquare l E o a K) f hf e t
  | compactExchange f f' cf cf' x y z wi wp hi e =>
    exact (ordinaryCompactificationSquares l E o a K).1 f f' cf cf' x y z wi wp hi e
  | compactProjection f cf e t =>
    exact (ordinaryCompactificationSquares l E o a K).2 f cf e t

end WeilConjectures.IntegralSystemRealization
