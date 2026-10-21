/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.AdicResidueLiftComparisons
public import Mathlib.CategoryTheory.CofilteredSystem

/-! # Mittag-Leffler for perfect finite-reduction Hom

Source: Stacks Project, Tags 09C5 and 09C6.
(blueprint: lem-sfb-adic-perfect-reduction-hom-ml).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

/-- The finite-reduction Hom tower from a constant perfect local model is Mittag-Leffler.
Source: Stacks Project, proetale.tex, Tags 09C5 and 09C6, the dual-complex calculation.
(blueprint: lem-sfb-adic-perfect-reduction-hom-ml).

Proof: let T be the completed realization of P and put H = RHom(T,M). Bounded
finite-projective duality identifies it with the tensor of M and the constant completed
dual P. Completeness of M implies completeness of H. Tensoring the quotient Roos
triangle with this bounded dual commutes with products (finite-projective terms are
idempotent summands of finite powers), so its reductions are precisely
RHom(T_n,M_n). Every M_n is constant with the same perfect value as T_n by hypothesis,
so these reductions are constant perfect complexes. Exact evaluation on the weakly
contractible slice identifies their H^0 sections with Hom(T_n,M_n): constant free
module sheaves are projective there, their finite summands are projective, and bounded
complexes of projectives are K-projective. These identifications commute with the actual
quotient maps, since the evaluation formula lambda tensor m maps p to lambda(p)m and
the dual differential commute with coefficient change. Apply 09C5 to the restriction
of H to constant coefficients, using the complete-coefficient equivalence. It yields
Mittag-Leffler for this actual Hom tower, with no compatible markings assumed. -/
theorem adicResidueHomTower_mittagLeffler
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (_hAffine : IsAffine
      ((AsSmall.down : coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).obj U).left)
    (_hU : AdicResidueSliceWeaklyContractible.{u, v} X U)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) (c d : ℤ)
    (_hc : P.IsStrictlyGE c) (_hd : P.IsStrictlyLE d)
    (_hP : ∀ q : ℤ, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q))
    (M : AdicResidueLocalDerived.{u, v} X J U)
    (_hM : CategoryTheory.ConstantCompletion.IsComplete
      (adicResidueLocalProjection.{u, v} X J U 0) M)
    (_hfinite : ∀ n : ℕ, Nonempty
      ((adicResidueLocalReduction.{u, v} X J U n).obj
        ((adicResidueRestriction
      (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X)
        A J) U).obj (adicResidueConstantPerfect.{u, v} X J P)) ≅
        (adicResidueLocalReduction.{u, v} X J U n).obj M)) :
    (adicResidueHomTower.{u, v} X J U
      ((adicResidueRestriction
      (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X)
        A J) U).obj (adicResidueConstantPerfect.{u, v} X J P)) M).IsMittagLeffler := by
  sorry

end AlgebraicGeometry.Scheme
