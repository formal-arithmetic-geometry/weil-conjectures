/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.CondensedTateIntegralTowerData
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
import Sheaf.Paper.NormalizedTateTensorTowerCore
import Sheaf.Paper.NormalizedTateTensorTowerProperties
import Sheaf.Paper.NormalizedTateTensorTowerZero

/-! # Strict normalized models for integral root tensors

Source: smooth-purity transport, construction of the normalized Tate-unit tower.
(blueprint: lem-pur-normalized-tate-tensor-tower)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

attribute [local irreducible] HasDerivedCategory.standard Functor.leftAdjoint
  SheafOfModules.monoidalCategory completedAdicDerivedChange

/-- The actual integral root tensor gives a strict normalized tower with a common
single-degree local model. This asserts no reconstruction or exceptional-image result.

Source: current blueprint, smooth-purity transport, reconstruction proof Steps 2--5.
(blueprint: lem-pur-normalized-tate-tensor-tower)

Proof: on a common pro-etale cover choose compatible primitive roots. Taking limits
identifies the integral root module with the completed coefficient unit and identifies
its projections with the finite root generators. Tensor these local bases in the
specified order. Extension of scalars commutes with those tensors by balancing, with
the coefficient projection at power zero. Hence the resulting finite comparison has
exactly ProjectionBalanced's formula, including arbitrary local quotient scalars.
The root powers are locally free of rank one. Tensoring with a line is an exact
functor, so its single complex is K-flat; its ordinary reductions therefore compute
the derived reductions. The actual strict quotient tower, its exact evaluations, and
these counits give the stated AdicTower and ProjectionNormalized. Compare the
normalizations on root generators: both apply the root power map and the quotient
scalar action. This gives the displayed equality for every normalized comparison,
and multiplying exponents and residues proves the cocycle, including equal indices.
The same trivializing cover provides a common adic-lisse rank-one complex supported
in degree -2d. Its finite reductions are finite lisse, giving their intrinsic and
fixed-coefficient constructibility. At d=0 all these arguments use the
coefficient unit and the empty root tensor; empty schemes require no exception.
-/
theorem normalizedTateTensorTower
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ) :
    ∃ (M : AdicTower T (datum.{u} ell))
      (e : ∀ n : ℕ, M.level n ≅ (derivedRealization T ell n).obj (finiteTwist T ell n d))
      (h : M.tower = strictDerivedTower T ell d),
      ProjectionNormalized T ell hT d M e h ∧
      ∃ (S : Stratification T) (W : UniformAdicTowerData (datum.{u} ell) M S),
        W.lower = -(2 * (d : ℤ)) ∧ W.upper = -(2 * (d : ℤ)) ∧
        (∀ (b a : ℕ) (hab : a ≤ b)
          (r : CoefficientLineComparison
            (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
            (ell ^ (b + 1)) (ell ^ (a + 1))
            (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T),
          (pbcDerivedExtend (pbcAdicQuotient T (datum.{u} ell) b a hab)).map (e b).hom ≫
              (scalarComparison T ell b a hab).hom.app (finiteTwist T ell b d) ≫
              (derivedRealization T ell a).map (proTwistMap d r) =
            (M.normalization b a hab).hom ≫ (e a).hom) ∧
        (∀ (n : ℕ) (q : ℤ),
          @IsConstructibleProEtaleCoefficientModuleSheaf T (Ring.{u} ell ⧸
              (datum.{u} ell).ideal ^ (n + 1)) _ ((datum.{u} ell).quotientFinite n)
            ((pbcRestrict (pbcLevelConstantComparison T (datum.{u} ell) n).hom).obj
              ((_root_.DerivedCategory.homologyFunctor _ q).obj (M.level n)))) ∧
        (∀ (n : ℕ) (q : ℤ),
          IsConstructibleProEtaleFixedModuleSheaf T (coefficient ell (n + 1))
            ((_root_.DerivedCategory.homologyFunctor _ q).obj (finiteTwist T ell n d))) ∧
        ∀ hd : d = 0, ∀ (b a : ℕ) (hab : a ≤ b),
          let e₀ (n : ℕ) := e n ≪≫ (derivedRealization T ell n).mapIso
            (eqToIso (congrArg (finiteTwist T ell n) hd) ≪≫ finiteZeroIso T ell n);
          (pbcDerivedExtend (pbcAdicQuotient T (datum.{u} ell) b a hab)).map (e₀ b).hom ≫
              (scalarComparison T ell b a hab).hom.app (𝟙_ _) ≫
              (derivedRealization T ell a).map (unitReduction T ell b a hab).hom =
            (M.normalization b a hab).hom ≫ (e₀ a).hom := by
  obtain ⟨M, e, h, hp, hr, hsquare⟩ := normalizedTateTensorTower_core T ell hT d
  obtain ⟨S, W, hl, hu, hc, hf⟩ :=
    normalizedTateTensorTower_properties T ell hT d M e h hp hsquare
  refine ⟨M, e, h, hp, S, W, hl, hu, hsquare, hc, hf, ?_⟩
  exact normalizedTateTensorTower_zero T ell hT d M e h hp hsquare hr

end AlgebraicGeometry.Scheme.PurityIntegralTower
