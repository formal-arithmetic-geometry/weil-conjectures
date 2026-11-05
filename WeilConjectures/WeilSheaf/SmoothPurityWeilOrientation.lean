/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurity
import WeilConjectures.WeilSheaf.SmoothPurityNativeTateDescent
import WeilConjectures.WeilSheaf.SmoothPurityOrientationOfTateEncoding

/-!
# Frobenius equivariance of the orientation of a smooth morphism, proved

`AlgebraicGeometry.WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_absolutePurity`
proves the statement of
`AlgebraicGeometry.WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso`
(blueprint `thm-pur-weil-equivariance-of-purity-and-trace`, the purity square at `K = ℚ̄_ℓ`),
word for word, from the absolute purity route:
- the native Tate encoding `α` (A3,
  `AlgebraicGeometry.WeilSheaf.purity_nonempty_toCondensedTateDescentIso`: the Tate twist sheaf is
  the descent of the finite-base root-defined Tate sheaf);
- the invertibility of the exceptional base change map at the unit along `k₀ ⟶ k̄₀` for every
  smooth `f` (A1',
  `AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothUnitBaseChange_descendedShriekGeometricExchange`,
  by Verdier duality), which together produce the orientation as an isomorphism of native Weil
  complexes (`exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_tateEncoding`),
  so it commutes with the Frobenius structures.

The proof lives in this leaf module rather than in `WeilConjectures.WeilSheaf.SmoothPurity`
because the two imports above enlarge that module's import closure by about 1850 modules, which
makes the unchanged elaboration of
`AlgebraicGeometry.WeilComplex.exists_natTrans_forget_eq_upperShriekUnitTensorMap` there exceed
the heartbeat limit.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

open ProEtale MonoidalCategory

variable [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l f]

/-- **Frobenius equivariance of the orientation of a smooth morphism** (blueprint:
`thm-pur-weil-equivariance-of-purity-and-trace`, the purity square at `K = ℚ̄_ℓ`), the statement
of `AlgebraicGeometry.WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso`
proved from the native Tate encoding (A3) and the invertibility of the exceptional unit base
change along `k₀ ⟶ k̄₀` (A1'). -/
theorem exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_absolutePurity (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    ∃ g : forget.obj ((upperShriek f).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))) ≅
      forget.obj (((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧),
      (Endofunctor.IsoAlgebra.derivedStrIso _).hom.app
          ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))).obj ≫
          g.hom =
        (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory.map g.hom ≫
          (Endofunctor.IsoAlgebra.derivedStrIso _).hom.app (((tateTwist k₀ l X d).obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).obj := by
  obtain ⟨α⟩ := WeilSheaf.purity_nonempty_toCondensedTateDescentIso k₀ l X d
  exact exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_tateEncoding f d α

end WeilComplex

end AlgebraicGeometry
