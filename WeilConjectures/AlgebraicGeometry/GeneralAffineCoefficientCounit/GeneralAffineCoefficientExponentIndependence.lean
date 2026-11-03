/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralAffineCoefficientCounit.GeneralAffineCoefficientCounitNormalizationDefs

/-! Kummer-normalized exponent independence for the general affine coefficient counit.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-thm-smooth-purity/lem-pur-projection-purity-agreement.proof.md,
common maximum exponent comparison (blueprint: lem-pur-affine-coefficient-counit-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.GeneralAffineCoefficientCounit
open AffineOrderedIntegrationGeneral FiniteCompactificationTranspose
variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The complete common-maximum Kummer comparison, separated from the main theorem.

Proof: compare both annihilating powers with their maximum. The power maps on roots
and on the middle multiplicative sheaf give the kernel equation and generator equation;
the finite Tate pullback theorem makes the induced line map canonical. Naturality of
projective trace, open restriction, coefficient-first counits, and the specified Hom
transpose gives the remaining four equalities. Power-map composition supplies the
cocycle, including equal exponents and the zero-ring case.
-/
theorem general_affine_exponent_independence
    (k : Type u) [Field k] (_hk : Finite k ∨ IsAlgClosed k)
    (ell : ℕ) (hell : ell.Prime) (_hp : (ringChar k).Prime)
    (hne : ringChar k ≠ ell) {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (r s : ℕ) (_hrs : r ≤ s)
    (hA : ((ell ^ (r + 1) : ℕ) : A) = 0)
    (hA' : ((ell ^ (s + 1) : ℕ) : A) = 0)
    (H : E A Y)
    (_hH : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y H) :
    letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
    let N := ell ^ (r + 1)
    let M := ell ^ (s + 1)
    let hN : 0 < N := pow_pos hell.pos _
    let hM : 0 < M := pow_pos hell.pos _
    let hY := baseUnit k ell hell hne (r + 1) aY
    let hY' := baseUnit k ell hell hne (s + 1) aY
    ∃ (q : (ProjectiveLine Y).rootsOfUnitySheaf M ⟶
        (ProjectiveLine Y).rootsOfUnitySheaf N)
      (e : Scheme.finiteEtaleTateLine (ProjectiveLine Y) M A hA' ≅
        Scheme.finiteEtaleTateLine (ProjectiveLine Y) N A hA),
      q ≫ kernel.ι (N • 𝟙 (ProjectiveLine Y).gmSheaf) =
        (M / N) • kernel.ι (M • 𝟙 (ProjectiveLine Y).gmSheaf) ∧
      (∀ (U : (ProjectiveLine Y).Etaleᵒᵖ) (a : A)
        (z : ((ProjectiveLine Y).rootsOfUnitySheaf M).obj.obj U),
        e.hom.hom.app U (Scheme.finiteEtaleTateOneGenerator A M (ProjectiveLine Y)
          hA' U a z) = Scheme.finiteEtaleTateOneGenerator A N (ProjectiveLine Y)
            hA U a (q.hom.app U z)) ∧
      (Etale.ordinaryFinitePushforward A (ProjectiveLine Y ↘ Y)).map
          (projectiveExponentIso A Y e).hom ≫ Etale.projectiveLineTrace N hN A hA Y hY =
        Etale.projectiveLineTrace M hM A hA' Y hY' ∧
      (Etale.affineTraceLineLeft A Y).map (lineExponentIso A Y e).hom ≫
          CoordinateLine.integration A N hA Y hN hY =
        CoordinateLine.integration A M hA' Y hM hY' ∧
      (Etale.affineTraceLineLeft A Y).map (sourceExponentIso A Y e H).hom ≫
          (CoordinateLine.adjunction A N hA Y hN hY).counit.app H =
        (CoordinateLine.adjunction A M hA' Y hM hY').counit.app H ∧
      (C A Y).map ((Etale.affineTraceLineLeft A Y).map
          (sourceExponentIso A Y e H).hom) ≫
          (C A Y).map ((CoordinateLine.adjunction A N hA Y hN hY).counit.app H) =
        (C A Y).map ((CoordinateLine.adjunction A M hA' Y hM hY').counit.app H) ∧
      (C A (AffineSpace PUnit.{u + 1} Y)).map (sourceExponentIso A Y e H).hom ≫
          (C A (AffineSpace PUnit.{u + 1} Y)).map
            ((CoordinateLine.comparison A N hA Y hN hY).hom.app H) =
        (C A (AffineSpace PUnit.{u + 1} Y)).map
          ((CoordinateLine.comparison A M hA' Y hM hY').hom.app H) := by
  sorry

end AlgebraicGeometry.ProEtale.GeneralAffineCoefficientCounit
