/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.FiniteSmoothCoefficientArrows
import Sheaf.Paper.FiniteSmoothOrdinaryTwistCocycle

/-! The unrestricted tensor/pullback coherence square underlying the finite smooth
purity-source cocycle.

Source: blueprint sk-lem-sp-reduction-compatibilities.proof.md, part (3),
tensor coefficient-composition square before restricting to bounded inputs.
(blueprint: lem-pur-finite-smooth-purity-source-tensor-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The tensor/pullback square for the concrete purity source, with the
ordinary twist and pullback cocycles supplied as hypotheses.  This is the
unrestricted structural subargument; bounded constructibility is imposed only
by `puritySourceCocycle`.
Source: blueprint sk-lem-sp-reduction-compatibilities.proof.md, part (3).
(blueprint: lem-pur-finite-smooth-purity-source-tensor-composition). -/
theorem finiteSourceTensorComposition
    (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (twists : ∀ (r m : ℕ) (_hm : 1 ≤ m) (hmr : m ≤ r),
      CoefficientLineComparison (FiniteReduction.quotient ell hmr) (ell ^ r) (ell ^ m)
        (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) X)
    (htwist : ∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r),
      (ordinaryScalar (FiniteReduction.quotient ell hnm) X).map
          ((twists r m (hn.trans hnm) hmr).tensorPower d).hom ≫
        ((twists m n hn hnm).tensorPower d).hom =
      (ordinaryAssociator X ell hmr hnm).hom.app
          (line (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) X d) ≫
        ((twists r n hn (hnm.trans hmr)).tensorPower d).hom)
    (hpull : ∀ (r m n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
      (K : DerivedCategoryModule (coefficient ell r) Y),
      QuotientCocycle
        (ordinaryScalar (FiniteReduction.quotient ell hmr) Y)
        (ordinaryScalar (FiniteReduction.quotient ell hnm) Y)
        (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
        (ordinaryScalar (FiniteReduction.quotient ell hmr) X)
        (ordinaryScalar (FiniteReduction.quotient ell hnm) X)
        (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
        (ordinaryAssociator Y ell hmr hnm)
        (ordinaryAssociator X ell hmr hnm)
        (ordinaryFinitePullback (coefficient ell r) f)
        (ordinaryFinitePullback (coefficient ell m) f)
        (ordinaryFinitePullback (coefficient ell n) f)
        (ordinaryPullbackMap (FiniteReduction.quotient ell hmr) f)
        (ordinaryPullbackMap (FiniteReduction.quotient ell hnm) f)
        (ordinaryPullbackMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K) :
  ∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : DerivedCategoryModule (coefficient ell r) Y),
    QuotientCocycle
      (ordinaryScalar (FiniteReduction.quotient ell hmr) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) Y)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hmr) X)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) X)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (ordinaryAssociator Y ell hmr hnm)
      (ordinaryAssociator X ell hmr hnm)
      (puritySource (coefficient ell r) f
        (line (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) X d))
      (puritySource (coefficient ell m) f
        (line (coefficient ell m) (ell ^ m) (CharP.cast_eq_zero _ _) X d))
      (puritySource (coefficient ell n) f
        (line (coefficient ell n) (ell ^ n) (CharP.cast_eq_zero _ _) X d))
      (fun K ↦ (pullbackTwistComparison f d
        (twists r m (hn.trans hnm) hmr) K).hom)
      (fun K ↦ (pullbackTwistComparison f d (twists m n hn hnm) K).hom)
      (fun K ↦ (pullbackTwistComparison f d
        (twists r n hn (hnm.trans hmr)) K).hom) K := by
  sorry

end AlgebraicGeometry.Etale.FiniteSmoothPurity
