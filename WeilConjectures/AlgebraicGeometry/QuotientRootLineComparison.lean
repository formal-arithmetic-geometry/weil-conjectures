/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothCoefficientArrows
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import all WeilConjectures.SecSmoothPurity.ReductionExceptionalObjects

/-! # Normalized comparison for quotient root lines

Source: latest blueprint, sk-lem-sp-reduction, coefficient twist comparison.
(blueprint: lem-pur-quotient-root-line-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- Quotient comparison fixed by the power map and all scalar/root generators.
Source: latest blueprint, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-compatibilities.proof.md (3), Orientation.
(blueprint: lem-pur-quotient-root-line-comparison).

Proof: factor ell^r as ell^m times ell^(r-m). Multiplication by ell^(r-m)
on G_m carries the ell^r-kernel into the ell^m-kernel; the kernel universal
property gives roots and its displayed power equation. On a common etale cover
choose a primitive ell^r-root. Its image is a primitive ell^m-root, so the
induced balanced map on scalar/root generators is the identity B -> B in these
free rank-one coordinates. It is therefore a sheaf isomorphism. The formula is
independent of the local primitive root and glues by the tensor universal property.
The source line is locally free, so its derived scalar extension is its ordinary
extension in degree zero. Compose this canonical scalar counit with the derived
single of the sheaf isomorphism. This gives derivedIso with exactly the stated
normalization. The kernel inclusion is monic and scalar/root generators generate,
so every field is determined by these equations. At r=m the power is one, and on
an empty scheme the same universal properties apply. -/
theorem quotientRootLineComparison
    (ell : ℕ) [Fact ell.Prime] (T : Scheme.{u})
    (hT : IsUnit (ell : Γ(T, ⊤)))
    (r m : ℕ) (hm : 1 ≤ m) (hmr : m ≤ r) :
    Nonempty (CoefficientLineComparison (FiniteReduction.quotient ell hmr)
      (ell ^ r) (ell ^ m) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T) := by
  let A := coefficient.{u} ell r
  let B := coefficient.{u} ell m
  let phi : A →+* B := FiniteReduction.quotient ell hmr
  have hA : ((ell ^ r : ℕ) : A) = 0 := CharP.cast_eq_zero _ _
  have hB : ((ell ^ m : ℕ) : B) = 0 := CharP.cast_eq_zero _ _
  have hdiv : ell ^ m ∣ ell ^ r := pow_dvd_pow ell hmr
  have hBr : ((ell ^ r : ℕ) : B) = 0 :=
    (ringChar.spec B (ell ^ r)).mpr
      (dvd_trans ((ringChar.spec B (ell ^ m)).mp hB) hdiv)
  have hTr : IsUnit ((ell ^ r : ℕ) : Γ(T, ⊤)) := by
    simpa only [Nat.cast_pow] using hT.pow r
  have hp : 0 < ell := (Fact.out : ell.Prime).pos
  have hmp : 0 < ell ^ m := hp.trans_le (Nat.le_self_pow (by omega : m ≠ 0) ell)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hexp⟩ :=
    (Scheme.finiteEtaleTwistPullbackData B (ell ^ m) hmp hB).laws
  obtain ⟨q, t, hq, ht, _⟩ := hexp (ell ^ r) (pow_pos hp r) hdiv T hTr
  let s : (ProEtale.etaleSheafExtendScalars phi T).obj
      (Scheme.finiteEtaleTateLine T (ell ^ r) A hA) ≅
        Scheme.finiteEtaleTateLine T (ell ^ r) B hBr :=
    @asIso _ _ _ _
      (((ProEtale.etaleSheafExtendScalarsAdjunction phi T).homEquiv _ _).symm
        (ProEtale.reductionEtaleTateMap phi T (ell ^ r) hA hBr))
      (ProEtale.reductionTateOrdinaryScalar_isIso phi T (ell ^ r) hA hBr)
  let e : (ProEtale.etaleSheafExtendScalars phi T).obj
      (Scheme.finiteEtaleTateLine T (ell ^ r) A hA) ≅
        Scheme.finiteEtaleTateLine T (ell ^ m) B hB := s ≪≫ t 1
  refine ⟨{
    roots := q
    roots_power := hq
    sheafIso := e
    generators := ?_
    derivedIso := ProEtale.reductionEtaleTateIso phi T (ell ^ r) hA hBr hTr ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso (t 1)
    derived_normalization := ?_ }⟩
  · intro W a z
    change ((ProEtale.etaleSheafExtendScalarsAdjunction phi T).homEquiv _ _
      e.hom).hom.app W (Scheme.finiteEtaleTateOneGenerator A (ell ^ r) T hA W a z) =
        Scheme.finiteEtaleTateOneGenerator B (ell ^ m) T hB W (phi a)
          (q.hom.app W z)
    have hs : (ProEtale.etaleSheafExtendScalarsAdjunction phi T).homEquiv _ _ s.hom =
        ProEtale.reductionEtaleTateMap phi T (ell ^ r) hA hBr := by
      exact Equiv.apply_symm_apply _ _
    dsimp only [e, Iso.trans_hom]
    rw [Adjunction.homEquiv_naturality_right, hs]
    change (t 1).hom.hom.app W
      ((ProEtale.reductionEtaleTateMap phi T (ell ^ r) hA hBr).hom.app W
        (Scheme.finiteEtaleTateOneGenerator A (ell ^ r) T hA W a z)) = _
    rw [show (ProEtale.reductionEtaleTateMap phi T (ell ^ r) hA hBr).hom.app W
        (Scheme.finiteEtaleTateOneGenerator A (ell ^ r) T hA W a z) =
          Scheme.finiteEtaleTateOneGenerator B (ell ^ r) T hBr W (phi a) z from
      (ProEtale.reductionEtaleTateMap_existsUnique phi T
        (ell ^ r) hA hBr).exists.choose_spec W a z]
    exact ht W (phi a) z
  · simp only [Iso.trans_hom, Functor.mapIso_hom, ProEtale.reductionEtaleTateIso,
      asIso_hom, ProEtale.reductionEtaleTateExtensionMap, e, s, Functor.map_comp,
      Category.assoc]
    rfl

end AlgebraicGeometry.Etale.FiniteSmoothPurity
