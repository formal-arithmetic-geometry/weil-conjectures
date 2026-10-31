/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalReductionComparisons
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.SmoothPurity.EtaleFiniteTwistPullbackRest
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects

/-! Root-normalized comparison for the finite extension coefficient quotients.

This is the coefficient-line construction required before the vector integration
square can be transported to the pro-etale presentation.
(blueprint: lem-pur-finite-diagonal-vector-reduction-root-comparison). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- The normalized root-power comparison for the actual finite extension quotients.
Source: blueprint/latest, sk-lem-sp-reduction,
thm-pur-finite-reduction-of-purity.proof.md, Step 2 (invertible twists).
Proof: use N = ell^n and M = ell^m, with M dividing N. The quotient homomorphism
shows that N also annihilates the target ring. At this common exponent, the
adjoint of reductionEtaleTateMap is an isomorphism by scalar balancing. Compose
it with the exponent-change isomorphism induced by z mapping to z^(N/M).
Adjunction naturality and the two generator formulas give the required generator
normalization. Compose the derived scalar isomorphism with the degree-zero image
of the same exponent-change map; its defining formula gives derived_normalization.
Invertibility of N on X is required for exponent change and the flat-single
calculation; in the diagonal application it follows from the structure map to k.
(blueprint: lem-pur-finite-diagonal-vector-reduction-root-comparison). -/
theorem finiteDiagonalRootComparison
    (hX : IsUnit (P.diagonalExponent : Γ(X, ⊤))) :
    Nonempty (CoefficientLineComparison (quotient P m hm hmn)
        P.diagonalExponent (P.finiteReductionSetting m hm).diagonalExponent
        P.diagonalExponent_annihilates
        (P.finiteReductionSetting m hm).diagonalExponent_annihilates X) := by
  let A := P.Coefficient
  let Q := P.finiteReductionSetting m hm
  let B := Q.Coefficient
  let phi : A →+* B := quotient P m hm hmn
  let N := P.diagonalExponent
  let M := Q.diagonalExponent
  have hA : (N : A) = 0 := P.diagonalExponent_annihilates
  have hB : (M : B) = 0 := Q.diagonalExponent_annihilates
  have hBN : (N : B) = 0 := by
    rw [← map_natCast phi, hA, map_zero]
  have hp : 0 < P.coefficients.l := P.coefficients.prime.out.pos
  have hN : 0 < N := pow_pos hp P.level
  have hM : 0 < M := pow_pos hp m
  have hdiv : M ∣ N := pow_dvd_pow P.coefficients.l hmn
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hexp⟩ :=
    (Scheme.finiteEtaleTwistPullbackData B M hM hB).laws
  obtain ⟨q, t, hq, ht, _⟩ := hexp N hN hdiv X hX
  let s : (ProEtale.etaleSheafExtendScalars phi X).obj
      (Scheme.finiteEtaleTateLine X N A hA) ≅
        Scheme.finiteEtaleTateLine X N B hBN :=
    @asIso _ _ _ _
      (((ProEtale.etaleSheafExtendScalarsAdjunction phi X).homEquiv _ _).symm
        (ProEtale.reductionEtaleTateMap phi X N hA hBN))
      (ProEtale.reductionTateOrdinaryScalar_isIso phi X N hA hBN)
  let e : (ProEtale.etaleSheafExtendScalars phi X).obj
      (Scheme.finiteEtaleTateLine X N A hA) ≅
        Scheme.finiteEtaleTateLine X M B hB := s ≪≫ t 1
  refine ⟨{
    roots := q
    roots_power := hq
    sheafIso := e
    generators := ?_
    derivedIso := ProEtale.reductionEtaleTateIso phi X N hA hBN hX ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso (t 1)
    derived_normalization := ?_ }⟩
  · intro W a z
    change ((ProEtale.etaleSheafExtendScalarsAdjunction phi X).homEquiv _ _
      e.hom).hom.app W (Scheme.finiteEtaleTateOneGenerator A N X hA W a z) =
        Scheme.finiteEtaleTateOneGenerator B M X hB W (phi a)
          (q.hom.app W z)
    have hs : (ProEtale.etaleSheafExtendScalarsAdjunction phi X).homEquiv _ _ s.hom =
        ProEtale.reductionEtaleTateMap phi X N hA hBN := by
      exact Equiv.apply_symm_apply _ _
    dsimp only [e, Iso.trans_hom]
    rw [Adjunction.homEquiv_naturality_right, hs]
    change (t 1).hom.hom.app W
      ((ProEtale.reductionEtaleTateMap phi X N hA hBN).hom.app W
        (Scheme.finiteEtaleTateOneGenerator A N X hA W a z)) = _
    rw [show (ProEtale.reductionEtaleTateMap phi X N hA hBN).hom.app W
        (Scheme.finiteEtaleTateOneGenerator A N X hA W a z) =
          Scheme.finiteEtaleTateOneGenerator B N X hBN W (phi a) z from
      (ProEtale.reductionEtaleTateMap_existsUnique phi X N hA hBN).exists.choose_spec W a z]
    exact ht W (phi a) z
  · simp only [Iso.trans_hom, Functor.mapIso_hom, ProEtale.reductionEtaleTateIso,
      asIso_hom, ProEtale.reductionEtaleTateExtensionMap, e, s, Functor.map_comp,
      Category.assoc]
    rfl

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
