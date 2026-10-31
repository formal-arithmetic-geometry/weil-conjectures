/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.P1KummerScalarEndpoints
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.AlgebraicGeometry.PurEtaleScalarMateProjection
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteChernPullback
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
public import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystemSupplement
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
public import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
public import WeilConjectures.CategoryTheory.DerivedSingleUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalCartier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth


/-!
# Finite-ring coefficient comparison preserves the normalized projective-line splitting

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts paragraph (blueprint:
lem-sp-finite-p1-coefficient-splitting).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The normalized projective-line splitting and its trace commute with arbitrary finite
coefficient extension, and the diagonal Kummer class is carried to the corresponding
coefficient class. The proper comparison is the scalar mate, whose definition is the
counit transpose. The proof is the retained chart calculation in the source.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts paragraph (blueprint:
lem-sp-finite-p1-coefficient-splitting).

Proof:
(1) For T = S, P, W the endpoint records of lem-sp-p1-kummer-scalar-endpoint-existence
(def-sp-p1-kummer-scalar-endpoints) are the specified u_T and shifted balanced λ_T: the
unit and Tate line are flat (lem-asd-finite-etale-twist-line), their degree-zero
complexes are K-flat (lem-pc-bounded-above-flat-kflat-site), and scalar extension is the
ordinary tensor there (lem-pur-derived-change-of-rings); the transposed insertions are
a ⊗ b ↦ φ(a)b and (z ⊗ a) ⊗ b ↦ z ⊗ φ(a)b, shifted by two for λ_T.
(2) With F_R = q_R^{-1}, the scalar/pullback comparison κ, constant pullback z_R and the
roots-normalized twist pullback k_R (lem-asd-etale-finite-twist-pullback), the squares
u_P T(z_A) κ = z_B F_B(u_S) and λ_P T(k_A) κ = k_B F_B(λ_S) hold, checked on pure
tensors via lem-sfb-ringed-derived-monoidal-comparisons.
(3) χ_q is the counit transpose (lem-asd-proper-finite-coefficient-extension, here
`scalarMate`); by counit naturality, the defining transpose and naturality of κ, the
adjunct of γ T_S(a) is λ_P T_P(â) κ_K, where â = ε F_A(a).
(4) The first column v_R of s_R is H_R(k_R) η, with adjunct k_R
(lem-asd-ordinary-finite-p1-adjunction); steps 2 and 3 give γ T_S(v_A) = v_B λ_S.
(5) The second column h_R has adjunct c_R z_R; lem-sp-p1-kummer-derived-scalar gives
λ_P T_P(c_A) = c_B u_P, so steps 2 and 3 give γ T_S(h_A) = h_B u_S.
(6) T_S is additive (lem-pur-derived-change-of-rings); biproduct extensionality on the two
injections gives γ T_S(s_A) = s_B (λ_S ⊕ u_S); postcomposing with t_B = pr_2 s_B^{-1} and
cancelling T_S(s_A) gives t_B γ = u_S T_S(t_A).
(7) On W take endpoint records a, b, e for Z/N → A, Z/N → B and A → B; with the
composition comparison α, lem-sp-p1-kummer-scalar-endpoint-composition gives
e_0 E(a_0) = b_0 α and e_1 E(a_1) = b_1 α.
(8) With c_A = a_1 F_A(c_Λ) a_0^{-1} and c_B = b_1 F_B(c_Λ) b_0^{-1} for the Kummer arrow
c_Λ of O_W(Δ), naturality of α and step 7 give e_1 E(c_A) = c_B e_0, the diagonal clause.
No step uses flatness of A → B or of Z/N → A.
-/
theorem finiteP1CoefficientSplitting
    (N : ℕ) (_hN : 0 < N)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (eS : P1KummerScalarEndpoints φ N hA hB S)
    (eP : P1KummerScalarEndpoints φ N hA hB (ProjectiveLine S))
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (dA : OrdinaryFiniteP1Datum A N hA tA S hS)
    (dB : OrdinaryFiniteP1Datum B N hB tB S hS) :
    ((scalarExtension φ S).map dA.decomposition.hom ≫
        (scalarMate φ (ProjectiveLine S ↘ S)).app
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
          eP.shiftedLineIso.hom =
      biprod.lift
          ((scalarExtension φ S).map biprod.fst ≫ eS.shiftedLineIso.hom)
          ((scalarExtension φ S).map biprod.snd ≫ eS.unitIso.hom) ≫
        dB.decomposition.hom) ∧
      ((scalarMate φ (ProjectiveLine S ↘ S)).app
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
          eP.shiftedLineIso.hom ≫ dB.trace =
      (scalarExtension φ S).map dA.trace ≫ eS.unitIso.hom) ∧
      ∀ (hW : IsUnit (N : Γ(pullback (ProjectiveLine S ↘ S)
          (ProjectiveLine S ↘ S), ⊤)))
        (eW : P1KummerScalarEndpoints φ N hA hB
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))),
        (scalarExtension φ (pullback (ProjectiveLine S ↘ S)
            (ProjectiveLine S ↘ S))).map
          (ordinaryFiniteFirstChern A N hA _ hW
            (@Scheme.Pic.ofIsInvertible _
              (Scheme.Modules.dual (pullback.diagonal (ProjectiveLine S ↘ S)).ker.toModules)
              (projectiveLine_diagonal_ker_isInvertible S).isInvertible_dual_toModules)) ≫
          eW.shiftedLineIso.hom =
        eW.unitIso.hom ≫ ordinaryFiniteFirstChern B N hB _ hW
          (@Scheme.Pic.ofIsInvertible _
            (Scheme.Modules.dual (pullback.diagonal (ProjectiveLine S ↘ S)).ker.toModules)
            (projectiveLine_diagonal_ker_isInvertible S).isInvertible_dual_toModules) := by
  sorry

end AlgebraicGeometry.Etale
