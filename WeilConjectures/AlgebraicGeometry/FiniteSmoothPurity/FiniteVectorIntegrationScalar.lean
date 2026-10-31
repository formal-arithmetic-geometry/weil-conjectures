/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteCoefficientTensorFactorization
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteScalarUnitNormalization
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingIntegrationExponent

/-! # Scalar and exponent compatibility before transposing vector integration

Source: blueprint/latest, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
  cachedEtaleMonoidalPreadditive cachedEtaleCoproducts cachedEtaleColimits
  cachedEtaleFlatResolution cachedEtaleInjectiveResolution
  cachedEtaleExactColimits cachedEtaleTensor4 cachedEtaleTensor12
  cachedEtaleTensor23 cachedEtaleTensorColimits cachedEtaleTensorFlipColimits

open WeilConjectures.PurityFiniteSetting
open CategoryTheory.MonoidalCategory
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar

end AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private theorem common_trace
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (d : ℕ) (E : S.Modules) [E.IsFiniteLocallyFreeOfRank d]
    (hS : IsUnit (N : Γ(S, ⊤))) :
    (compactScalarMap φ (vectorBundlePurityCompactification S d E)).app
        (vectorIntegrationCoefficient A N hA S d E) ≫
      (vectorBundlePurityLower B S d E).map
        ((scalarPullbackIso φ (VectorBundleZeroSection.π S d E)).inv.app
            (line A N hA S d) ≫
          (ordinaryFinitePullback B (VectorBundleZeroSection.π S d E)).map
            (VectorTraceScalar.base φ N hN hA hB S hS d)) ≫
      vectorBundleIntegration N hN B hB S hS d E =
    (ordinaryScalar φ S).map (vectorBundleIntegration N hN A hA S hS d E) ≫
      (ExceptionalCoefficients.unitIso φ S).hom := by
  change SheafOfModules.{u} S.ringCatSheaf at E
  have hv := (VectorTraceScalar.vectorTraceScalarDescent N hN φ hA hB S hS d E).2.2.2.2
  rw [finiteScalarUnit_normalization φ S] at hv
  dsimp only [VectorTraceScalar.vector, VectorTraceScalar.pullBase] at hv
  change ((compactScalarMap φ (vectorBundlePurityCompactification S d E)).app
      (vectorIntegrationCoefficient A N hA S d E) ≫
    (vectorBundlePurityLower B S d E).map
      ((scalarPullbackIso φ (VectorBundleZeroSection.π S d E)).inv.app (line A N hA S d) ≫
        (ordinaryFinitePullback B (VectorBundleZeroSection.π S d E)).map
          (VectorTraceScalar.base φ N hN hA hB S hS d))) ≫
      vectorBundleIntegration N hN B hB S hS d E = _ at hv
  simpa only [ordinaryScalar, Category.assoc] using hv

private theorem compose_trace
    {C D : Type*} [Category C] [Category D] (P : D ⥤ C) (L : C ⥤ D)
    {U V W X Z : D} {J : C}
    (q : X ⟶ L.obj J) (β : J ⟶ P.obj U)
    (l : U ⟶ V) (h : U ⟶ W) (e : W ⟶ V)
    (t : L.obj (P.obj V) ⟶ Z) (t' : L.obj (P.obj W) ⟶ Z) (s : X ⟶ Z)
    (hf : l = h ≫ e) (he : L.map (P.map e) ≫ t = t')
    (hv : q ≫ L.map (β ≫ P.map h) ≫ t' = s) :
    q ≫ L.map (β ≫ P.map l) ≫ t = s := by
  rw [hf]
  simp only [Functor.map_comp, Category.assoc] at hv ⊢
  rw [he]
  exact hv

/-- The trace square on compact supports, before taking an exceptional adjoint or
restricting to any section. The coefficient comparison is the pullback of the ordered
root-tensor comparison, and the target comparison is coefficient-unit multiplication.
Source: blueprint/latest, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2; sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, (3), Orientation.
(blueprint: lem-sp-finite-vector-integration-scalar).

Proof: N also annihilates B. The canonical exponent-change isomorphism b at B,
from N to M, has the same root power map as t, since the root kernel inclusion is
monic. The scalar adjunction and root-generator universal property identify
t.sheafIso with the unique common-exponent balancing followed by b. Apply the
derived normalization and shift, then induct over the ordered tensor powers to
factor t.tensorPower d as VectorTraceScalar.base at N followed by
finiteGeneralRingLevelPower of b. The successor calculation uses only naturality
of the tensor bifunctor, so no factors are permuted. Apply inverse image and
compact support. finiteGeneralRingIntegrationExponent cancels the exponent factor
against integration at M. vectorTraceScalarDescent gives the remaining scalar
square at N. The single/unit identifications have identity arrows, so its unit
comparison is the displayed multiplication-normalized unitIso. This proof has
no exceptional inverse image or section adjunct. At rank zero all ordered powers
are the scalar unit map; empty schemes and zero coefficient rings are included
by the same universal properties. No scalar flatness is assumed. -/
theorem finiteVectorIntegration_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hMN : M ∣ N)
    (hA : (N : A) = 0) (hB : (M : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (d : ℕ) (E : S.Modules) [E.IsFiniteLocallyFreeOfRank d]
    (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (M : Γ(S, ⊤)))
    (t : CoefficientLineComparison φ N M hA hB S) :
    (compactScalarMap φ (vectorBundlePurityCompactification S d E)).app
        (vectorIntegrationCoefficient A N hA S d E) ≫
      (vectorBundlePurityLower B S d E).map
        ((scalarPullbackIso φ (VectorBundleZeroSection.π S d E)).inv.app
            (line A N hA S d) ≫
          (ordinaryFinitePullback B (VectorBundleZeroSection.π S d E)).map
            (t.tensorPower d).hom) ≫
      vectorBundleIntegration M hM B hB S hS' d E =
    (ordinaryScalar φ S).map (vectorBundleIntegration N hN A hA S hS d E) ≫
      (ExceptionalCoefficients.unitIso φ S).hom := by
  change SheafOfModules.{u} S.ringCatSheaf at E
  have hBN : (N : B) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg φ hA
  have hexp := (Scheme.finiteEtaleTwistPullbackData B M hM hB).laws.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨q, b, hq, hb, _⟩ := hexp N hN hMN S hS
  have hcomparison : ProEtale.FiniteGeneralRingKummerComparison B N M hBN hB S q (b 1) :=
    ⟨hq, hb⟩
  have hf := finiteCoefficientTensor_factor φ N M hN hA hBN hB S hS t q (b 1) hcomparison d
  have he := ProEtale.finiteGeneralRingIntegrationExponent B N M hN hM hMN hBN hB
    S hS hS' d E q (b 1) hcomparison
  exact compose_trace (ordinaryFinitePullback B (VectorBundleZeroSection.π S d E))
    (vectorBundlePurityLower B S d E)
    ((compactScalarMap φ (vectorBundlePurityCompactification S d E)).app
      (vectorIntegrationCoefficient A N hA S d E))
    ((scalarPullbackIso φ (VectorBundleZeroSection.π S d E)).inv.app (line A N hA S d))
    (t.tensorPower d).hom (VectorTraceScalar.base φ N hN hA hBN S hS d)
    (ProEtale.finiteGeneralRingLevelPower B N M hBN hB S (b 1) d).hom
    (vectorBundleIntegration M hM B hB S hS' d E)
    (vectorBundleIntegration N hN B hBN S hS d E)
    ((ordinaryScalar φ S).map (vectorBundleIntegration N hN A hA S hS d E) ≫
      (ExceptionalCoefficients.unitIso φ S).hom)
    hf he (common_trace φ N hN hA hBN S d E hS)

end AlgebraicGeometry.Etale.FiniteSmoothPurity
