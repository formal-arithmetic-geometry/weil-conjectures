/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationCartesianTensorDescent
public import WeilConjectures.AlgebraicGeometry.ShriekTensorCompositionSupplement

import all Mathlib.Logic.Small.Defs

/-! # Projection and ordered affine counit on a Cartesian chart

Source: blueprint sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2, simultaneous trivializations and ordered affine counits.
(blueprint: lem-pur-vector-integration-cartesian-projection-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] rightDerivedLowerShriek upperStar
  VectorBundleZeroSection.π VectorBundleZeroSection.scheme leftDerivedUpperStarComp
  leftDerivedUpperStarIsoMapDerivedCategory
attribute [local implicit_reducible] Scheme.Modules

/-- The Cartesian projection square followed by the ordered affine counit.
Source: vector-bundle purity proof, paragraph 2, tensor normalization of the inner block.
(blueprint: lem-pur-vector-integration-cartesian-projection-counit).

Proof:
1. Write a=affineTraceProjection T d, E for the Cartesian shriek exchange, δ for pullback tensor
comparison, S for derivedSquareUpperStarIso, and ℓ for leftDerivedUpperStarIsoMapDerivedCategory.
The inverse-image map u from q*(termwise p*K tensor p*L) to termwise a*(f*K) tensor q*p*L is δ_q
followed in its first factor by q*(ℓ_p inverse), S_K inverse and ℓ_a. Conjugate
compactProjectionMapCoeffFirst_baseChangeMap by these exact-pullback comparisons. Exchange
naturality and δ naturality cancel q*ℓ_p against q*(ℓ_p inverse), giving f*P_p followed by E and
a!u equal to δ_f, tensor of E, and P_a. No exchange map is inverted.

2. For a coefficient J on T let e0 be coefficientDescent J, then δ_a, then tensor of ℓ_a(J) and
the identity. The affine identity is P_a(a*P_d,J) followed by a!e0 inverse, C_d inverse and ε_d(J)
equal to tensor J of the unit affine trace followed by the right unitor. Derive it from
ordinaryAffineCounit_tensor_normalization: transport its Tate object by
(affineLinearCoefficientDescent inverse) followed by towerTateIso; projection naturality moves
this specified isomorphism through P_a, and the two towerTateIso factors cancel. Explicit
unfolding identifies affineDualizingTowerComparison with affineTraceUnboundedCompactComparison. At
the unit its bounded-below comparison equals C_d by the restriction theorem.

3. In the equation of step 1 transport the second factor q*p*L along S_L inverse followed by
a*(b.hom). Transport the first factor from f*K to K′ along cK. Projection naturality in both
variables and counit naturality allow these maps to pass to the affine formula of step 2.
Expanding the constructed tensor descent shows that these are exactly its factors, with no
unspecified comparison isomorphism.

4. The unit trace after these transports is E at p*L, then a! of S_L inverse, a!(a*b), inverse
affine coefficient descent, C_d inverse at the unit, and ε_d at the unit. These are precisely
vectorIntegrationCartesianPrefix followed by affineTraceCounit. Tensor pullback and right-unitor
naturality give the displayed right side ending in cK.hom. The d=0 formulas use the identity
adjunction and tensor unit; no step needs a nonempty base or a nonzero ring.
-/
theorem vectorIntegrationCartesianProjectionCounit
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    {X S T : Scheme.{u}} [IsNoetherian T]
    (p : X ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [HasCompactification p] (f : T ⟶ S) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (q : affineTraceTower T d ⟶ X)
    (sq : IsPullback q (affineTraceProjection T d) p f)
    (L K : DerivedCategoryModule A S) (K' : DerivedCategoryModule A T)
    (cK : (ordinaryFinitePullback A f).obj K ≅ K')
    (b : (ordinaryFinitePullback A f).obj L ≅ affineLinearBaseCoefficient A N hA T d) :
    (ordinaryFinitePullback A f).map
        (compactSupportProjectionMap A p ((ordinaryFinitePullback A p).obj L) K) ≫
      (rightDerivedLowerShriekBaseChangeMap A sq).app _ ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection T d)).map
        (vectorIntegrationCartesianTensorDescent A N hA t p f hT d q sq L K K' cK b).inv ≫
      (affineTraceUnboundedCompactComparison A T d).inv.app _ ≫
      (affineTraceAdjunction A N hA t D T hT d).counit.app K' =
    (ordinaryFiniteTensorPullback A f K
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj
        ((ordinaryFinitePullback A p).obj L))).hom ≫
      ((ordinaryFiniteTensor A T).obj ((ordinaryFinitePullback A f).obj K)).map
        (vectorIntegrationCartesianPrefix N hN A hA t p f hT d q sq L b ≫
          affineTraceCounit A N hA t D T hT d) ≫
      (derivedTensorSingleUnitIso ((ordinaryFinitePullback A f).obj K)).hom ≫ cK.hom := by
  sorry

end AlgebraicGeometry.Etale
