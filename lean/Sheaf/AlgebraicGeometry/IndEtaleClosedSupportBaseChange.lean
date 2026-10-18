/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Finite.Exact
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction
public import Mathlib.CategoryTheory.Shift.Adjunction

import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.SixFunctors.OpenTensorNormalization
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.SixFunctors.BaseChange.Square
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Sheaf.CategoryTheory.ModuleRestrictionKernelComparison
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.SixFunctors.OpenClosed.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact

/-!
# Ind-etale base change for closed etale support

Source: Stacks Project, Tags 03Q9, 0A45 and 09XQ, with the closed-support
adjunction mate and its counit normalization
(blueprint: lem-per-ind-etale-closed-support-base-change).

The closed right adjoint is determined by its adjunction. By the supported-kernel
adjunction and bounded-below derivation it is the right derived supported inverse image.
The inverse used to form its exchange is the inverse of the specified closed exchange;
its zero value off the isomorphism locus only makes the construction total.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Closed direct image on D+ has a right adjoint, necessarily the derived support kernel.
Source: Stacks Project, Tags 09XQ and 0A45
(blueprint: lem-per-ind-etale-closed-support-base-change).
Proof: the supported-kernel adjunction gives i_* left adjoint to i^!_0 on abelian sheaves.
Its natural Hom bijection respects each scalar endomorphism, hence restricts to A-modules.
Closed i_* is exact (04CA). Module sheaves have enough injectives; bounded-below
adjunction derivation gives i_* on D+ left adjoint to R(i^!_0). Since exact i_* agrees
with its right derived functor, the latter is a left adjoint as asserted. -/
@[instance]
theorem closedSupportPlus_isLeftAdjoint
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus.IsLeftAdjoint := by
  sorry

/-- The closed right adjoint on D+, uniquely determined together with its adjunction.
Source: Stacks Project, Tag 09XQ (blueprint: lem-per-ind-etale-closed-support-base-change).
The preceding theorem constructs the adjoint by deriving the supported kernel, so this
universal-property choice introduces no unspecified geometric object. -/
abbrev closedSupportPlus {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :=
  (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus.rightAdjoint

/-- The fixed derived closed adjunction, with counit the derived support inclusion.
Source: Stacks Project, Tag 09XQ (blueprint: lem-per-ind-etale-closed-support-base-change). -/
def closedSupportPlusAdjunction {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] :
    (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus ⊣ closedSupportPlus A i :=
  Adjunction.ofIsLeftAdjoint _

/-- The canonical shifts of the closed right adjoint are the mates of the direct-image shifts.
Source: Stacks Project, Tag 09XQ (blueprint: lem-per-ind-etale-closed-support-base-change). -/
instance closedSupportPlusCommShift {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] : (closedSupportPlus A i).CommShift ℤ :=
  (closedSupportPlusAdjunction A i).rightAdjointCommShift ℤ

/-- Inverse of the canonical closed direct-image exchange, with a zero extension elsewhere.
The theorem asserts invertibility, so the zero branch is never used on its domain.
Source: Stacks Project, Tag 04CA (blueprint: lem-per-ind-etale-closed-support-base-change). -/
def closedSupportExchangeInverse
    {Z' Z T' T : Scheme.{u}} {h : Z' ⟶ Z} {i' : Z' ⟶ T'}
    {i : Z ⟶ T} {g : T' ⟶ T} (sq : CommSq h i' i g) :
    (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} A) i').rightDerivedFunctorPlus ⟶
      (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus ⋙
        (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus :=
  open Classical in
  if hc : IsIso (derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq) then
    @inv _ _ _ _ (derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq) hc
  else 0

/-- The canonical closed-support exchange: transpose the inverse closed exchange followed
by inverse image of the closed counit. This is a natural transformation of A-module
valued derived functors, so all its components are A-linear morphisms.
Source: Stacks Project, Tags 09XQ and 0A45
(blueprint: lem-per-ind-etale-closed-support-base-change). -/
def closedSupportBaseChangePlus
    {Z' Z T' T : Scheme.{u}} {h : Z' ⟶ Z} {i' : Z' ⟶ T'}
    {i : Z ⟶ T} {g : T' ⟶ T} [IsClosedImmersion i] [IsClosedImmersion i']
    (sq : CommSq h i' i g) :
    closedSupportPlus A i ⋙ (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategoryPlus ⟶
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus ⋙ closedSupportPlus A i' :=
  (mateEquiv (closedSupportPlusAdjunction A i) (closedSupportPlusAdjunction A i')
    (TwoSquare.mk _ _ _ _ (closedSupportExchangeInverse A sq))).natTrans

/-- The ind-etale support mate is invertible, shift compatible, and normalized by the
closed counits, with no constructibility hypothesis.
Source: Stacks Project, Tags 03Q9, 0A45 and 09XQ
(blueprint: lem-per-ind-etale-closed-support-base-change).
Proof, following the node's eleven steps:
1. The complementary opens are qcqs: Noetherian opens are quasi-compact, and open
   immersion diagonals are identities. Base change preserves the complementary pair.
2. Derive the supported-kernel adjunction on A-modules; its counit is support inclusion.
3. An injective resolution has degreewise surjective restriction to the complementary
   open. Its support-kernel short exact sequence gives the natural localization triangle.
4. The closed exchange is an isomorphism by geometric stalks: zero outside the support
   and the same germ on it. Exact closed pushforward is fully faithful on D+.
5. Transpose the inverse closed exchange followed by g^* of the closed counit; this is
   closedSupportBaseChangePlus, and gives precisely the displayed counit equation.
6. Strict localizations are invariant under ind-etale maps. Their pulled-back open
   complements are isomorphic, so exchange there is invertible.
7. The strict-local global-homology theorem (03Q9) identifies all cohomological degrees
   with closed geometric stalks, for both complementary open direct images.
8. The derived exchange cube and those identifications show that the original open
   exchange is invertible at every stalk. Forgetting coefficients detects this for A-modules.
9. Apply g^* to the support triangle. TR3 completes the identity and open exchange to a
   triangle map. Full faithfulness and the counit equation identify its first map with
   closed pushforward of exactly the specified support mate.
10. The cohomology ladder and five lemma make this first map invertible. The left inverse
    of closed pushforward then makes the support mate invertible.
11. Scalar actions are preserved throughout. Shifting resolutions shifts support inclusion
    and exchange; their transposes coincide. Counit uniqueness also gives the composition
    law stated below. The argument never assumes constructible cohomology. -/
theorem indEtale_closedSupport_baseChange
    {Z' Z T' T : Scheme.{u}} {h : Z' ⟶ Z} {i' : Z' ⟶ T'}
    {i : Z ⟶ T} {g : T' ⟶ T} [IsNoetherian T] [IsNoetherian T']
    [IsClosedImmersion i] [IsClosedImmersion i'] [IsAffineHom g]
    (hg : ∀ t : T', ∃ (V : T'.Opens) (U : T.Opens),
      t ∈ V ∧ IsAffine V.toScheme ∧ IsAffine U.toScheme ∧
      ∃ e : V.toScheme ⟶ U.toScheme,
        e ≫ U.ι = V.ι ≫ g ∧ RingHom.IndEtaleAcrossUniverses e.appTop.hom)
    (sq : IsPullback h i' i g) :
    IsIso (derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq.toCommSq) ∧
    IsIso (closedSupportBaseChangePlus A sq.toCommSq) ∧
    NatTrans.CommShift (closedSupportBaseChangePlus A sq.toCommSq) ℤ ∧
    ∀ K : _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (derivedBaseChangeMapPlus (ModuleCat.{u + 1} A) sq.toCommSq).app
          ((closedSupportPlus A i).obj K) ≫
        (lowerStar (ModuleCat.{u + 1} A) i').rightDerivedFunctorPlus.map
          ((closedSupportBaseChangePlus A sq.toCommSq).app K) ≫
        (closedSupportPlusAdjunction A i').counit.app
          ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.obj K) =
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.map
        ((closedSupportPlusAdjunction A i).counit.app K) := by
  sorry

/-- Successive affine ind-etale base changes compose through the canonical inverse-image
composition isomorphisms. All objects are arbitrary bounded-below complexes.
Source: Stacks Project, Tags 03Q9 and 09XQ
(blueprint: lem-per-ind-etale-closed-support-base-change).
Proof: closed direct-image exchange pastes because successive restrictions of sections
are their restriction along the composite. Transpose the right-hand composite using the
two closed adjunctions. Their counit equations reduce it to g₂^*g₁^* of the original
closed counit. The composite-square mate has the same transpose. Injectivity of the
adjunction Hom bijection gives the equality, with exactly the displayed canonical
composition identifications (Step 11 of the node). -/
theorem indEtale_closedSupport_baseChange_comp
    {Z Z₁ Z₂ T T₁ T₂ : Scheme.{u}}
    {i : Z ⟶ T} {i₁ : Z₁ ⟶ T₁} {i₂ : Z₂ ⟶ T₂}
    {h₁ : Z₁ ⟶ Z} {h₂ : Z₂ ⟶ Z₁} {g₁ : T₁ ⟶ T} {g₂ : T₂ ⟶ T₁}
    [IsClosedImmersion i] [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsNoetherian T] [IsNoetherian T₁] [IsNoetherian T₂]
    [IsAffineHom g₁] [IsAffineHom g₂]
    (hg₁ : ∀ t : T₁, ∃ (V : T₁.Opens) (U : T.Opens),
      t ∈ V ∧ IsAffine V.toScheme ∧ IsAffine U.toScheme ∧
      ∃ e : V.toScheme ⟶ U.toScheme,
        e ≫ U.ι = V.ι ≫ g₁ ∧ RingHom.IndEtaleAcrossUniverses e.appTop.hom)
    (hg₂ : ∀ t : T₂, ∃ (V : T₂.Opens) (U : T₁.Opens),
      t ∈ V ∧ IsAffine V.toScheme ∧ IsAffine U.toScheme ∧
      ∃ e : V.toScheme ⟶ U.toScheme,
        e ≫ U.ι = V.ι ≫ g₂ ∧ RingHom.IndEtaleAcrossUniverses e.appTop.hom)
    (sq₁ : IsPullback h₁ i₁ i g₁) (sq₂ : IsPullback h₂ i₂ i₁ g₂)
    (K : _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (closedSupportBaseChangePlus A (sq₂.toCommSq.horiz_comp sq₁.toCommSq)).app K ≫
        (closedSupportPlus A i₂).map
          ((upperStarCompDerivedPlus (ModuleCat.{u + 1} A) g₂ g₁).hom.app K) =
      (upperStarCompDerivedPlus (ModuleCat.{u + 1} A) h₂ h₁).hom.app
          ((closedSupportPlus A i).obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) h₂).mapDerivedCategoryPlus.map
          ((closedSupportBaseChangePlus A sq₁.toCommSq).app K) ≫
        (closedSupportBaseChangePlus A sq₂.toCommSq).app
          ((upperStar (ModuleCat.{u + 1} A) g₁).mapDerivedCategoryPlus.obj K) := by
  sorry

/-- The identity base change comparison is the identity under the canonical identity
inverse-image identifications.
Source: Stacks Project, Tag 09XQ
(blueprint: lem-per-ind-etale-closed-support-base-change).
Proof: transpose through the closed adjunction. Identity restriction fixes the closed
counit; the triangle identities and injectivity of transposition give the equation.
This is the identity case in Step 11 of the node. -/
theorem closedSupport_baseChange_id
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (K : _root_.DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (closedSupportBaseChangePlus A (IsPullback.id_horiz i).toCommSq).app K ≫
        (closedSupportPlus A i).map
          ((upperStarIdDerivedPlus (ModuleCat.{u + 1} A) T).hom.app K) =
      (upperStarIdDerivedPlus (ModuleCat.{u + 1} A) Z).hom.app
        ((closedSupportPlus A i).obj K) := by
  sorry

end AlgebraicGeometry.Etale
