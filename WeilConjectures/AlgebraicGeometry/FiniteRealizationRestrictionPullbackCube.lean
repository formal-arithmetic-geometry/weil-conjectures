/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedEtaleTensorOrigin.SupportedEtaleTensorOrigin
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryRestrictionPullbackSquare
public import WeilConjectures.AlgebraicGeometry.OpenScalarOperations.OpenScalarOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! The finite realization restriction/pullback cube.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
`thm-pur-finite-reduction-of-purity.proof.md`, Proof Step 2 (finite-reduction compatibility
of pullback; restriction face of the realization coordinates); Stacks Tags 03D2, 03D3, 00YV
and 04VG.
(blueprint: lem-pur-finite-realization-restriction-pullback-cube)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The canonical finite realization restriction/pullback square commutes.

The four sides are the section-normalized realization restriction square, the
canonical intrinsic and fixed pullback comparisons, and the identified-coefficient
restriction/pullback squares.  The equality is asserted on every unbounded derived
object, with no flatness, boundedness, finiteness, or constructibility assumption on
that object.

Proof (node lem-pur-finite-realization-restriction-pullback-cube):
1. Work with the ordinary sheaf functors e, r, p, b whose exact descents occur here. For a
   fixed `B`-sheaf `M` the two ordinary composites `a_M, c_M` start at the constant-ring
   inverse image of `U_Y e_Y^B M`; by the module inverse-image/direct-image adjunction a map
   out of it is determined by its composite with the pullback unit, and forgetting module
   structure is faithful.
2. Compute both adjuncts on a section `s`: `ρ_Y` leaves `s` unchanged, `π_A` sends the
   inverse-image unit to the realized fixed inverse-image unit and `β` keeps that section;
   on the other path `βrg` gives the same `B`-inverse-image unit, `π_B` its realized fixed
   unit and `ρ_X` keeps it. The scalar actions agree since `f⁻¹ φ_Y` intertwines the two
   constant-ring identifications. Hence `a_M = c_M`, naturally in `M`.
3. All ordinary functors are additive and exact (realization is an equivalence, restriction
   keeps the underlying sheaf, both inverse images are exact), so they act termwise on
   unbounded complexes and the equality of step 2 is an equality of chain maps.
4. Each face is the localization of its ordinary face with its factorization isomorphisms;
   uniqueness of lifted natural transformations and faithfulness of precomposition with the
   localization give the equality on the whole unbounded derived category; evaluate at `N`.
   No flatness of `φ` is used.
Source: `thm-pur-finite-reduction-of-purity.proof.md` (part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction), Proof Step 2; Stacks Tags 03D2, 03D3, 00YV, 04VG.
(blueprint: lem-pur-finite-realization-restriction-pullback-cube)
-/
theorem finiteRealizationRestrictionPullbackCube
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))) :
    (let E_A_Y := (Scheme.sfIntrinsicDerivedEquivalence Y A).functor
     let E_B_Y := (Scheme.sfIntrinsicDerivedEquivalence Y B).functor
     let E_A_X := (Scheme.sfIntrinsicDerivedEquivalence X A).functor
     let E_B_X := (Scheme.sfIntrinsicDerivedEquivalence X B).functor
     let U_Y := OpenScalarOperations.scalarRestriction φ Y
     let U_X := OpenScalarOperations.scalarRestriction φ X
     let Uhat_Y := SupportedEtaleTensorOrigin.fixedRestriction φ Y
     let Uhat_X := SupportedEtaleTensorOrigin.fixedRestriction φ X
     let P_A := Scheme.proEtaleConstantRingDerivedPullback A f
     let P_B := Scheme.proEtaleConstantRingDerivedPullback B f
     let Pfix_A := sfFixedDerivedPullback A f
     let Pfix_B := sfFixedDerivedPullback B f
     let ρ_Y := SupportedEtaleTensorOrigin.restrictionPresentation φ Y
     let ρ_X := SupportedEtaleTensorOrigin.restrictionPresentation φ X
     let π_A := reductionRealizationPullbackIso A f
     let π_B := reductionRealizationPullbackIso B f
     let β := Functor.mapDerivedCategorySquareIso
       (upperStarRestrictScalarsIso (ρ := SupportedEtaleTensorOrigin.liftedHom φ) f)
     let βrg := (Scheme.proEtaleRingRestrictionDerivedPullback f
       (Scheme.proEtaleConstantRing Y A) (Scheme.proEtaleConstantRing Y B)
       (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing X B)
       (Scheme.proEtaleConstantRingMap (T := Y) φ)
       (Scheme.proEtaleConstantRingMap (T := X) φ)
       (Scheme.proEtaleConstantRingComparison f A)
       (Scheme.proEtaleConstantRingComparison f B)
       (by
         simpa [Scheme.proEtaleConstantRingComparison,
           Scheme.proEtaleConstantRingMap] using
           (Scheme.proEtaleConstantInverseImageMap_naturality f
             (a := CommRingCat.ofHom (RingHom.ulift φ))).symm)).symm
     P_A.map (ρ_Y.hom.app N) ≫
         (π_A.hom.app (Uhat_Y.obj N)) ≫
         E_A_X.map (β.hom.app N) =
       βrg.hom.app (E_B_Y.obj N) ≫
         U_X.map (π_B.hom.app N) ≫
         ρ_X.hom.app (Pfix_B.obj N)) := by
  sorry

end AlgebraicGeometry.ProEtale
