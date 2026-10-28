/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Paper.FiniteRingFixedCoordinates
public import Sheaf.Paper.ProEtaleProperOpenUnitNormalization
public import Sheaf.Paper.RingOpenMapOpenUnit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful

/-! # Endomorphism coordinates of open restriction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

/-- Finite coefficient realization conjugates the endomorphism obtained by taking
an arbitrary open-adjunction transpose and restricting the proper image.
There is no proper/open comparison or etale-origin witness in this assertion.
Source: compactification-coherence proof, first two paragraphs; Stacks 00YV,
03DI, 03D6, 0D6D (blueprint: lem-sf-finite-ring-open-restriction-coordinates).

Proof: before deriving, finiteDirectImage_eq identifies the two direct images
with the same constant-section scalar map. The left-adjoint uniqueness comparison
finitePullbackIso therefore preserves its unit and counit. By its definition,
finiteOpenIso is the left-adjoint uniqueness comparison for the resulting open
adjunction, so it preserves the open unit. The fixed realization comparisons
cancel the realization unit in inverse image and extension by zero; their direct
image comparison is its counit-normalized mate. These equations descend to the
derived categories by the exact localization and right-derived factorization
identities. The section-normalized ordinary direct-image compositor is the
conjugate of geometricPullComposition. Consequently the restriction square is
the pasting of the pullback composition square and the proper counit square.
Apply the open unit square, naturality to the arbitrary arrow m, the restriction
square, and then the inverse open unit square. All inner coordinate isomorphisms
cancel, leaving conjugation by a. This uses no invertibility of m and no
properness of r. Identity maps, empty opens, and zero coefficients use precisely
the same unit/counit and inverse-pair identities. -/
theorem finiteOpenRestriction_endomorphism_coordinates
    (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{w}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d)
    (hi : (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (c.i ≫ r.hom) =
      proEtaleRingCompositeCoefficients c.i r.hom
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring d.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring c.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring X)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull r.hom)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull c.i))
    (K : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1))))))
    (M : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
    (a : M ≅ (sfIntrinsicDerivedEquivalence X
      (Padic.coefficientExtensionRing l E (n + 1))).functor.obj K)
    (m : (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
        (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1))))
        d.i).mapDerivedCategory.obj K ⟶
      (AlgebraicGeometry.ProEtale.lowerStar
        (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1))))
        r.hom).rightDerivedFunctor.obj
        ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek
          (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1))))
          c.i).mapDerivedCategory.obj K)) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let B := ModuleCat.{w + 1} (ULift.{w + 1} A)
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    let J₁ := (PurCompactSupport.openExtension R c.i).mapDerivedCategory
    let J₂ := (PurCompactSupport.openExtension R d.i).mapDerivedCategory
    let o₁ := J₁.mapIso a ≪≫ (finiteFixedOpenIso l E n c.i).app K
    let o₂ := J₂.mapIso a ≪≫ (finiteFixedOpenIso l E n d.i).app K
    let m' := o₂.hom ≫ (sfIntrinsicDerivedEquivalence d.Z A).functor.map m ≫
      (finiteFixedPushIso l E n r.hom).inv.app
        ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek B c.i).mapDerivedCategory.obj K) ≫
      (PurCompactSupport.push R r.hom).map o₁.inv
    letI : IsIso (PurCompactSupport.openDerivedAdjunction R c.i).unit :=
      PurCompactSupport.openDerivedAdjunction_unit_isIso R c.i
    letI : IsIso (AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      B c.i).unit := Adjunction.isIso_mapDerivedCategoryAdjunction_unit
      (AlgebraicGeometry.ProEtale.openImmersionLowerShriekUpperStarAdjunction B c.i)
    ((PurCompactSupport.openDerivedAdjunction R d.i).homEquiv _ _ m' ≫
      PurCompactSupport.refinementRestriction R r hi M) ≫
        (asIso (PurCompactSupport.openDerivedAdjunction R c.i).unit).inv.app M =
      a.hom ≫ (sfIntrinsicDerivedEquivalence X A).functor.map
        (((AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
            B d.i).homEquiv _ _ m ≫
          (AlgebraicGeometry.ProEtale.properOpenRestriction (ULift.{w + 1} A)
            r.hom c.i d.i r.i_hom).app
            ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek B c.i
              ).mapDerivedCategory.obj K)) ≫
          (asIso (AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
            B c.i).unit).inv.app K) ≫ a.inv := by sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
