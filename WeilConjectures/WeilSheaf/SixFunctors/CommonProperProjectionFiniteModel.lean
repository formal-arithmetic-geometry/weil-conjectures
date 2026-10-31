/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Proper.NativeProperProjectionComparisons

/-! # A finite coefficient-field model of the common-stage proper projection

Source: BS 6.8.14--6.8.15 and thm-sf-pf-field, common-stage compatibility.
(blueprint: lem-sf-common-proper-projection-finite-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.commonStageDerivedPullback WeilConjectures.commonStageDerivedTensor
  WeilConjectures.geometricCommonStageDirectImage
  WeilConjectures.geometricCommonStageAdjunction
  WeilConjectures.rationalDerivedPullback WeilConjectures.rationalDerivedTensor
  WeilConjectures.canonicalRationalPullbackTensor
  WeilConjectures.canonicalCommonStagePullbackTensor

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

open scoped AlgebraicGeometry.ProEtaleWeilSheaf
namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]

/-- Finite-stage inclusion compares pullback, tensor and the actual adjunction
counits. No projection map or projection invertibility is asserted.
Source: thm-sf-pf-field.proof.md, compatibility paragraph;
BS 6.7.2 and 6.8.14--6.8.15; Step 1 of the ordinary projection proof.
(blueprint: lem-sf-common-proper-projection-finite-model).

Proof: localize the integral pullback/direct-image adjunction at the finite
coefficient field E. Finite scalar extension has invertible right-adjoint
mates, so these adjunctions descend through the common-stage quotient.
Uniqueness of right adjoints compares the descended adjunction with the
specified geometricCommonStageAdjunction; this gives b and its counit equation.
The canonical common-stage pullback comparison gives a. The representative
formula for common-stage tensor supplies tX and tY: on integral representatives
these are balanced scalar-extension associativity, and on rational arrows they
are their localizations. Their scalar cocycle makes them natural isomorphisms
on all finite-stage arrows. For the tensor equation, insert the defining
finite representative of canonicalCommonStagePullbackTensor. Both composites
are the included rational pullback tensor comparison; cancel the canonical
inclusion tensor comparisons. For the counit equation, use the descended
finite-stage counit and the unique adjunction-compatible right comparison.
This calculation is independent of any projection formula. Identity field
extensions use the tensor unit, and the same formulas cover zero objects,
empty schemes and identity maps. -/
theorem properCommonProjection_finiteStageComparison [IsProper p]
    (hl : IsUnit (l : AlgebraicClosure k₀))
    [∀ x : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      Invertible (l : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField x)]
    [∀ y : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      Invertible (l : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField y)]
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :
    let F := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
    let X := (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber
    let W := (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber
    let f := NativeBaseChange.geometricMap k₀ p
    let IX := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E
    let IY := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := W) E
    let FC := commonStageDerivedPullback l (PadicAlgCl l) f
    let GC := properCommonPush k₀ l p hl
    let TCX := commonStageDerivedTensor l (PadicAlgCl l) X
    let TCY := commonStageDerivedTensor l (PadicAlgCl l) W
    ∃ (G : sfRationalConstructibleCategory l F X ⥤ sfRationalConstructibleCategory l F W)
      (adj : rationalDerivedPullback l F f ⊣ G)
      (tX : (IX.prod IX) ⋙ TCX ≅ rationalDerivedTensor l F X ⋙ IX)
      (tY : (IY.prod IY) ⋙ TCY ≅ rationalDerivedTensor l F W ⋙ IY)
      (a : rationalDerivedPullback l F f ⋙ IX ≅ IY ⋙ FC)
      (b : G ⋙ IY ≅ IX ⋙ GC),
      (∀ P Q : sfRationalConstructibleCategory l F W,
        IX.map (canonicalRationalPullbackTensor l F f P Q).hom ≫
          tX.inv.app ((rationalDerivedPullback l F f).obj P,
            (rationalDerivedPullback l F f).obj Q) ≫
          TCX.map (Prod.mkHom (a.hom.app P) (a.hom.app Q)) =
        a.hom.app ((rationalDerivedTensor l F W).obj (P, Q)) ≫
          FC.map (tY.inv.app (P, Q)) ≫
          (canonicalCommonStagePullbackTensor l (PadicAlgCl l) f
            (IY.obj P) (IY.obj Q)).hom) ∧
      ∀ K : sfRationalConstructibleCategory l F X,
        IX.map (adj.counit.app K) = a.hom.app (G.obj K) ≫
          FC.map (b.hom.app K) ≫
          (geometricCommonStageAdjunction l (PadicAlgCl l)
            (AlgebraicClosure k₀) hl f).counit.app (IX.obj K) := by sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
