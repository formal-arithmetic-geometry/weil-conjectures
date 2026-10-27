/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Paper.AffineDiagonalSectionCoordinates

/-! # DNC identity in geometric affine diagonal coordinates

Source: smooth-purity, Agreement on the model, standard-pair deformation.
(blueprint: lem-pur-affine-diagonal-dnc-coordinate-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] affineDiagonalNormalCoordinates
  affineDiagonalNormalFunction affineDiagonalDifferenceLift
  Etale.FiniteSmoothPurity.ReesConeNormalized
  affineDiagonalSectionCoordinates affineDiagonalSourceCoordinates
  affineDiagonalNormalSectionCoordinates

/-- The normalized deformation arrow is identity in the geometric section coordinates.
This statement has no exponent, Tate orientation, or integration transpose in it.
Source: latest blueprint, smooth-purity, projection-purity agreement, standard-pair
paragraph; DNC section geometry (4) and normalized DNC invariance.
(blueprint: lem-pur-affine-diagonal-dnc-coordinate-identity).

Proof: the proved difference-coordinate map identifies (W,p1,diagonal) with the
standard affine pair over X. Its section is zero by the proved translated-coordinate
zero identity. Apply the
extended-Rees functor to this isomorphism of pairs. In polynomial charts it is
R[x,y,t,(y-x)/t] = R[x,t,v], with y-x=t*v, so it identifies the whole deformation
with affine d-space over A1_X. Its fibre at one is the difference-coordinate map;
its fibre at zero is exactly affineDiagonalNormalCoordinates: ReesConeNormalized
fixes every degree-one class, not just the isomorphism class of the bundle.
The canonical exceptional mate for this family isomorphism identifies its section
invariant with the pullback of the standard section invariant. Mate pasting and
derived pullback composition identify the two sectionRestrictionIso readings with
sourceComparison followed by the source coordinate map, and normalComparison
followed by the normal coordinate map, respectively. Apply the normalization
predicate of existsUnique_dncInvariance at the identity base change and this family
trivialization. Cancel the canonical identity pullback comparisons to obtain the
displayed equation. For d=0 there are no generators, and the same Rees and mate
identities are identity identities. They also hold over the empty base. -/
theorem affineDiagonalDncCoordinateIdentity (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] (d : ℕ) :
    let p := affineDiagonalProjection Y d
    let s := pullback.diagonal p
    let aX := p ≫ aY
    letI := affineDiagonalProjection_smooth Y d
    letI := SmoothOfRelativeDimension.smooth d p
    letI := Dnc.compactifiable P p aY
    let δ := (Dnc.existsUnique_dncInvariance P d (pullback.fst p p) aX s
      (pullback.diagonal_fst p)).exists.choose
    let C := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) (affineDiagonalSpace Y d)).mapDerivedCategory
    ∀ (q : s.ker.normalCone ≅ PurityNormalBundle.normalCone s)
      (hq : Etale.FiniteSmoothPurity.ReesConeNormalized s q),
      δ.hom ≫ (Dnc.normalComparison P d (pullback.fst p p) aX s
          (pullback.diagonal_fst p)).hom ≫
        C.map (P.affineDiagonalNormalSectionCoordinates Y aY d q hq).hom =
      (Dnc.sourceComparison P d (pullback.fst p p) aX s).hom ≫
        C.map (P.affineDiagonalSourceCoordinates Y aY d).hom := by sorry

end WeilConjectures.PurityFiniteSetting
