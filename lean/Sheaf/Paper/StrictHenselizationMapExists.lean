/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.RingTheory.ProEtale.HenselianLocalRing
import Sheaf.AlgebraicGeometry.StrictHenselization

/-! # Existence of the local strict-henselization map

Source: Stacks Project, Tags 03PS, 04GU and 08HR
(blueprint: lem-weil-pbc-strict-henselization-map-exists).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- Existence of a local map over the base with the prescribed pointed residue map.
Source: Stacks Project, paragraph after Tag 03PS, Tags 04GU and 08HR
(blueprint: lem-weil-pbc-strict-henselization-map-exists).

Proof: Put C = strictHenselizationRing barT and let t : Spec Omega -> Spec C
be the given residue embedding. Its factorizations imply t followed by the
structural map is barT, and locality of the residue embedding makes its image
the closed point. The local-structure theorem makes C strictly henselian.
For each affine pointed etale neighbourhood V of barS, pull V back along
Spec C -> T -> S. Choose an affine chart through the marked point of the pullback,
with coordinate ring B and marked prime q. The local map C -> B_q is weakly etale.
Olivier's theorem (Stacks Tag 092Z), in
`Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing`, makes it an
isomorphism. Its inverse gives a section. The field-valued point's ring map
extends to B_q, so the section preserves that point, not just its underlying prime.
These sections give maps Spec C -> V over S preserving the chosen point.
Two such maps agree: the etale diagonal is open, the marked closed point lies
in its range, and every point of Spec C generalizes the closed point. Thus their
pair factors through the diagonal. This proves compatibility of the maps with
all transition morphisms. Conjugating by the affine spectrum identifications
gives a cone. The strict-henselization limit supplies u : Spec C -> Spec C_S;
full faithfulness of Spec supplies h : C_S -> C. Its composites with the cone
legs give the structural-map equality. Limit extensionality and the prescribed
pointed factorizations give t followed by u equal to the point defined by sigmaS,
hence the required equality of ring maps into Omega. Since that composite is
local, `isLocalHom_of_comp` proves h local. The extra hypotheses hOmegaS and
hOmegaT are unnecessary in this route because the pointed factorizations are
already supplied; their signatures are retained unchanged.
Source for the section argument: Stacks Tags 03QO and 092Z; the pointed
localization calculation also occurs inside
`Sheaf.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk` as a private proof.
-/
theorem strictHenselizationMapExists
    {S T : Scheme.{v}} (g : T ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barT : Spec (.of Ω) ⟶ T) (barS : Spec (.of Ω) ⟶ S)
    (hbar : barS = barT ≫ g)
    [Algebra (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω]
    [Algebra (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω]
    (hΩS : algebraMap (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barS)).hom)
    (hΩT : algebraMap (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barT)).hom)
    [IsLocalRing (Scheme.strictHenselizationRing barS)]
    [IsLocalRing (Scheme.strictHenselizationRing barT)]
    (σS : IsLocalRing.ResidueField (Scheme.strictHenselizationRing barS) ≃+*
      separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)
    (σT : IsLocalRing.ResidueField (Scheme.strictHenselizationRing barT) ≃+*
      separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)
    (hσS : ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barS),
      Spec.map (CommRingCat.ofHom
          (((IntermediateField.val
            (separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              σS.toRingHom).comp
            (IsLocalRing.residue (Scheme.strictHenselizationRing barS)))) ≫
          (Scheme.strictHenselizationCone barS).π.app (Opposite.op (Opposite.op j)) ≫
            (Spec (Opposite.unop ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj j).2.left)
    (hσT : ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barT),
      Spec.map (CommRingCat.ofHom
          (((IntermediateField.val
            (separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              σT.toRingHom).comp
            (IsLocalRing.residue (Scheme.strictHenselizationRing barT)))) ≫
          (Scheme.strictHenselizationCone barT).π.app (Opposite.op (Opposite.op j)) ≫
            (Spec (Opposite.unop ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj j).2.left) :
    ∃ h : Scheme.strictHenselizationRing barS ⟶ Scheme.strictHenselizationRing barT,
      IsLocalHom h.hom ∧
      Spec.map h ≫ Scheme.strictHenselizationStructuralMap barS =
        Scheme.strictHenselizationStructuralMap barT ≫ g ∧
      (((IntermediateField.val
          (separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
            σS.toRingHom).comp
          (IsLocalRing.residue (Scheme.strictHenselizationRing barS))) =
        ((((IntermediateField.val
          (separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
            σT.toRingHom).comp
          (IsLocalRing.residue (Scheme.strictHenselizationRing barT)))).comp h.hom := by
  sorry


end AlgebraicGeometry
