/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.Paper.StrictHenselizationLocalStructure
import Sheaf.Paper.StrictHenselizationPointedMap
import Sheaf.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.RingTheory.MapIntoHenselianColimit

/-! # Existence of the local strict-henselization map

Source: Stacks Project, Tags 03PS, 04GU and 08HR
(blueprint: lem-weil-pbc-strict-henselization-map-exists).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Existence of a local map over the base with the prescribed pointed residue map.
Source: Stacks Project, paragraph after Tag 03PS, Tags 04GU and 08HR
(blueprint: lem-weil-pbc-strict-henselization-map-exists).

Proof: The residue-field map of barS = barT followed by g is the composite of
those of g and barT. The hypotheses hOmegaS and hOmegaT identify these with the
chosen algebra maps into Omega. A polynomial separable over the smaller residue
field stays separable over the larger one, so the relative separable closure for
S is contained in that for T. Choose an affine open U = Spec A containing the
point s. The local structure and pointed-map theorems identify the closed points
and residue fields of both neighbourhood colimits. The map from the local
spectrum of the T colimit to S factors through U because its closed point maps
to s; all other points generalize the closed point. This gives an A-algebra
structure on the T colimit. The theorem `Scheme.etale_local_ring_triples` identifies
the S colimit with a filtered colimit of etale A-algebras. Its maximal ideal lies
over the prime p of s, also the contraction of the T maximal ideal. The inclusion
of relative separable closures, conjugated by sigmaS and sigmaT, is therefore a
map of residue fields over kappa(p). Apply `Algebra.map_into_henselian_colimit`
using strict henselianity of the T colimit to obtain the A-algebra map h. Its
inverse-image maximal ideal is the maximal ideal on S, so h is local. Its
prescribed residue-field map gives the displayed equality of maps to Omega.
Being an A-algebra map gives equality after composing with U -> S, which is
the displayed structural-map diagram. No uniqueness or compatibility with
arbitrary neighbourhood morphisms is asserted in this lemma.
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
          (IsLocalRing.residue (Scheme.strictHenselizationRing barT)))).comp h.hom := by sorry

end AlgebraicGeometry
