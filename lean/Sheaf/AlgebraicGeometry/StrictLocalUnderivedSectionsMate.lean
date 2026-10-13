/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm
public import WeilConjectures.SixFunctors.BaseChange.Square

/-! # The underived mate on pointed neighbourhood sections -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The underived exchange map evaluated after restriction to the strict-local base.
Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-strict-local-underived-sections-mate). -/
noncomputable def strictLocalUnderivedMateSections {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    lowerStar AddCommGrpCat.{v + 1} f ⋙
        (sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
          (op ((strictLocalNeighbourhoods s).obj i)) ⟶
      upperStar AddCommGrpCat.{v + 1}
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) ⋙
        Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
          AddCommGrpCat.{v + 1} :=
  Functor.whiskerLeft (lowerStar AddCommGrpCat.{v + 1} f)
      (strictLocalSectionRestrictionNat s i) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (baseChangeMap AddCommGrpCat.{v + 1}
        (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)).toCommSq)
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      (upperStar AddCommGrpCat.{v + 1}
        (pullback.fst f (Scheme.strictHenselizationStructuralMap s)))
      (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1}
        (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).hom

/-- Evaluating the underived mate on sections is restriction along the cone leg.
This is an equality of transformations of sheaves, before complexes or derivation.

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-strict-local-underived-sections-mate).

Proof: expand the restriction on the base as the inverse-image adjunction unit
followed by evaluation at the pointed neighbourhood section. Expand baseChangeMap
as the unit along the second pullback projection, the inverse-image square
comparison, and the counit along f. Naturality of evaluation moves the latter
maps across the neighbourhood section. The two adjunction triangle identities
cancel the intermediate unit and counit. The result is evaluation of f_*F on
the stage, identified by sourceStageSectionsIso, followed by sectionsPullbackNat
along the cone leg and the inverse composition comparison upperStarComp.
Q.first identifies the map on the base with the pointed neighbourhood section;
Q.over identifies the composite projection to X. These equations determine the
map into the scheme pullback, so both evaluations use the same map. All operations
are functorial in F, giving the equality of natural transformations. No etaleness
of the cone leg is needed. The zero sheaf and empty fibre use the same identities. -/
theorem strictLocalUnderivedMateSections_eq {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (Q : StrictLocalNeighbourhoodGeometry f s)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    strictLocalUnderivedMateSections f s i =
      (sourceStageSectionsIso f s i).hom ≫
        Functor.whiskerLeft
          (upperStar AddCommGrpCat.{v + 1} ((strictLocalNeighbourhoodProjection f s).app i))
          (sectionsPullbackNat (Q.legs.app i)) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (upperStarComp AddCommGrpCat.{v + 1} (Q.legs.app i)
            ((strictLocalNeighbourhoodProjection f s).app i)
            (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) (Q.over i).symm).inv
          (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
            AddCommGrpCat.{v + 1}) := by sorry

end AlgebraicGeometry.Etale
