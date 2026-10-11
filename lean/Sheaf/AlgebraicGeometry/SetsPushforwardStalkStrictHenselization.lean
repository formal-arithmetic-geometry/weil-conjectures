/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # Stalk of a direct image over the strict henselization

Source: Stacks Project, Tag 03Q9, degree zero for sets, with Tags 09YQ and 09YU
(blueprint: lem-weil-pbc-sets-pushforward-stalk-strict-henselization).
-/

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The compatibility needed to map the base-changed strict henselization to V ×_Y X, for a
representative affine pointed neighbourhood `j` with leg `c_V` (the limit leg followed by
`Spec Γ(V, ⊤) ≅ V`).
Source: Stacks Project, Tag 03Q9, fibre products commuting with limits
(blueprint: lem-weil-pbc-sets-pushforward-stalk-strict-henselization).
Proof: by `exists_strictHenselizationStructuralMap`, `c_V` followed by `V ⟶ Y` is
`strictHenselizationStructuralMap y`; then use `pullback.condition`. -/
theorem strictHenselizationBaseChange_condition
    {X Y : Scheme.{v}} (f : X ⟶ Y)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) :
    (pullback.fst (strictHenselizationStructuralMap y) f ≫
        (strictHenselizationCone y).π.app (op (op j)) ≫
          Spec.map (ΓSpecIso
            ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj
              j).1.left.unop).inv) ≫
        ((AffineEtale.Spec Y).obj
          ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1).hom =
      pullback.snd (strictHenselizationStructuralMap y) f ≫ f := by
  sorry

/-- The map X^sh → V ×_Y X with components c_V ∘ f^sh and p, for a representative affine
pointed neighbourhood `j`.
Source: Stacks Project, Tag 03Q9, fibre products commuting with limits
(blueprint: lem-weil-pbc-sets-pushforward-stalk-strict-henselization). -/
noncomputable def strictHenselizationBaseChangeMap
    {X Y : Scheme.{v}} (f : X ⟶ Y)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) :
    pullback (strictHenselizationStructuralMap y) f ⟶
      pullback ((AffineEtale.Spec Y).obj
        ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1).hom f :=
  pullback.lift
    (pullback.fst (strictHenselizationStructuralMap y) f ≫
      (strictHenselizationCone y).π.app (op (op j)) ≫
        Spec.map (ΓSpecIso
          ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj
            j).1.left.unop).inv)
    (pullback.snd (strictHenselizationStructuralMap y) f)
    (strictHenselizationBaseChange_condition f y j)

/-- The site morphism σ_V from the final object to the iterated fibre product.
Source: Stacks Project, Tag 03Q9, canonical section restriction
(blueprint: lem-weil-pbc-sets-pushforward-stalk-strict-henselization). -/
noncomputable def strictHenselizationSectionMap
    {X Y : Scheme.{v}} (f : X ⟶ Y)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) :
    Etale.mk (𝟙 (pullback (strictHenselizationStructuralMap y) f)) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤
        (pullback.snd (strictHenselizationStructuralMap y) f)).obj
          ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
            ((AffineEtale.Spec Y).obj
              ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)) :=
  MorphismProperty.Over.homMk
    (pullback.lift (strictHenselizationBaseChangeMap f y j) (𝟙 _)
      (pullback.lift_snd _ _ _)) (pullback.lift_snd _ _ _)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open Scheme

/-- Every direct-image germ has an affine representative, and the canonical comparison
with sections on the strict henselization pullback is the unique map with the unit and
restriction formula, and is bijective.
Source: Stacks Project, Tag 03Q9, degree zero for sets, with Tags 09YQ and 09YU
(blueprint: lem-weil-pbc-sets-pushforward-stalk-strict-henselization).

Proof:
1. Use `def-weil-pbc-strict-henselization-limit` and `def-pc-fibre-product` for the
   neighbourhood and base-changed limit diagrams. By
   `lem-weil-pbc-qcqs-morphism-permanence`, the base changes are qcqs; their transitions
   are affine. Apply `lem-weil-pbc-filtered-category-directed-cofinal` to the opposite
   of the small neighbourhood category. The same directed cofinal family computes
   both section colimits and the inverse limits, using
   `lem-weil-pbc-limit-affine-transition` and `lem-weil-pbc-spec-small-colimit-limit`.
2. Apply `lem-weil-pbc-sets-etale-section-continuity` to this system and the pullback
   of H to a fixed stage. The composition isomorphisms of
   `lem-weil-pbc-sets-etale-inverse-image-composition-units` identify the resulting
   limit sheaf with p⁻¹H. By `lem-weil-pbc-sets-etale-inverse-image-restriction`,
   sections at each stage identify with H(V ×_Y X), and the units and composition
   equations identify the transition maps with restrictions of f_*H.
3. The component of the section colimit comparison at a representative V is
   restriction along σ_V of the unit image p*s. The unit equations in
   `lem-weil-pbc-sets-etale-inverse-image-composition-units` give compatibility under
   pointed refinement.
4. By `def-weil-pbc-geometric-stalks` and
   `lemma-weil-pbc-affine-neighbourhood-cofinal`, the affine section colimit is the
   geometric stalk. Every element therefore has an affine representative. The
   colimit component formula uniquely determines Θ; continuity makes it bijective. -/
theorem sets_pushforward_stalk_strictHenselization
    {X Y : Scheme.{v}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (H : Sheaf X.smallEtaleTopology (Type (v + 1)))
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    (∀ t : ((pointSmallEtale y).sheafFiber.obj
      (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous (Type (v + 1))
        (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)).obj H)),
      ∃ (n : ObjectProperty.FullSubcategory
        (fun n : (pointSmallEtale y).fiber.Elements => IsAffine n.1.left))
        (s : H.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj n.obj.1))),
        (pointSmallEtale y).toPresheafFiber n.obj.1 n.obj.2
          (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
            (Type (v + 1)) (Y.smallGrothendieckTopology @Etale)
            (X.smallGrothendieckTopology @Etale)).obj H).obj s = t) ∧
    ∃ Θ : ((pointSmallEtale y).sheafFiber.obj
      (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous (Type (v + 1))
        (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)).obj H)) →
      ((etaleSetPullback (pullback.snd (strictHenselizationStructuralMap y) f)).obj H).obj.obj
        (op (Scheme.Etale.mk (𝟙 (pullback (strictHenselizationStructuralMap y) f)))),
      (∀ (j : SmallModel.{v} (strictHenselizationNeighbourhoods y))
        (s : H.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
          ((AffineEtale.Spec Y).obj
            ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)))),
        Θ ((pointSmallEtale y).toPresheafFiber
            ((AffineEtale.Spec Y).obj
              ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)
            ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).2
          (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
            (Type (v + 1)) (Y.smallGrothendieckTopology @Etale)
            (X.smallGrothendieckTopology @Etale)).obj H).obj s) =
          ((etaleSetPullback (pullback.snd (strictHenselizationStructuralMap y) f)).obj
            H).obj.map (strictHenselizationSectionMap f y j).op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤
                (pullback.snd (strictHenselizationStructuralMap y) f))
              (Type (v + 1)) (X.smallGrothendieckTopology @Etale)
              ((pullback (strictHenselizationStructuralMap y) f).smallGrothendieckTopology
                @Etale)).unit.app H).hom.app
                (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
                  ((AffineEtale.Spec Y).obj
                    ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)))
                s)) ∧
      Function.Bijective Θ ∧
      ∀ Θ' : ((pointSmallEtale y).sheafFiber.obj
      (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous (Type (v + 1))
        (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)).obj H)) →
        ((etaleSetPullback (pullback.snd (strictHenselizationStructuralMap y) f)).obj H).obj.obj
        (op (Scheme.Etale.mk (𝟙 (pullback (strictHenselizationStructuralMap y) f)))),
        (∀ (j : SmallModel.{v} (strictHenselizationNeighbourhoods y))
        (s : H.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
          ((AffineEtale.Spec Y).obj
            ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)))),
        Θ' ((pointSmallEtale y).toPresheafFiber
            ((AffineEtale.Spec Y).obj
              ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)
            ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).2
          (((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
            (Type (v + 1)) (Y.smallGrothendieckTopology @Etale)
            (X.smallGrothendieckTopology @Etale)).obj H).obj s) =
          ((etaleSetPullback (pullback.snd (strictHenselizationStructuralMap y) f)).obj
            H).obj.map (strictHenselizationSectionMap f y j).op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤
                (pullback.snd (strictHenselizationStructuralMap y) f))
              (Type (v + 1)) (X.smallGrothendieckTopology @Etale)
              ((pullback (strictHenselizationStructuralMap y) f).smallGrothendieckTopology
                @Etale)).unit.app H).hom.app
                (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
                  ((AffineEtale.Spec Y).obj
                    ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)))
                s)) →
        Θ' = Θ := by
  sorry

end AlgebraicGeometry
