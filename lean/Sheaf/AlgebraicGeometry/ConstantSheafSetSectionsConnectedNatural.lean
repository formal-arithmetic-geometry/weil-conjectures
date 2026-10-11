/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable
public import Sheaf.AlgebraicGeometry.EtaleSheaves

/-!
# Constant etale sheaf sections on a connected scheme

Source: Stacks Project, Remark 59.23.2 (Tag 03P5), set-valued form, and
Modules on Sites, Section 18.43 (Tags 093I and 093R)
(blueprint: lem-weil-pbc-constant-sheaf-set-sections-connected-natural).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- On a nonempty connected scheme over an algebraically closed field, the canonical
constant-section map is bijective. Under every morphism over the field its pullback
is the constant section with the same value, without connectedness of the source.
Source: Stacks Project, Remark 59.23.2 (Tag 03P5), and Tags 093I and 093R
(blueprint: lem-weil-pbc-constant-sheaf-set-sections-connected-natural).

Proof: `lem-galois-constant-sheaf-sets-representable` identifies the constant sheaf
with the sheaf represented by the disjoint union of copies of the base, carrying
`e` to its coprojection. By `lem-galois-coproduct-copies-morphisms-clopen`, a section
is an indexed clopen decomposition. The nonempty connected base forces this
decomposition to have exactly one nonempty piece, by
`lem-weil-pbc-connected-locally-constant-map`, proving bijectivity.
For a morphism `v`, apply `lem-weil-pbc-sets-etale-inverse-image-constant-sheaf`;
its canonical isomorphism carries the unit-pullback of the section of value `e`
to that same constant value. The unit notation and its compatibilities are supplied
by `lem-weil-pbc-sets-etale-inverse-image-composition-units`. No condition on `V`
is used. In the formula the base-changed terminal object is `U ×_U V`, canonically
isomorphic to `V`, so its sections are global sections on `V`. -/
theorem constantSheaf_set_sections_connected_natural
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (U : Scheme.{u}) [U.Over (Spec (.of Ω))] [ConnectedSpace U] (E : Type u) :
    Function.Bijective (fun e : E =>
      (toSheafify U.smallEtaleTopology
        ((Functor.const U.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))).app
          (Opposite.op (Etale.mk (𝟙 U))) ⟨e⟩) ∧
    ∀ (V : Scheme.{u}) [V.Over (Spec (.of Ω))] (v : V ⟶ U) [v.IsOver (Spec (.of Ω))],
      let b := MorphismProperty.Over.pullback @Etale ⊤ v
      let F := (constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
        (ULift.{u + 1, u} E)
      let G := (constantSheaf V.smallEtaleTopology (Type (u + 1))).obj
        (ULift.{u + 1, u} E)
      let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        b (Type (u + 1)) (U.smallGrothendieckTopology @Etale)
          (V.smallGrothendieckTopology @Etale)
      ∃ γ : (etaleSetPullback v).obj F ≅ G, ∀ e : E,
        γ.hom.hom.app (Opposite.op (b.obj (Etale.mk (𝟙 U))))
          (((adj.unit.app F).hom.app (Opposite.op (Etale.mk (𝟙 U))))
            ((toSheafify U.smallEtaleTopology
              ((Functor.const U.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))).app
                (Opposite.op (Etale.mk (𝟙 U))) ⟨e⟩)) =
          (toSheafify V.smallEtaleTopology
            ((Functor.const V.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))).app
              (Opposite.op (b.obj (Etale.mk (𝟙 U)))) ⟨e⟩ := by
  sorry

end AlgebraicGeometry.Scheme
