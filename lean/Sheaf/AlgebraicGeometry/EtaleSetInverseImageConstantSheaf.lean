/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheafExists
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheafUnique
import Sheaf.AlgebraicGeometry.Sites.InverseImageRepresentable
import Sheaf.Paper.SetsEtaleInverseImageConstantBaseChange

/-! # Inverse image of a set-valued constant étale sheaf is constant

Source: literature/stacks-project/sites-modules.tex, Section 18.43 (Tag 093I)
and Lemma 093R (blueprint: lem-weil-pbc-sets-etale-inverse-image-constant-sheaf).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The inverse image of a constant set-valued étale sheaf is canonically constant.
Source: Stacks Project, Modules on Sites, Tag 093R, and Sites, Example 0H7J
(blueprint: lem-weil-pbc-sets-etale-inverse-image-constant-sheaf).

Proof:
1. By `lem-galois-constant-sheaf-sets-representable`, represent the constant sheaf
   over U by the coproduct of copies of U indexed by E, carrying each canonical
   section to the corresponding coprojection.
2. By `lem-weil-pbc-scheme-coproduct-family`, the summands are disjoint open
   subschemes covering this coproduct. The codiagonal is an isomorphism on each
   summand, hence étale; the coprojections are morphisms of the small étale site.
3. Apply `lem-galois-inverse-image-representable` to this étale object. Its
   naturality at the coprojections, with the unit compatibilities of
   `lem-weil-pbc-sets-etale-inverse-image-composition-units`, identifies the
   pulled-back canonical sections with the base-changed coprojections.
4. By `lem-weil-pbc-sets-etale-inverse-image-constant-base-change`, the base-changed
   coproduct is the coproduct of copies of V, compatibly with the coprojections.
   Compose with the inverse of the representation over V to obtain γ and its
   displayed equations.
5. Each factor is an isomorphism, so γ is an isomorphism. The equations prescribe
   the images of every canonical coprojection section. The representation and
   sheafification universal property of `lem-galois-constant-sheaf-sets-representable`
   therefore imply uniqueness among all sheaf morphisms with these equations. -/
theorem etaleSetInverseImageConstantSheaf
    (U V : Scheme.{u}) (v : V ⟶ U) (E : Type u) :
    ∃ γ :
        (Scheme.etaleSetPullback v).obj
            ((constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
              (ULift.{u + 1, u} E)) ⟶
          (constantSheaf V.smallEtaleTopology (Type (u + 1))).obj
            (ULift.{u + 1, u} E),
      (∀ e : E,
        γ.hom.app (Opposite.op ((MorphismProperty.Over.pullback
          (P := @AlgebraicGeometry.Etale) (Q := ⊤) v).obj
          (Scheme.Etale.mk (𝟙 U))))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback
            (P := @AlgebraicGeometry.Etale) (Q := ⊤) v) (Type (u + 1))
            (U.smallGrothendieckTopology @Etale)
            (V.smallGrothendieckTopology @Etale)).unit.app
              ((constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
                (ULift.{u + 1, u} E))).hom.app
            (Opposite.op (Scheme.Etale.mk (𝟙 U)))
            (((toSheafify U.smallEtaleTopology
              ((Functor.const U.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))).app
                (Opposite.op (Scheme.Etale.mk (𝟙 U))) ⟨e⟩))) =
          (toSheafify V.smallEtaleTopology
            ((Functor.const V.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))).app
            (Opposite.op ((MorphismProperty.Over.pullback
          (P := @AlgebraicGeometry.Etale) (Q := ⊤) v).obj
              (Scheme.Etale.mk (𝟙 U)))) ⟨e⟩) ∧
      IsIso γ ∧
      ∀ γ' :
          (Scheme.etaleSetPullback v).obj
              ((constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
                (ULift.{u + 1, u} E)) ⟶
            (constantSheaf V.smallEtaleTopology (Type (u + 1))).obj
              (ULift.{u + 1, u} E),
        (∀ e : E,
          γ'.hom.app (Opposite.op ((MorphismProperty.Over.pullback
          (P := @AlgebraicGeometry.Etale) (Q := ⊤) v).obj
            (Scheme.Etale.mk (𝟙 U))))
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback
            (P := @AlgebraicGeometry.Etale) (Q := ⊤) v) (Type (u + 1))
              (U.smallGrothendieckTopology @Etale)
              (V.smallGrothendieckTopology @Etale)).unit.app
                ((constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
                  (ULift.{u + 1, u} E))).hom.app
              (Opposite.op (Scheme.Etale.mk (𝟙 U)))
              (((toSheafify U.smallEtaleTopology
                ((Functor.const U.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))).app
                  (Opposite.op (Scheme.Etale.mk (𝟙 U))) ⟨e⟩))) =
            (toSheafify V.smallEtaleTopology
              ((Functor.const V.Etaleᵒᵖ).obj (ULift.{u + 1, u} E))).app
              (Opposite.op ((MorphismProperty.Over.pullback
          (P := @AlgebraicGeometry.Etale) (Q := ⊤) v).obj
                (Scheme.Etale.mk (𝟙 U)))) ⟨e⟩) →
          γ' = γ := by
  obtain ⟨γ, hγ, hIso⟩ := etaleSetInverseImageConstantSheaf_exists U V v E
  refine ⟨γ, ?_, hIso, ?_⟩
  · simpa [etaleSetInverseImageConstantSheafCondition] using hγ
  · intro γ' hγ'
    apply etaleSetInverseImageConstantSheaf_unique U V v E γ
    · simpa [etaleSetInverseImageConstantSheafCondition] using hγ
    · simpa [etaleSetInverseImageConstantSheafCondition] using hγ'

end AlgebraicGeometry
