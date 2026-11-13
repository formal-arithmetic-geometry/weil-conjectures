/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Inverse image of étale sheaves of sets along an étale morphism

Source: Stacks Project, Étale Cohomology, Tag 03S2, paragraph after Definition 03S3;
Sites, Tag 00XZ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- For an étale morphism `j`, the set-valued inverse image `j⁻¹` is naturally isomorphic to
`Etale.localizationRestriction`, compatibly with the unit; in particular `(j⁻¹G)(U) ≅ G(U)`
(Stacks, Tags 03S2 and 00XZ). -/
theorem etaleSetInverseImageRestriction {X U : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    ∃ ρ : Scheme.etaleSetPullback j ≅
      Etale.localizationRestriction (Type (u + 1)) j inferInstance,
      ∀ (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
        (W : X.Etale) (s : G.obj.obj (op W)),
        (ρ.hom.app G).hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ j).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ j) (Type (u + 1))
            (X.smallGrothendieckTopology @Etale)
            (U.smallGrothendieckTopology @Etale)).unit.app G).hom.app (op W) s) =
          G.obj.map
            ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j
              inferInstance trivial).counit.app W).op s := by
  let adj₁ := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ j) (Type (u + 1))
    (X.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
  let siteAdj := MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance trivial
  let adj₂ := siteAdj.sheafPushforwardContinuous (E := Type (u + 1))
        (U.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)
  refine ⟨adj₁.leftAdjointUniq adj₂, ?_⟩
  intro G W s
  have h := Adjunction.unit_leftAdjointUniq_hom_app adj₁ adj₂ G
  exact congrArg (fun f ↦ f.hom.app (op W) s) h

end AlgebraicGeometry
