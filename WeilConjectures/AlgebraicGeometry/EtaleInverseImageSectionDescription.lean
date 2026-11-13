/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageLocalSheafification
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageKanRepresentative

/-!
# Local representatives of sections of an étale inverse image

## References

* Stacks Project, Tag 09XN
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Every global section of the inverse image is locally the restriction of a section pulled
back by the adjunction unit. A morphism into the base change of `V` encodes the commuting
factorization through the étale scheme `V` over `S`. -/
theorem etaleInverseImageSectionDescription (S T : Scheme.{u}) (g : T ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (s : ((Scheme.etaleSetPullback g).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 T)))) :
    ∃ (I : Type u) (Z : I → T.Etale)
      (π : ∀ i : I, Z i ⟶ Scheme.Etale.mk (𝟙 T)),
      Sieve.ofArrows Z π ∈ T.smallEtaleTopology (Scheme.Etale.mk (𝟙 T)) ∧
      ∀ i : I, ∃ (V : S.Etale)
        (a : Z i ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj V)
        (t : F.obj.obj (op V)),
        ((Scheme.etaleSetPullback g).obj F).obj.map (π i).op s =
          ((Scheme.etaleSetPullback g).obj F).obj.map a.op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
              (S.smallGrothendieckTopology @Etale)
              (T.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op V) t) := by
  dsimp [Scheme.etaleSetPullback]
  obtain ⟨I, Z, π, hπ, hp⟩ := etaleInverseImageSectionDescription_core S T g F s
  refine ⟨I, Z, π, hπ, ?_⟩
  intro i
  obtain ⟨p, hp⟩ := hp i
  obtain ⟨V, a, t, ht⟩ :=
    etaleInverseImageSectionDescription_representation S T g F (Z i) p
  exact ⟨V, a, t, hp.trans ht⟩

end AlgebraicGeometry
