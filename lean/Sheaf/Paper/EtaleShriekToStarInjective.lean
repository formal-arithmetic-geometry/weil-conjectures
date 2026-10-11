module

public import Sheaf.AlgebraicGeometry.EtaleGraphSectionExtensionMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale

/-! # Injectivity of extension by zero into direct image

Source: Stacks Project, `etale-cohomology.tex`, Lemma 0F4L (lemma-shriek-into-star-separated-etale),
second paragraph of the proof (blueprint: lem-weil-pbc-etale-shriek-to-star-injective).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The canonical map from extension by zero to direct image is sectionwise injective,
locally injective, and a monomorphism (blueprint: lem-weil-pbc-etale-shriek-to-star-injective).

Proof: pairwise coincidence loci of maps into the finite étale cover are clopen, so a finite
clopen refinement makes the graph supports equal or disjoint. On each piece disjoint supports
force every coefficient to vanish. Thus the presheaf comparison is locally injective; the
sheafification lifting lemma makes the canonical sheaf map injective on every section and a
monomorphism. The argument uses `lem-weil-pbc-etale-graph-section-extension-map` and the
site-module sheafification lifting lemma.
-/
theorem etale_lower_shriek_to_lower_star_injective
    {X U : Scheme.{u}} (π : U ⟶ X) [IsFinite π] [Etale π]
    (Λ : Type (u + 1)) [CommRing Λ]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (∀ W : X.Etale,
      Function.Injective (ConcreteCategory.hom
        ((Etale.etaleLowerShriekToLowerStar
          (ModuleCat.{u + 1} Λ) π M).hom.app (op W)))) ∧
      Sheaf.IsLocallyInjective
        (Etale.etaleLowerShriekToLowerStar
          (ModuleCat.{u + 1} Λ) π M) ∧
      Mono (Etale.etaleLowerShriekToLowerStar
        (ModuleCat.{u + 1} Λ) π M) := by
  sorry

end AlgebraicGeometry
