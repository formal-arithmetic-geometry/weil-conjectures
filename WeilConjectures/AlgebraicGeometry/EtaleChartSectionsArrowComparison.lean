/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleChartSectionsObjectComparison

/-!
# Restricting inverse-image sections to an etale chart

## References

* Stacks Project, Tags 0EZX and 0A3H
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The sections map on a chart is the terminal-object unit map of the induced
morphism to its etale base, up to isomorphism of arrows. No flatness or connectedness
assumption is needed for this comparison.
(Stacks, Tags 0EZX and 0A3H) -/
theorem nonempty_etaleChartSections_arrowIso
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} (p : X ⟶ S)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ p).obj V) :
    Nonempty (Arrow.mk
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app G).hom.app (op V) ≫
        ((p)^*[ModuleCat.{u + 1} Λ].obj G).obj.map φ.op) ≅
      Arrow.mk
        (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (φ.left ≫ pullback.fst V.hom p)).unit.app
            ((V.hom)^*[ModuleCat.{u + 1} Λ].obj G)).hom.app
              (op (Scheme.Etale.mk (𝟙 V.left))))) := by
  obtain ⟨e₁, e₂, h⟩ :=
    (etaleChartSections_objectComparison Λ p G φ).some
  exact ⟨Arrow.isoMk e₁ e₂ h⟩

end AlgebraicGeometry.Etale
