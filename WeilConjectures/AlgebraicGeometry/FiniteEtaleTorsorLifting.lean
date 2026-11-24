/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.CategoryTheory.Sites.Torsor

import WeilConjectures.AlgebraicGeometry.FiniteEtaleSchemeTorsorLift
import WeilConjectures.AlgebraicGeometry.SchemeTorsorPullbackCompatible
import WeilConjectures.AlgebraicGeometry.EtaleTorsorUnitActionUnique

/-!
# Finite étale equivalences and transport of torsors

## References

* Stacks Project, Tags 0A5G and 03RV
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Every inverse-image-coefficient torsor lifts under a finite étale equivalence.
(Stacks, Tag 0A5G, using Tags 03RV and 03Q1.) -/
theorem finiteEtale_lifts_torsor_transport
    [(@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange]
    {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y)
    (hFE : (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ i).IsEquivalence)
    (M : Type (u + 1)) [AddCommGroup M] [Finite M]
    (τ : Sheaf.Torsor
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)) →
      Sheaf.Torsor ((upperStar AddCommGrpCat.{u + 1} i).obj
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M))))
    (hτ : ∀ T : Sheaf.Torsor
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of M)), ∃ eT : (Scheme.etaleSetPullback i).obj T.sheaf ≅ (τ T).sheaf,
      let G := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M)
      (∀ (W : Y.Etale) (g : G.obj.obj (op W)) (t : T.sheaf.obj.obj (op W)),
      eT.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
          (Y.smallGrothendieckTopology @Etale)
          (Y₀.smallGrothendieckTopology @Etale)).unit.app T.sheaf).hom.app (op W)
            (T.vadd (op W) g t)) =
      (τ T).vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app
          (op W) g)
        (eT.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
            (Y.smallGrothendieckTopology @Etale)
            (Y₀.smallGrothendieckTopology @Etale)).unit.app T.sheaf).hom.app (op W) t))))
    (R : Sheaf.Torsor ((upperStar AddCommGrpCat.{u + 1} i).obj
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)))) :
    ∃ T, τ T ≈ R := by
  let c := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).app
    (AddCommGrpCat.of M)
  obtain ⟨t₀, hrepr, t, e, he, hact⟩ :=
    finiteEtale_lifts_scheme_torsor i hFE M (Sheaf.Torsor.ofIso c R)
  obtain ⟨eR, hR⟩ := scheme_torsor_pullback_compatible i M t t₀ e he hact R hrepr
  obtain ⟨eT, hT⟩ := hτ t.toSheafTorsor
  refine ⟨t.toSheafTorsor, ⟨⟨eT.symm ≪≫ eR, ?_⟩⟩⟩
  exact etale_torsor_unit_action_unique i _ t.toSheafTorsor
    (τ t.toSheafTorsor) R eT eR hT hR

end AlgebraicGeometry.Etale
