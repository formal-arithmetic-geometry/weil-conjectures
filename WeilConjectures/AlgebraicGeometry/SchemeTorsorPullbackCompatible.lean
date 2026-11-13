/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

import WeilConjectures.AlgebraicGeometry.SchemeTorsorPullbackEquivariantHom
import WeilConjectures.AlgebraicGeometry.SchemeTorsorPullbackEquivariantHomIsIso

/-!
# Compatibility of an equivariant representative with inverse image

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 0A5G](https://stacks.math.columbia.edu/tag/0A5G)
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

/-- An equivariant base-change isomorphism gives the unit-compatible sheaf isomorphism. -/
theorem scheme_torsor_pullback_compatible
    {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y)
    (M : Type (u + 1)) [AddCommGroup M] [Finite M]
    (t : Scheme.EtaleTorsor M Y) (t₀ : Scheme.EtaleTorsor M Y₀)
    (e : pullback t.π i ≅ t₀.P)
    (he : e.hom ≫ t₀.π = pullback.snd t.π i)
    (hact : ∀ m : M,
      pullback.map t.π i t.π i (t.vadd m) (𝟙 Y₀) (𝟙 Y)
        (by rw [Category.comp_id, t.vadd_π])
        (by rw [Category.comp_id, Category.id_comp]) ≫ e.hom = e.hom ≫ t₀.vadd m)
    (R : Sheaf.Torsor ((upperStar AddCommGrpCat.{u + 1} i).obj
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M))))
    (hrepr : t₀.toSheafTorsor ≈ Sheaf.Torsor.ofIso
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).app
        (AddCommGrpCat.of M)) R) :
    ∃ E : (Scheme.etaleSetPullback i).obj t.toSheafTorsor.sheaf ≅ R.sheaf,
      let G := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M)
      (∀ (W : Y.Etale) (g : G.obj.obj (op W)) (x : t.toSheafTorsor.sheaf.obj.obj (op W)),
      E.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
          (Y.smallGrothendieckTopology @Etale)
          (Y₀.smallGrothendieckTopology @Etale)).unit.app t.toSheafTorsor.sheaf).hom.app (op W)
            (t.toSheafTorsor.vadd (op W) g x)) =
      R.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app
          (op W) g)
        (E.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
            (Y.smallGrothendieckTopology @Etale)
            (Y₀.smallGrothendieckTopology @Etale)).unit.app t.toSheafTorsor.sheaf).hom.app
              (op W) x))) := by
  obtain ⟨f, hf⟩ := scheme_torsor_pullback_equivariant_hom i M t t₀ e he hact R hrepr
  have := scheme_torsor_pullback_equivariant_hom_isIso i M t R f hf
  exact ⟨asIso f, hf⟩

end AlgebraicGeometry.Etale
