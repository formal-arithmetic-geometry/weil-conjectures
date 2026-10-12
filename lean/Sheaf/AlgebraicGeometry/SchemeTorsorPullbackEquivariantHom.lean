/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
import Sheaf.AlgebraicGeometry.Sites.InverseImageRepresentable
import Sheaf.Paper.SiteSheafificationSectionsLocal
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.ConstructibleSheaf.Defs


/-!
# Equivariant morphisms for scheme torsor inverse image

Source: Stacks Project Tags 03Q1 (4), 03AG and 0A5G.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale

/-- An equivariant map from the inverse-image sheaf to the represented torsor.
Source: Stacks Project Tags 03Q1 (4), 03AG and 0A5G, final paragraph.
(blueprint: lem-weil-pbc-scheme-torsor-pullback-equivariant-hom)

Proof: The adjunction and Yoneda identify inverse image of the sheaf represented by
`t` with the sheaf represented by its base change. Compose its canonical comparison
with Yoneda of `e`, then with the given torsor identification `hrepr`. This supplies a
sheaf morphism without any invertibility assertion. The representable comparison
carries the unit of a section to its base change. For a constant coefficient `m`,
`hact` and the constant-sheaf comparison's unit identity give the displayed equation.
Every coefficient section is locally the unit of a constant presheaf section: use
sheafification's local representation property. On that cover the preceding equation
applies. Pull the cover back along `i`, use naturality of the two units and of the
morphism and actions, and use separatedness of `R.sheaf` to glue the equalities.
The inverse of the coefficient comparison in `ofIso` cancels its forward map, leaving
exactly the coefficient adjunction unit in the formula. -/
theorem scheme_torsor_pullback_equivariant_hom
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
    ∃ f : (Scheme.etaleSetPullback i).obj t.toSheafTorsor.sheaf ⟶ R.sheaf,
      let G := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M)
      (∀ (W : Y.Etale) (g : G.obj.obj (op W)) (x : t.toSheafTorsor.sheaf.obj.obj (op W)),
      f.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
          (Y.smallGrothendieckTopology @Etale)
          (Y₀.smallGrothendieckTopology @Etale)).unit.app t.toSheafTorsor.sheaf).hom.app (op W)
            (t.toSheafTorsor.vadd (op W) g x)) =
      R.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app G).hom.app
          (op W) g)
        (f.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (u + 1))
            (Y.smallGrothendieckTopology @Etale)
            (Y₀.smallGrothendieckTopology @Etale)).unit.app t.toSheafTorsor.sheaf).hom.app
              (op W) x))) := by
  sorry

end AlgebraicGeometry.Etale
