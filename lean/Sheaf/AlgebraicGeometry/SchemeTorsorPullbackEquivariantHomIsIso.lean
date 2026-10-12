/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor


/-!
# Equivariant morphisms for scheme torsor inverse image

Source: Stacks Project Tags 03Q1 (4), 03AG and 0A5G.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Unit-equivariant maps from an inverse-image torsor sheaf are invertible.
Source: Stacks Project Section 03AG (morphisms of torsors), and Tag 03Q1 (4).
(blueprint: lem-weil-pbc-scheme-torsor-pullback-equivariant-hom-is-iso)

Proof: Inverse image preserves the torsor action and local nonemptiness, since it
preserves finite limits and covering epimorphisms. The displayed equation on units
implies equivariance on arbitrary local sections: sections of both inverse images
are locally represented by source-site sections, by the sheafification construction
of inverse image; refine the two representing covers to a common one and use
naturality, followed by separatedness. An equivariant map between torsors is locally
bijective. Locally choose a section of the source torsor. Translation identifies
both torsors with the coefficient group, and the map becomes the identity on that
group. Hence it is locally injective and locally surjective, and is an isomorphism
of sheaves. This argument also covers empty site objects and the trivial group:
local nonemptiness is the torsor axiom, not a global section assumption. -/
theorem scheme_torsor_pullback_equivariant_hom_isIso
    {Y Y₀ : Scheme.{u}} (i : Y₀ ⟶ Y)
    (M : Type (u + 1)) [AddCommGroup M] [Finite M]
    (t : Scheme.EtaleTorsor M Y)
    (R : Sheaf.Torsor ((upperStar AddCommGrpCat.{u + 1} i).obj
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M))))
    (f : (Scheme.etaleSetPullback i).obj t.toSheafTorsor.sheaf ⟶ R.sheaf)
    (hf :
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
              (op W) x)))) : IsIso f := by
  sorry

end AlgebraicGeometry.Etale
