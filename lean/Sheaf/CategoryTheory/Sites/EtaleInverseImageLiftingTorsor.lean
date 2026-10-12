/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact

/-! # Inverse image of a lifting torsor

Source: Stacks Project, Tag 03AJ, lifting-torsor construction and its inverse-image
compatibility (blueprint: lem-sc-etale-inverse-image-lifting-torsor).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory.Sheaf.Torsor

/-- Inverse image preserves the fibre torsor of a short exact sequence over a section.
Source: Stacks Project, Tag 03AJ, construction of the torsor of lifts;
inverse-image fibre compatibility in lem-sc-etale-torsor-inverse-image-extension.
(blueprint: lem-sc-etale-inverse-image-lifting-torsor)

Proof: Express the sheaf of lifts as the pullback of the underlying sheaf map to the
quotient along the global section. Set inverse image preserves finite limits and the
terminal sheaf, and its comparison with abelian inverse image preserves the underlying
maps and addition. Consequently this pullback is the sheaf of lifts of the pulled-back
section. Pull back the given equivariant isomorphism from T to the original lifting torsor
and compose it with this fibre comparison. Translation in a fibre is addition of the
image of the kernel; naturality of the comparisons and of the adjunction units gives the
asserted equivariance on pulled-back sections. This argument requires no injectivity
of the middle object after pullback. -/
theorem etale_inverse_image_lifting_torsor
    (X Y : Scheme.{u}) (f : Y ⟶ X)
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hS : S.ShortExact)
    (s : S.X₃.obj.obj (op (⊤_ X.Etale)))
    (T : Torsor S.X₁) (he : T ≈ lifts terminalIsTerminal hS s) :
    let U := Etale.upperStar AddCommGrpCat.{u + 1} f
    let hY := hS.map_of_exact U
    let s' := (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).hom.app (U.obj S.X₃)
      (Etale.globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f S.X₃
        ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
          terminalIsTerminal).inv.app S.X₃ s))
    let T' := lifts terminalIsTerminal hY s'
    ∃ eT : (Scheme.etaleSetPullback f).obj T.sheaf ≅ T'.sheaf,
        (∀ (W : X.Etale) (g : S.X₁.obj.obj (op W)) (t : T.sheaf.obj.obj (op W)),
          eT.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
              (X.smallGrothendieckTopology @Etale)
              (Y.smallGrothendieckTopology @Etale)).unit.app T.sheaf).hom.app (op W)
                (T.vadd (op W) g t)) =
          T'.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
            (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app S.X₁).hom.app
              (op W) g)
            (eT.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
              (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
                (X.smallGrothendieckTopology @Etale)
                (Y.smallGrothendieckTopology @Etale)).unit.app T.sheaf).hom.app (op W) t))) := by
  sorry

end CategoryTheory.Sheaf.Torsor
