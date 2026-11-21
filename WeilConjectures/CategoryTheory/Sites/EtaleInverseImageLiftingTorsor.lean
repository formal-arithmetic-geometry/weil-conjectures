/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.CategoryTheory.Sites.EtaleInverseImageLiftsFibre

/-! # Inverse image of a lifting torsor

## References

* Stacks Project, Tag 03AJ, lifting-torsor construction and its inverse-image
  compatibility.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory.Sheaf.Torsor

/-- Inverse image preserves the fibre torsor of a short exact sequence over a section.
Source: Stacks Project, Tag 03AJ, construction of the torsor of lifts. -/
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
  dsimp only
  let b := MorphismProperty.Over.pullback @Etale ⊤ f
  let L := Scheme.etaleSetPullback f
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
    (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale)
  let aa := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  obtain ⟨e⟩ := he
  obtain ⟨c, hc⟩ := etale_inverse_image_lifts_fibre X Y f S hS s
  refine ⟨L.mapIso e.iso ≪≫ c, ?_⟩
  intro W g t
  have hn (x : T.sheaf.obj.obj (op W)) :
      (L.map e.iso.hom).hom.app (op (b.obj W))
          ((a.unit.app T.sheaf).hom.app (op W) x) =
        (a.unit.app (lifts terminalIsTerminal hS s).sheaf).hom.app (op W)
          (e.iso.hom.hom.app (op W) x) := by
    exact (congrArg (fun k ↦ k.hom.app (op W) x) (a.unit.naturality e.iso.hom)).symm
  change c.hom.hom.app (op (b.obj W))
      ((L.map e.iso.hom).hom.app (op (b.obj W))
        ((a.unit.app T.sheaf).hom.app (op W) (T.vadd (op W) g t))) = _
  rw [hn, e.map_vadd]
  apply Subtype.ext
  rw [hc]
  change ((aa.unit.app S.X₂).hom.app (op W))
      ((show S.X₂.obj.obj (op W) from (e.iso.hom.hom.app (op W) t).val) +
        S.f.hom.app (op W) g) =
    _ + _
  rw [map_add]
  rw [show ((aa.unit.app S.X₂).hom.app (op W)) (S.f.hom.app (op W) g) =
      ((S.map (Etale.upperStar AddCommGrpCat.{u + 1} f)).f.hom.app (op (b.obj W)))
        (((aa.unit.app S.X₁).hom.app (op W)) g) from
    congrArg (fun k ↦ k.hom.app (op W) g) (aa.unit.naturality S.f)]
  congr 1
  change ((aa.unit.app S.X₂).hom.app (op W)) (e.iso.hom.hom.app (op W) t).val =
    (c.hom.hom.app (op (b.obj W))
      ((L.map e.iso.hom).hom.app (op (b.obj W))
        ((a.unit.app T.sheaf).hom.app (op W) t))).val
  rw [hn]
  exact (hc W (e.iso.hom.hom.app (op W) t)).symm

end CategoryTheory.Sheaf.Torsor
