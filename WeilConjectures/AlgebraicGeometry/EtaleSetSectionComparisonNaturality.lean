/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison

/-! # Restriction naturality of the section comparison

## References

* Stacks Project, Tags 03CB and 03CC
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The section comparison maps are natural in the étale object (Stacks, Tags 03CB and 03CC). -/
theorem etaleSetSectionComparison_naturality
    {R S T : Scheme.{u}} (h : T ⟶ S) (f : S ⟶ R) (k : T ⟶ R) (hk : h ≫ f = k)
    (G : Sheaf R.smallEtaleTopology (Type (u + 1)))
    {V W : R.Etale} (v : V ⟶ W) :
    etaleSetSectionComparison h f k hk G W ≫
        ((Scheme.etaleSetPullback k).obj G).obj.map
          ((MorphismProperty.Over.pullback @Etale ⊤ k).map v).op =
      ((Scheme.etaleSetPullback f).obj G).obj.map
          ((MorphismProperty.Over.pullback @Etale ⊤ f).map v).op ≫
        etaleSetSectionComparison h f k hk G V := by
  let B (S T : Scheme.{u}) (f : S ⟶ T) :=
    MorphismProperty.Over.pullback @Etale ⊤ f
  let F := (Scheme.etaleSetPullback f).obj G
  let K := (Scheme.etaleSetPullback k).obj G
  let η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (B T S h) (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
    (T.smallGrothendieckTopology @Etale)).unit.app F
  let β := (Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S T f h).hom.app G
  let γ := eqToHom (congrArg (fun a : T ⟶ R ↦ (Scheme.etaleSetPullback a).obj G) hk)
  let δ := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
    h f k hk.symm).hom
  let α := Functor.whiskerLeft (B S R f).op η.hom ≫
    Functor.whiskerLeft ((B S R f) ⋙ (B T S h)).op β.hom ≫
    Functor.whiskerLeft ((B S R f) ⋙ (B T S h)).op γ.hom ≫
    Functor.whiskerRight (NatTrans.op δ) K.obj
  exact (α.naturality v.op).symm

end AlgebraicGeometry
