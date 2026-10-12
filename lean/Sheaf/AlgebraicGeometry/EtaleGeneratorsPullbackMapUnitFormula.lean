module

public import Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Unit formula for pullback generator map

Source: Stacks Project, Tags 040E and 0097.
(blueprint: lem-sc-etale-generators-pullback-map-unit-formula)
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000 in
-- Unfolding the generator torsor and the pullback comparison is expensive.
/-- The canonical pullback generator map obeys the unit equivariance formula.
Source: Stacks Project, Tags 040E and 0097.
(blueprint: lem-sc-etale-generators-pullback-map-unit-formula)
Proof: reduce equality of lifted generator subtypes to equality of module maps.
Pullback carries multiplication by g to multiplication by its pulled-back
function, by `pullback_map_smulHom`. The Gm adjunction unit equation identifies
the group element on the right with the pullback of g along the first projection.
Move that scalar past the three source comparison maps using
`smulHom_naturality_assoc`. The remaining composites agree by reflexivity.
-/
theorem etale_generators_pullback_map_unit_formula {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    [SheafOfModules.IsInvertible.{u, u, u} ((tensorPullback f).obj L)] :
    ∀ (W : X.Etale) (g : X.gmSheaf.obj.obj (op W))
      (s : (etaleIsoTorsor L).sheaf.obj.obj (op W)),
      (etaleGeneratorsPullbackSection f L W ((etaleIsoTorsor L).vadd (op W) g s)) =
      (etaleIsoTorsor ((tensorPullback f).obj L)).vadd
        (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
        ((upperStarGmSheafToGmSheaf f).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
          (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
            X.gmSheaf).hom.app (op W) g))
        (etaleGeneratorsPullbackSection f L W s) := by
  intro W g s
  apply ULift.ext
  apply Subtype.ext
  simp only [etaleGeneratorsPullbackSection, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_hom]
  change _ = smulMor _ _ ≫ _
  change (pullbackObjUnitIso (Limits.pullback.snd W.hom f)).hom ≫
    (pullbackObjUnitIso (Limits.pullback.fst W.hom f)).inv ≫
    (pullback (Limits.pullback.fst W.hom f)).map (pullbackObjUnitIso W.hom).inv ≫
    (pullback (Limits.pullback.fst W.hom f)).map
      (smulMor _ ((Additive.toMul g.down : Γ(W.left, ⊤)ˣ) : Γ(W.left, ⊤)) ≫ s.down.1) ≫ _ = _
  erw [Functor.map_comp]
  unfold smulMor
  erw [pullback_map_smulHom]
  let adj := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  have hunit : adj.unit.app X.gmSheaf ≫
      (Etale.lowerStar AddCommGrpCat.{u + 1} f).map (upperStarGmSheafToGmSheaf f) =
      gmSheafToLowerStarGmSheaf f :=
    (adj.homEquiv X.gmSheaf Y.gmSheaf).apply_symm_apply _
  have hg := congrArg (fun a ↦ a.hom.app (op W) g) hunit
  change (upperStarGmSheafToGmSheaf f).hom.app _
      ((adj.unit.app X.gmSheaf).hom.app (op W) g) =
    (gmSheafToLowerStarGmSheaf f).hom.app (op W) g at hg
  erw [hg]
  simp only [Category.assoc]
  erw [← smulHom_naturality_assoc, ← smulHom_naturality_assoc,
    ← smulHom_naturality_assoc]
  rfl

end AlgebraicGeometry.Scheme.Modules
