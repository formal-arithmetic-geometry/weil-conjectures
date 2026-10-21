/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import Sheaf.AlgebraicGeometry.QcoherentPullbackSectionsNaturality

/-! # Structural pullback after sheafifying tensor sections

Source: Stacks Project, Tags 03DR, 03P2 and 01FD.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
attribute [local irreducible] qcoherentPullbackSection etaleTensorSectionsRestriction
attribute [local irreducible] tensorPullback tensorPullbackObj coherentEtaleMap
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Cache sheafification on each open slice for quasi-coherent coefficient interfaces.
Source: Mathlib sheafification on small sites.
(blueprint: lem-weil-pbc-qcoherent-tensor-pullback-sheaf-map)

Proof: Apply the existing abelian sheafification instance to each open slice. -/
@[instance 3000]
theorem qcoherentPullback_hasWeakSheafifyOver (X : Scheme.{u}) :
    ∀ U : TopologicalSpace.Opens X,
      HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} := by
  intro U
  infer_instance

/-- Cache the local-bijectivity characterization on each open slice.
Source: Mathlib sheafification on small sites.
(blueprint: lem-weil-pbc-qcoherent-tensor-pullback-sheaf-map)

Proof: Apply the existing abelian sheafification characterization on each slice. -/
@[instance 3000]
theorem qcoherentPullback_wEqualsOver (X : Scheme.{u}) :
    ∀ U : TopologicalSpace.Opens X,
      ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  intro U
  infer_instance

/-- Structural pullback on the lifted tensor-section presheaves of arbitrary modules. -/
def tensorPullbackSectionPresheafMap {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) (G : SheafOfModules.{u} Y.ringCatSheaf)
    (ψ : (tensorPullback g).obj F ⟶ G) :
    (etaleTensorSectionsPresheaf F ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) ⟶
      g.Etale.op ⋙ (etaleTensorSectionsPresheaf G ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) where
  app U := AddCommGrpCat.uliftFunctor.map
    (qcoherentPullbackSection g F G ψ U.unop (g.Etale.obj U.unop)
      (pullback.fst U.unop.hom g) pullback.condition)
  naturality {U V} a := by
    have hs := qcoherentPullbackSection_square_naturality g F G ψ
      (U₁ := U.unop) (U₂ := V.unop)
      (V₁ := g.Etale.obj U.unop) (V₂ := g.Etale.obj V.unop)
      (pullback.fst U.unop.hom g) (pullback.fst V.unop.hom g)
      pullback.condition pullback.condition a.unop (g.Etale.map a.unop) (by
        dsimp only [Scheme.Hom.Etale, MorphismProperty.Over.pullback]
        exact pullback.lift_fst _ _ _)
    change AddCommGrpCat.uliftFunctor.map (etaleTensorSectionsRestriction F a.unop) ≫
        AddCommGrpCat.uliftFunctor.map _ =
      AddCommGrpCat.uliftFunctor.map _ ≫
        AddCommGrpCat.uliftFunctor.map (etaleTensorSectionsRestriction G (g.Etale.map a.unop))
    exact (AddCommGrpCat.uliftFunctor.map_comp _ _).symm.trans
      ((congrArg AddCommGrpCat.uliftFunctor.map hs).trans
        (AddCommGrpCat.uliftFunctor.map_comp _ _))

attribute [local irreducible] tensorPullbackSectionPresheafMap

/-- Structural pullback of the lifted associated quasi-coherent sheaves. -/
def qcoherentPullbackSheafMap {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) (G : SheafOfModules.{u} Y.ringCatSheaf)
    [hF : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [hG : SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) G]
    (ψ : (tensorPullback g).obj F ⟶ G) :
    liftedCoherentEtaleSheaf F ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (liftedCoherentEtaleSheaf G) :=
  ⟨tensorPullbackSectionPresheafMap g F G ψ⟩

attribute [local irreducible] qcoherentPullbackSheafMap

/-- The terminal component followed by terminal restriction is lifted section pullback.
Source: Stacks Project, Tags 03AX and 01FD.
(blueprint: lem-weil-pbc-qcoherent-tensor-pullback-sheaf-map)

Proof: The pushforward section comparison is restriction along the terminal
isomorphism. The coefficient component is the lifted structural section map.
Functoriality of coefficient lift identifies their composite. -/
theorem qcoherentPullbackSheafMap_terminal {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) (G : SheafOfModules.{u} Y.ringCatSheaf)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (ψ : (tensorPullback g).obj F ⟶ G) :
    (qcoherentPullbackSheafMap g F G ψ).hom.app (op (⊤_ X.Etale)) ≫
        (Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} g).hom.app
          (liftedCoherentEtaleSheaf G) =
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map
        (qcoherentPullbackSection g F G ψ (⊤_ X.Etale) (g.Etale.obj (⊤_ X.Etale))
          (pullback.fst (⊤_ X.Etale).hom g) pullback.condition ≫
            etaleTensorSectionsRestriction G (PreservesTerminal.iso g.Etale).inv) := by
  unfold qcoherentPullbackSheafMap tensorPullbackSectionPresheafMap
    Etale.lowerStarCompSheafSectionsTerminalIso
  dsimp only [NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.op, Iso.symm,
    CoherentEtale.Coeff, etaleTensorSectionsSheaf, sheafCompose,
    Functor.comp_map, etaleTensorSectionsPresheaf]
  exact (AddCommGrpCat.uliftFunctor.map_comp _ _).symm

/-- The structural coefficient maps respect a commuting square of module maps.
Source: Stacks Project, Tags 03DR and 01FD.
(blueprint: lem-weil-pbc-qcoherent-tensor-pullback-sheaf-map)

Proof: Equality of morphisms of sheaves reduces to equality on each section.
The defining coefficient maps are the lifted structural section maps. Their
commutativity is coefficient naturality of the structural section formula,
and applying ULift preserves that equality. -/
theorem qcoherentPullbackSheafMap_naturality {X Y : Scheme.{u}}
    (g : Y ⟶ X) {F F' : SheafOfModules.{u} X.ringCatSheaf}
    {G G' : SheafOfModules.{u} Y.ringCatSheaf}
    [hF : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    [hF' : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F']
    [hG : SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) G]
    [hG' : SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) G']
    (ψ : (tensorPullback g).obj F ⟶ G)
    (ψ' : (tensorPullback g).obj F' ⟶ G') (a : F ⟶ F') (b : G ⟶ G')
    (hab : (tensorPullback g).map a ≫ ψ' = ψ ≫ b) :
    coherentEtaleMap F F' a ≫ qcoherentPullbackSheafMap g F' G' ψ' =
      qcoherentPullbackSheafMap g F G ψ ≫
        (Etale.lowerStar AddCommGrpCat.{u + 1} g).map (coherentEtaleMap G G' b) := by
  unfold qcoherentPullbackSheafMap
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have ha : (coherentEtaleMap F F' a).hom.app U =
      AddCommGrpCat.uliftFunctor.map (((tensorPullback U.unop.hom).map a).app ⊤) := by
    unfold coherentEtaleMap
    exact congrArg AddCommGrpCat.uliftFunctor.map
      ((Classical.choose_spec (etale_zariski_qcoh_comparison X)).1 F F' a U.unop)
  have hb : (coherentEtaleMap G G' b).hom.app (g.Etale.op.obj U) =
      AddCommGrpCat.uliftFunctor.map
        (((tensorPullback (g.Etale.obj U.unop).hom).map b).app ⊤) := by
    unfold coherentEtaleMap
    exact congrArg AddCommGrpCat.uliftFunctor.map
      ((Classical.choose_spec (etale_zariski_qcoh_comparison Y)).1 G G' b
        (g.Etale.obj U.unop))
  change (coherentEtaleMap F F' a).hom.app U ≫ _ =
    _ ≫ (coherentEtaleMap G G' b).hom.app (g.Etale.op.obj U)
  rw [ha, hb]
  unfold tensorPullbackSectionPresheafMap
  exact (AddCommGrpCat.uliftFunctor.map_comp _ _).symm.trans
    ((congrArg AddCommGrpCat.uliftFunctor.map
      (qcoherentPullbackSection_coefficient_naturality g
        (F := F) (F' := F') (G := G) (G' := G') ψ ψ' a b hab U.unop
        (g.Etale.obj U.unop) (pullback.fst U.unop.hom g) pullback.condition)).trans
      (AddCommGrpCat.uliftFunctor.map_comp _ _))

end
end AlgebraicGeometry.Scheme.Modules
