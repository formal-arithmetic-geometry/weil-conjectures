/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
public import WeilConjectures.CategoryTheory.Sites.GrpTorsor
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar

/-!
# Torsors under classical groups

Let `X` be a scheme and `G` a sheaf of groups on the small pro-étale site of `X` whose
underlying sheaf of sets is classical, i.e. of the form `ν^* G₀` for an étale sheaf `G₀`
(Stacks 099X). We show that every pro-étale `G`-torsor is classical, and that it is
trivialized by an étale covering.

## Main results

- `AlgebraicGeometry.Scheme.proEtaleSetRestrictionComparisonIso`: for `f : Y ⟶ X` weakly
  étale, restricting the inverse image `ν_X^* G` of an étale sheaf of sets to `Y_proét` gives
  `ν_Y^* f^* G`.
- `AlgebraicGeometry.Scheme.isProEtaleClassical_proEtaleSetRestriction`: the restriction of a
  classical sheaf of sets to an object of the pro-étale site is classical.
- `AlgebraicGeometry.Scheme.isProEtaleClassical_grpTorsor`: a torsor under a classical sheaf
  of groups is classical.
- `AlgebraicGeometry.Scheme.exists_etale_trivialization_grpTorsor`: a torsor under a classical
  sheaf of groups is trivialized by an étale covering.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

section Restriction

variable {Y X : Scheme.{u}} (f : Y ⟶ X)

local instance : (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous X.smallEtaleTopology
    Y.smallEtaleTopology :=
  Etale.isContinuous_overPullback f

/-- The direct images `ν_X_* f_*` and `f_* ν_Y_*` of set-valued sheaves on `Y_proét` agree:
both take sections over the base changes `E ×_X Y` of étale `X`-schemes `E`. -/
noncomputable def proEtaleSetLowerStarComparisonIso :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).sheafPushforwardContinuous
        (Type (u + 1)) (ProEt.topology X) (ProEt.topology Y) ⋙
      (toProEt X).sheafPushforwardContinuous (Type (u + 1)) X.smallEtaleTopology
        (ProEt.topology X) ≅
    (toProEt Y).sheafPushforwardContinuous (Type (u + 1)) Y.smallEtaleTopology
        (ProEt.topology Y) ⋙
      (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        (Type (u + 1)) X.smallEtaleTopology Y.smallEtaleTopology :=
  have := ProEt.isContinuous_overPullback f
  have := isContinuous_toProEt Y
  have := ProEtale.isContinuous_overPullback_comp_toProEt f
  Functor.sheafPushforwardContinuousComp (toProEt X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (Type (u + 1))
      X.smallEtaleTopology (ProEt.topology X) (ProEt.topology Y) ≪≫
    Functor.sheafPushforwardContinuousIso (ProEtale.toProEtCompOverPullbackIso f)
      (Type (u + 1)) X.smallEtaleTopology (ProEt.topology Y) ≪≫
    (Functor.sheafPushforwardContinuousComp (MorphismProperty.Over.pullback @Etale ⊤ f)
      (toProEt Y) (Type (u + 1)) X.smallEtaleTopology Y.smallEtaleTopology
      (ProEt.topology Y)).symm

/-- For a weakly étale morphism `f : Y ⟶ X`, restricting the inverse image `ν_X^* G` of an
étale sheaf of sets `G` to the localization `Y_proét` of `X_proét` gives the inverse image
`ν_Y^* f^* G`. Both functors are left adjoint to `ν_X_* f_* ≅ f_* ν_Y_*`. -/
noncomputable def proEtaleSetRestrictionComparisonIso (hf : WeaklyEtale f) :
    ProEtale.comparisonCoefficientPullback (Type (u + 1)) X ⋙
        (MorphismProperty.Over.map ⊤ hf).sheafPushforwardContinuous (Type (u + 1))
          (ProEt.topology Y) (ProEt.topology X) ≅
      etaleSetPullback f ⋙ ProEtale.comparisonCoefficientPullback (Type (u + 1)) Y :=
  let adjX := (ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) X).comp
    ((MorphismProperty.Over.mapPullbackAdj (@WeaklyEtale) ⊤ f hf
      _root_.trivial).sheafPushforwardContinuous (ProEt.topology Y) (ProEt.topology X))
  let adjY := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
    X.smallEtaleTopology Y.smallEtaleTopology).comp
      (ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) Y)
  adjX.leftAdjointUniq (adjY.ofNatIsoRight (proEtaleSetLowerStarComparisonIso f).symm)

end Restriction

/-- The restriction of a classical sheaf of sets on `X_proét` to an object `U` of the small
pro-étale site is classical on `U_proét`. -/
theorem isProEtaleClassical_proEtaleSetRestriction {X : Scheme.{u}} (U : X.ProEt)
    {F : Sheaf (ProEt.topology X) (Type (u + 1))} (hF : IsProEtaleClassical X F) :
    IsProEtaleClassical U.left ((proEtaleSetRestriction X U).obj F) := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  exact ⟨(etaleSetPullback U.hom).obj G,
    ⟨(proEtaleSetRestriction X U).mapIso e ≪≫
      (proEtaleSetRestrictionComparisonIso U.hom U.prop).app G⟩⟩

/-- The structure maps `W ⟶ U` of the objects of the small pro-étale site of `U`, viewed as
objects of the small pro-étale site of `X`. -/
noncomputable def ProEt.overMapToConst {X : Scheme.{u}} (U : X.ProEt) :
    MorphismProperty.Over.map (P := @WeaklyEtale) ⊤ U.prop ⟶ (Functor.const _).obj U where
  app W := MorphismProperty.Over.homMk W.hom (by simp)
  naturality _ _ f := by ext; simp

section Torsor

variable {X : Scheme.{u}} {G : Sheaf (ProEt.topology X) GrpCat.{u + 1}}
  (hG : IsProEtaleClassical X
    ((sheafCompose (ProEt.topology X) (CategoryTheory.forget GrpCat.{u + 1})).obj G))
  (T : Sheaf.GrpTorsor G)

/-- A section of a `G`-torsor over `U` identifies the restrictions of `G` and of the torsor
to `U_proét`. -/
noncomputable def proEtaleSetRestrictionGrpTorsorIso (U : X.ProEt)
    (t : T.sheaf.obj.obj (op U)) :
    (proEtaleSetRestriction X U).obj ((sheafCompose (ProEt.topology X)
      (CategoryTheory.forget GrpCat.{u + 1})).obj G) ≅
      (proEtaleSetRestriction X U).obj T.sheaf :=
  ObjectProperty.isoMk _ (T.isoOfSection _ (ProEt.overMapToConst U) t)

/-- The objects of the small pro-étale site over which a `G`-torsor has a section cover `X`. -/
theorem coversTop_nonempty_grpTorsor :
    (ProEt.topology X).CoversTop
      (fun V : {V : X.ProEt // Nonempty (T.sheaf.obj.obj (op V))} ↦ V.1) := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ (ProEt.mk (𝟙 X))
    (MorphismProperty.Over.mkIdTerminal _ _)]
  exact (ProEt.topology X).superset_covering (fun V _ hV ↦ ⟨⟨V, hV⟩, ⟨𝟙 _⟩⟩)
    (T.nonemptySieve_mem _)

include hG in
/-- A torsor under a sheaf of groups with classical underlying sheaf of sets is locally
classical: over each object where it has a section it is isomorphic to `G`. -/
theorem isProEtaleLocallyClassical_grpTorsor : IsProEtaleLocallyClassical X T.sheaf := by
  refine ⟨_, _, coversTop_nonempty_grpTorsor T, fun V ↦ ?_⟩
  obtain ⟨t⟩ := V.2
  obtain ⟨H, ⟨e⟩⟩ := isProEtaleClassical_proEtaleSetRestriction V.1 hG
  exact ⟨H, ⟨(proEtaleSetRestrictionGrpTorsorIso T V.1 t).symm ≪≫ e⟩⟩

include hG in
/-- **Torsors under classical groups are classical** (Stacks 099X). Let `G` be a sheaf of
groups on `X_proét` whose underlying sheaf of sets is classical, i.e. of the form `ν^* G₀`.
Then every `G`-torsor is classical.
(blueprint: `lemma-torsors-under-classical-groups--1`) -/
theorem isProEtaleClassical_grpTorsor : IsProEtaleClassical X T.sheaf :=
  (proEtale_locallyClassical_etaleCover X T.sheaf).1 (isProEtaleLocallyClassical_grpTorsor hG T)

include hG in
/-- **Torsors under classical groups are étale locally trivial** (Stacks 099X). Let `G` be a
sheaf of groups on `X_proét` whose underlying sheaf of sets is classical. Then every
`G`-torsor `T` is trivialized by an étale covering `Yᵢ → X`: there is a section `t` of `T`
over each `Yᵢ`, and `g ↦ g • t` identifies `G` with `T` over every object mapping to `Yᵢ`.
(blueprint: `lemma-torsors-under-classical-groups--2`) -/
theorem exists_etale_trivialization_grpTorsor :
    ∃ (I : Type (u + 1)) (Y : I → X.Etale), X.smallEtaleTopology.CoversTop Y ∧
      ∀ i, ∃ t : T.sheaf.obj.obj (op ((toProEt X).obj (Y i))),
        ∀ (V : X.ProEt) (f : V ⟶ (toProEt X).obj (Y i)),
          Function.Bijective (T.smul (op V) · (T.sheaf.obj.map f.op t)) := by
  obtain ⟨I, Y, hY, hs⟩ := (proEtale_locallyClassical_etaleCover X T.sheaf).2.2
    (isProEtaleLocallyClassical_grpTorsor hG T) ⟨_, _, coversTop_nonempty_grpTorsor T, (·.2)⟩
  exact ⟨I, Y, hY, fun i ↦ ⟨(hs i).some, fun V f ↦ T.bijective_smul _ _⟩⟩

end Torsor

end AlgebraicGeometry.Scheme
