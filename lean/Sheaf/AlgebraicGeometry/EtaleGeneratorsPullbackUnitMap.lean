/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleIsoTorsor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackSectionsNatural
import Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackMapUnitFormula

/-!
# Pullback of generators on adjunction-unit sections

Source: Stacks Project, Tags 040E and 0097.
(blueprint: lem-sc-etale-generators-pullback-unit-map)
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Pulling back trivialisations defines a sheaf map, equivariant on sections in the
images of the two inverse-image adjunction units.

Source: Stacks Project, Tag 040E (generator torsors) and Tag 0097 (module pullback).
(blueprint: lem-sc-etale-generators-pullback-unit-map)

Proof: For W étale over X, pull a trivialisation of L back to W ×_X Y. Compare tensor
pullback with the usual module pullback by their adjunctions to module pushforward,
and use composition of pullbacks to identify its target with the restriction of
(tensorPullback f).obj L. Pullback takes the structure module to the structure module
and preserves isomorphisms, so this is a generator. The pseudofunctor composition
constraints and naturality of the comparison make these maps commute with every
restriction. They give a morphism from the generator sheaf to the direct image of
the target generator sheaf. Its adjoint is ρ. On a unit section its value is exactly
the pulled-back trivialisation, by the adjunction unit equation. For g a unit and s
a generator the tensor identity 1 ⊗ (g s) = f(g) (1 ⊗ s) gives the displayed equation;
the map upperStarGmSheafToGmSheaf is adjoint to the same pullback of units, so its
composite with the group unit is f(g). No assertion on arbitrary inverse-image
sections is needed here. For the zero ring or empty schemes the pullback functor
still preserves isomorphisms and the same equations apply. -/
theorem exists_etale_generators_pullback_unit_map
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    [SheafOfModules.IsInvertible.{u, u, u} ((tensorPullback f).obj L)] :
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
      (Y.smallGrothendieckTopology @Etale)).unit.app (etaleIsoTorsor L).sheaf
    let ηG := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
      X.gmSheaf
    ∃ ρ : (Scheme.etaleSetPullback f).obj (etaleIsoTorsor L).sheaf ⟶
        (etaleIsoTorsor ((tensorPullback f).obj L)).sheaf,
      ∀ (W : X.Etale) (g : X.gmSheaf.obj.obj (op W))
        (s : (etaleIsoTorsor L).sheaf.obj.obj (op W)),
        ρ.hom.app (op (b.obj W))
            (η.hom.app (op W) ((etaleIsoTorsor L).vadd (op W) g s)) =
          (etaleIsoTorsor ((tensorPullback f).obj L)).vadd (op (b.obj W))
            ((upperStarGmSheafToGmSheaf f).hom.app (op (b.obj W))
              (ηG.hom.app (op W) g))
            (ρ.hom.app (op (b.obj W)) (η.hom.app (op W) s)) := by
  let b := MorphismProperty.Over.pullback @Etale ⊤ f
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
    (Type (u + 1)) (X.smallGrothendieckTopology @Etale)
    (Y.smallGrothendieckTopology @Etale)
  let T := (etaleIsoTorsor L).sheaf
  let Q := (etaleIsoTorsor ((tensorPullback f).obj L)).sheaf
  let τ : T ⟶ (b.sheafPushforwardContinuous (Type (u + 1))
      (X.smallGrothendieckTopology @Etale)
      (Y.smallGrothendieckTopology @Etale)).obj Q :=
    ⟨{ app := fun W ↦ ↾(etaleGeneratorsPullbackSection f L W.unop)
       naturality := by
         intro V W i
         ext s
         exact (etaleGeneratorsPullbackSection_naturality f L i.unop s).symm }⟩
  let ρ := (adj.homEquiv T Q).symm τ
  have hunit : adj.unit.app T ≫ (b.sheafPushforwardContinuous (Type (u + 1))
      (X.smallGrothendieckTopology @Etale)
      (Y.smallGrothendieckTopology @Etale)).map ρ = τ := by
    exact (adj.homEquiv T Q).apply_symm_apply τ
  have heval (W : X.Etale) (s : T.obj.obj (op W)) :
      ρ.hom.app (op (b.obj W)) ((adj.unit.app T).hom.app (op W) s) =
        etaleGeneratorsPullbackSection f L W s := by
    exact congrArg (fun a ↦ a.hom.app (op W) s) hunit
  refine ⟨ρ, ?_⟩
  intro W g s
  erw [heval, heval]
  exact etale_generators_pullback_map_unit_formula f L W g s

end AlgebraicGeometry.Scheme.Modules
