/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.AlgebraicGeometry.EtaleFieldGeometricAction
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
import WeilConjectures.CategoryTheory.DiscreteContinuousRepToCommGrpFull
import WeilConjectures.CategoryTheory.DiscreteContinuousRepToCommGrpEssSurj

@[expose] public section

universe u w
open CategoryTheory
namespace Rep

attribute [local instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂

/-- The equivalence between commutative group objects in discrete continuous `G`-sets and
discrete continuous integer representations of `G`, together with chosen carrier isomorphisms
which are compatible with every equivariant morphism.
Source: Stacks Project, Tag 04JQ. -/
theorem discreteContinuousRep_equiv_with_compatible_objectwise_iso
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CartesianMonoidalCategory (DiscreteContAction (Type w) G)]
    [BraidedCategory (DiscreteContAction (Type w) G)] :
    let D := DiscreteContinuousRep.{0, u, w} ℤ G
    let U : D ⥤ Rep.{w} ℤ G := ObjectProperty.ι _
    let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type w) (G := G)) ⋙
      ObjectProperty.ι (Action.IsContinuous (V := Type w) (G := G))
    ∃ E : CommGrp (DiscreteContAction (Type w) G) ≌ D,
      ∃ e : ∀ X, (E.functor ⋙ U ⋙ RepToAction ℤ G ⋙
        (CategoryTheory.forget (ModuleCat.{w} ℤ)).mapAction G).obj X ≅
          (CommGrp.forget (DiscreteContAction (Type w) G) ⋙ V).obj X,
      ∀ {X Y} (f : X ⟶ Y),
        ((E.functor ⋙ U ⋙ RepToAction ℤ G ⋙
          (CategoryTheory.forget (ModuleCat.{w} ℤ)).mapAction G).map f) ≫
            (e Y).hom = (e X).hom ≫
              ((CommGrp.forget (DiscreteContAction (Type w) G) ⋙ V).map f) := by
  dsimp
  let H := discreteContinuousRepToCommGrp (G := G)
  let := discreteContinuousRepToCommGrp_full G
  let := discreteContinuousRepToCommGrp_essSurj G
  let : H.IsEquivalence := {}
  let E := H.asEquivalence
  let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type w) (G := G)) ⋙
    ObjectProperty.ι (Action.IsContinuous (V := Type w) (G := G))
  let W := CommGrp.forget (DiscreteContAction (Type w) G) ⋙ V
  let e := Functor.isoWhiskerRight E.counitIso W
  refine ⟨E.symm, fun X ↦ e.app X, ?_⟩
  intro X Y f
  exact e.hom.naturality f

end Rep
