module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Sheaf.AlgebraicGeometry.EtaleFieldGsets
public import Sheaf.RepresentationTheory.DiscreteContinuousRep

@[expose] public section

universe u w
open CategoryTheory
namespace Rep

/--
Source: Stacks Project, Tag 04JQ, proof of lemma-equivalence-abelian-sheaves-point.
(blueprint: lem-exc-discrete-continuous-rep-commgrp-compatible).

Proof: Given a commutative internal group object, transport its multiplication,
unit, and inverse along Cartesian comparison maps to obtain an abelian group on the
carrier; equivariance makes the action linear and continuity gives open stabilizers.
Conversely, use the additive and integer-module operations of a discrete continuous
representation to form the internal group object. On morphisms both constructions
use the underlying equivariant map, and the carrier comparisons commute with every
such map.

This is the objectwise construction needed for the equivalence: from a commutative
internal group object one constructs the integer module structure on its carrier,
and conversely; the construction also supplies chosen carrier isomorphisms and
checks their compatibility with every equivariant morphism.  The construction is
left as a separate theorem so that the categorical natural-isomorphism assembly
below is a short formal step.
-/
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
  sorry

end Rep
