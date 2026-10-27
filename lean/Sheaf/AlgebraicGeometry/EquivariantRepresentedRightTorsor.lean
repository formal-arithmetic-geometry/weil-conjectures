module

public import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Commuting left actions on represented right torsors

Source: Alper--Halpern-Leistner--Heinloth, Cartan--Iwahori--Matsumoto
Decompositions, Section 2, Claims 1--2, printed p.2
(blueprint: def-sfb-equivariant-represented-right-torsor).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- A left G-action on a represented right H-torsor, covering the given action on
its base and commuting with the right H-action. All laws are scheme-theoretic.
Source: AHLH, Section 2, Claims 1--2, printed p.2
(blueprint: def-sfb-equivariant-represented-right-torsor). -/
structure EquivariantRepresentedRightTorsor {B : Scheme.{u}}
    (G H : Grp (Over B)) (S : Over B) [ModObj G.X S] where
  torsor : RepresentedRightTorsor H S
  leftAction : ModObj G.X torsor.space
  covers : ∀ (T : Over B) (g : T ⟶ G.X) (p : T ⟶ torsor.space),
    (lift g p ≫ leftAction.smul) ≫ torsor.projection = g • (p ≫ torsor.projection)
  commutes : ∀ (T : Over B) (g : T ⟶ G.X) (p : T ⟶ torsor.space) (h : T ⟶ H.X),
    lift g (lift p h ≫ torsor.action) ≫ leftAction.smul =
      lift (lift g p ≫ leftAction.smul) h ≫ torsor.action

/-- A cartesian arrow of equivariant right torsors over j. Its cartesian square
identifies the source with the restriction of the target, preserving both actions;
when j is the identity it is precisely an equivariant torsor isomorphism.
Source: AHLH, Section 2, Claim 2, printed p.2
(blueprint: def-sfb-equivariant-represented-right-torsor). -/
structure EquivariantRepresentedRightTorsor.RestrictionIso {B : Scheme.{u}}
    {G H : Grp (Over B)} {S V : Over B} [ModObj G.X S] [ModObj G.X V]
    (j : S ⟶ V) (P : EquivariantRepresentedRightTorsor G H S)
    (Q : EquivariantRepresentedRightTorsor G H V) where
  map : P.torsor.space ⟶ Q.torsor.space
  cartesian : IsPullback map P.torsor.projection Q.torsor.projection j
  right_equivariant : ∀ (T : Over B) (p : T ⟶ P.torsor.space) (h : T ⟶ H.X),
    (lift p h ≫ P.torsor.action) ≫ map = lift (p ≫ map) h ≫ Q.torsor.action
  left_equivariant : ∀ (T : Over B) (g : T ⟶ G.X) (p : T ⟶ P.torsor.space),
    (lift g p ≫ P.leftAction.smul) ≫ map = lift g (p ≫ map) ≫ Q.leftAction.smul

end AlgebraicGeometry
