/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Sheaf.AlgebraicGeometry.AffineActionQuotientStack

/-! # The groupoid of Zariski locally trivial scheme torsor pairs

Source: Stacks Project, examples-stacks.tex, Tag 04UV (section-group-quotient-stacks),
restricted to Zariski locally trivial scheme torsors
(blueprint: def-sfb-zariski-torsor-groupoid).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.SchemeAction

variable {S : Scheme.{u}} (G J : Over S) [GrpObj G] [ModObj G J]

/-- Equivariant product trivializations on Zariski neighbourhoods covering the base.
The cartesian square identifies `G × U` with the actual base change of the torsor.
Source: Stacks 04UV, torsor description with the stipulated Zariski triviality
(blueprint: def-sfb-zariski-torsor-groupoid). -/
def IsZariskiTrivial (X : TorsorObject G J) : Prop :=
  ∀ x : X.base.left, ∃ (U : Over S) (j : U ⟶ X.base),
    IsOpenImmersion j.left ∧ x ∈ Set.range j.left.base ∧
      ∃ t : G ⊗ U ⟶ X.space,
        IsPullback t (snd G U) X.projection j ∧
          ∀ (W : Over S) (g h : W ⟶ G) (a : W ⟶ U),
            lift (g * h) a ≫ t = g • (lift h a ≫ t)

/-- The full category of Zariski locally trivial torsor pairs. Its arrows are the
existing cartesian equivariant scheme maps, preserving the map to `J`.
Source: Stacks 04UV (blueprint: def-sfb-zariski-torsor-groupoid). -/
abbrev ZariskiTorsorObject := ObjectProperty.FullSubcategory (IsZariskiTrivial G J)

/-- The torsor presentation over schemes, retaining its actual base projection.
Source: Stacks 04UV (blueprint: def-sfb-zariski-torsor-groupoid). -/
def zariskiTorsorGroupoid : BasedCategory (Over S) :=
  BasedCategory.ofFunctor
    (ObjectProperty.ι (IsZariskiTrivial G J) ⋙ (torsorGroupoid G J).p)

/-- The trivial torsor is Zariski trivial, with its identity product chart.
Source: Stacks 04UV (blueprint: def-sfb-zariski-torsor-groupoid).
Proof: at every point take the whole base with its identity open immersion and
identity product trivialization. The square is cartesian and equivariance is
associativity of multiplication. For an empty base the condition is vacuous. -/
theorem trivialObject_isZariskiTrivial (X : ActionObject G J) :
    IsZariskiTrivial G J (trivialObject G J X) := by
  sorry

/-- The canonical trivial-torsor map, with the inherited actual maps on arrows.
Source: Stacks 04UV (blueprint: def-sfb-zariski-torsor-groupoid). -/
def zariskiQuotientAtlas :
    BasedFunctor (discreteModuli (yoneda.obj J)) (zariskiTorsorGroupoid G J) where
  obj X := ⟨(quotientAtlas G J).obj X,
    trivialObject_isZariskiTrivial G J ((schemeToActionGroupoid G J).obj X)⟩
  map a := ObjectProperty.homMk ((quotientAtlas G J).map a)
  map_id X := congrArg ObjectProperty.homMk ((quotientAtlas G J).map_id X)
  map_comp a b := congrArg ObjectProperty.homMk ((quotientAtlas G J).map_comp a b)
  w := rfl

/-- The trivial pair of a test point as an object in the actual fibre groupoid.
Source: Stacks 04UV (blueprint: def-sfb-zariski-torsor-groupoid). -/
def zariskiTrivialFiber (T : Over S) (x : T ⟶ J) :
    Functor.Fiber (zariskiTorsorGroupoid G J).p T :=
  ⟨⟨trivialObject G J ⟨T, x⟩, trivialObject_isZariskiTrivial G J ⟨T, x⟩⟩, rfl⟩

end AlgebraicGeometry.SchemeAction
