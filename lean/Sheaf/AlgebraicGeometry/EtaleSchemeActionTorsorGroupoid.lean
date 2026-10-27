/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.AlgebraicGeometry.SchemeActionTorsorGroupoids

/-! # The groupoid of étale locally trivial equivariant scheme torsors

Source: Stacks Project, examples-stacks.tex, Tags 04WL and 04WM, with étale
local trivializations (blueprint: def-sfb-etale-scheme-action-torsor-groupoid).

The full subcategory retains actual schemes, actions, equivariant cartesian arrows,
and orbit maps from the existing fppf torsor construction. Étale local triviality
implies fppf local triviality, so the latter proof field adds no mathematical data.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.SchemeAction

variable {S : Scheme.{u}} (G V : Over S) [GrpObj G] [ModObj G V]

/-- Local equivariant trivializations on an étale covering sieve.
A cartesian square says exactly that the resulting map to the base change is an
isomorphism. Source: Stacks 04WL, 04WM, étale variant
(blueprint: def-sfb-etale-scheme-action-torsor-groupoid). -/
def IsEtaleLocallyTrivial (X : TorsorObject G V) : Prop :=
  ∃ R : Sieve X.base, R ∈ (Scheme.etaleTopology.over S) X.base ∧
    ∀ (W : Over S) (b : W ⟶ X.base), R b →
      ∃ q : G ⊗ W ⟶ X.space,
        IsPullback q (snd G W) X.projection b ∧
        ∀ (Z : Over S) (g h : Z ⟶ G) (w : Z ⟶ W),
          lift (g * h) w ≫ q = g • (lift h w ≫ q)

/-- Scheme torsors with equivariant maps, with étale local trivializations.
Full-subcategory arrows are the original equivariant cartesian maps preserving the
map to `V`; in each fibre these are precisely equivariant isomorphisms.
Source: Stacks 04WL, 04WM, étale variant
(blueprint: def-sfb-etale-scheme-action-torsor-groupoid). -/
def etaleTorsorGroupoid : BasedCategory (Over S) :=
  BasedCategory.ofFunctor
    (ObjectProperty.ι (IsEtaleLocallyTrivial G V) ⋙ (torsorGroupoid G V).p)

/-- A trivial torsor is already trivial on the maximal étale covering sieve.
Source: Stacks 04WM, formula for the trivial torsor
(blueprint: def-sfb-etale-scheme-action-torsor-groupoid).
Proof: use the maximal sieve and, over `b : W → T`, the map
`(h,w) ↦ (h,b(w))`. The product square is cartesian; multiplication on the
first coordinate proves equivariance. The maximal sieve is covering for every
Grothendieck topology, also over the empty scheme. -/
theorem trivialObject_isEtaleLocallyTrivial (X : ActionObject G V) :
    IsEtaleLocallyTrivial G V (trivialObject G V X) := by
  sorry

/-- The specified trivial-torsor functor with codomain the étale torsor category.
It sends `u` to `(G × T,(h,t) ↦ h • u(t))` and a labelled arrow `h` to right
translation by `h⁻¹`, exactly as in the existing scheme construction.
Source: Stacks 04WM
(blueprint: def-sfb-etale-scheme-action-torsor-groupoid). -/
def etaleTrivialTorsorFunctor :
    BasedFunctor (actionGroupoid G V) (etaleTorsorGroupoid G V) where
  obj X := ⟨trivialObject G V X, trivialObject_isEtaleLocallyTrivial G V X⟩
  map a := ObjectProperty.homMk ((trivialTorsorFunctor G V).map a)
  map_id X := by
    apply ObjectProperty.hom_ext
    exact (trivialTorsorFunctor G V).map_id X
  map_comp a b := by
    apply ObjectProperty.hom_ext
    exact (trivialTorsorFunctor G V).map_comp a b
  w := rfl

end AlgebraicGeometry.SchemeAction
