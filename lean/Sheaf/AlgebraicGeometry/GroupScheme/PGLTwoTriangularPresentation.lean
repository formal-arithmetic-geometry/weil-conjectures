/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-! # Relative PGL₂ with its triangular and diagonal subgroups

Source: Conrad, Reductive group schemes, Proposition 4.2.7, printed pp.123--124.
(blueprint: def-sfb-pgl-two-triangular-presentation).

A presentation specifies the represented fppf scalar quotient and the two subgroup
sheaf images. It does not assert that arbitrary projective points have global matrix lifts.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.PGLTwoTriangular

/-- Membership in the fppf sheaf image of matrices satisfying P. Covering sieves allow
nonaffine and nonreduced test schemes. Source: Conrad, Proposition 4.2.7, pp.123--124
(blueprint: def-sfb-pgl-two-triangular-presentation). -/
def LocallyMatrix {S : Scheme.{u}} (G : Grp (Over S))
    (q : ∀ V : Over S, Matrix.ProjGenLinGroup (Fin 2) Γ(V.left, ⊤) →* (V ⟶ G.X))
    (P : ∀ V : Over S, Matrix.GeneralLinearGroup (Fin 2) Γ(V.left, ⊤) → Prop)
    (V : Over S) (z : V ⟶ G.X) : Prop :=
  ∃ R : Sieve V, R ∈ (Scheme.fppfTopology.over S) V ∧
    ∀ (W : Over S) (h : W ⟶ V), R h →
      ∃ m : Matrix.GeneralLinearGroup (Fin 2) Γ(W.left, ⊤),
        P W m ∧ q W (Matrix.ProjGenLinGroup.mk m) = h ≫ z

/-- A relative presentation of PGL₂, B∞ and D. Injectivity and fppf local surjectivity
identify G with the sheafification of GL₂/scalars; the two image conditions specify
B∞ and D uniquely as subgroup functors. Source: Conrad, Proposition 4.2.7, pp.123--124
(blueprint: def-sfb-pgl-two-triangular-presentation). -/
structure Presentation {S : Scheme.{u}} (G B D : Grp (Over S))
    (iB : B ⟶ G) (iD : D ⟶ B) where
  quotient : ∀ V : Over S,
    Matrix.ProjGenLinGroup (Fin 2) Γ(V.left, ⊤) →* (V ⟶ G.X)
  injective : ∀ V : Over S, Function.Injective (quotient V)
  naturality : ∀ (V W : Over S) (h : W ⟶ V)
    (m : Matrix.ProjGenLinGroup (Fin 2) Γ(V.left, ⊤)),
    quotient W (Matrix.ProjGenLinGroup.map h.left.appTop.hom m) = h ≫ quotient V m
  locally_surjective : ∀ (V : Over S) (z : V ⟶ G.X),
    LocallyMatrix G quotient (fun _ _ ↦ True) V z
  closed_upper : IsClosedImmersion iB.hom.hom.left
  closed_diagonal : IsClosedImmersion iD.hom.hom.left
  upper_image : ∀ (V : Over S) (z : V ⟶ G.X),
    (∃ b : V ⟶ B.X, b ≫ iB.hom.hom = z) ↔
      LocallyMatrix G quotient (fun _ m ↦ m.val 1 0 = 0) V z
  diagonal_image : ∀ (V : Over S) (z : V ⟶ G.X),
    (∃ d : V ⟶ D.X, d ≫ iD.hom.hom ≫ iB.hom.hom = z) ↔
      LocallyMatrix G quotient (fun _ m ↦ m.val 1 0 = 0 ∧ m.val 0 1 = 0) V z

end AlgebraicGeometry.PGLTwoTriangular
