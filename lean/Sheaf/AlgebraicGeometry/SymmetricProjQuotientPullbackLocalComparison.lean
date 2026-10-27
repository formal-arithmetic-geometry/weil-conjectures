/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange

/-! # Local frame atlas for normalized symmetric Proj pullback

Source: Stacks Project, Constructions, Tags 01NQ, 01NR and 01OB.
(blueprint: lem-trf-symmetric-proj-quotient-pullback-comparison-local).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

attribute [local instance 2000] CategoryTheory.Abelian.hasFiniteLimits

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι
  Scheme.GradedAlgebraData.PullbackData.relProjComparison

/-- Common local frames and quotient coefficients for the fixed Proj pullback map.

Source: Stacks Project, Constructions, Tags 01NQ and 01N2 (base-change fractions),
01NR (twist frames and transition ratios), and 01OB (quotient normalization).
(blueprint: lem-trf-symmetric-proj-quotient-pullback-comparison-local).

Proof: cover the source by degree-one basic opens over pairs of affine base opens.
Scalar extension preserves the degree-one cover. On each such open choose the
pulled degree-one frame and its image frame. Both are free generators, since
localizing at the corresponding generator trivializes the degree-one twist.
On intersections the transition coefficient is the same pulled homogeneous ratio;
this remains true after any further restriction. The equation hb identifies the
image of every pulled module generator with the same coefficient times the two
frames. Pure tensors locally generate the tensor pullback; linearity and sheaf
uniqueness give this coefficient equation for every section on every subopen of a chart.
The section-normalized composition isomorphisms identify these with the two
morphisms below, including their equality transport. Refining base intersections
by affine opens gives compatibility without a separatedness assumption. Empty
schemes admit the empty cover; zero rings and empty charts satisfy the same formulas.
No global line isomorphism or gluing of line morphisms is asserted here. -/
theorem exists_normalized_pullback_frame_atlas
    {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
    [((Scheme.Modules.tensorPullback g).obj E).IsQuasicoherent]
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (D' : ProjectiveBundleQuotientGeometry.TautologicalQuotient
      ((Scheme.Modules.tensorPullback g).obj E))
    (b : Scheme.GradedAlgebraData.PullbackData g (SymmetricAlgebraSheaf.gradedAlgebraData E)
      (SymmetricAlgebraSheaf.gradedAlgebraData ((Scheme.Modules.tensorPullback g).obj E)))
    (hb : ∀ (U : S.affineOpens) (W : X.affineOpens) (h : W.1 ≤ g ⁻¹ᵁ U.1)
      (m : E.val.obj (op U.1)),
      b.map h (SymmetricAlgebra.ι Γ(S, U.1) _ m) =
        SymmetricAlgebra.ι Γ(X, W.1) _
          (((Scheme.Modules.tensorPullback g).obj E).presheaf.map (homOfLE h).op
            (Scheme.Modules.tensorPullbackSection g E U.1 m)))
    (e : (Scheme.Modules.tensorPullback
        (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)).obj E =
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData
          ((Scheme.Modules.tensorPullback g).obj E)).relProjHom ≫ g)).obj E) :
    let T := (SymmetricAlgebraSheaf.gradedAlgebraData
      ((Scheme.Modules.tensorPullback g).obj E)).relProj
    let M := (Scheme.Modules.tensorPullback
      (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)).obj E
    let P := (Scheme.Modules.tensorPullback b.relProjComparison).obj D.line
    let q : M ⟶ P :=
      (Scheme.Modules.tensorPullbackSectionComp b.relProjComparison
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
        (Scheme.Modules.tensorPullback b.relProjComparison).map D.quotient
    let q' : M ⟶ D'.line := (eqToIso e).hom ≫
      (Scheme.Modules.tensorPullbackSectionComp
        (SymmetricAlgebraSheaf.gradedAlgebraData
          ((Scheme.Modules.tensorPullback g).obj E)).relProjHom g).hom.app E ≫ D'.quotient
    ∃ (ι : Type u) (U : ι → T.Opens) (s : ∀ i, Γ(P, U i))
      (t : ∀ i, Γ(D'.line, U i)),
      (⨆ i, U i) = ⊤ ∧ (∀ i, Scheme.Modules.IsFreeGenerator (s i)) ∧
      (∀ i, Scheme.Modules.IsFreeGenerator (t i)) ∧
      (∀ i j (V : T.Opens) (hi : V ≤ U i) (hj : V ≤ U j) (a c : Γ(T, V)),
        a • P.presheaf.map (homOfLE hi).op (s i) =
          c • P.presheaf.map (homOfLE hj).op (s j) →
        a • D'.line.presheaf.map (homOfLE hi).op (t i) =
          c • D'.line.presheaf.map (homOfLE hj).op (t j)) ∧
      ∀ i (V : T.Opens) (hi : V ≤ U i) (m : Γ(M, V)),
        ∃ c : Γ(T, V),
          q.app V m = c • P.presheaf.map (homOfLE hi).op (s i) ∧
          q'.app V m = c • D'.line.presheaf.map (homOfLE hi).op (t i) := by sorry

end AlgebraicGeometry.SymmetricProjTautologicalCharts
