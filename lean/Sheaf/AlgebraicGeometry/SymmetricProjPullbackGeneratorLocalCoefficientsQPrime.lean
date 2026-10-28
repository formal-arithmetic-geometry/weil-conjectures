/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-! Local `q'` coefficient frames for the normalized pullback generator relation.

Source: Stacks Project, Constructions, Tags 01N2, 01NQ, 01NR and 01OB.
The statement isolates the second (normalized) quotient formula after a local
frame and coefficient formula for `q` have been chosen.
(blueprint: lem-trf-symmetric-proj-pullback-generator-local-coefficients-qprime)
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

/-- The matching local frame for the normalized second quotient map.

The open, the first frame, and its coefficient map are fixed as input. The
conclusion is only the existence of the second frame and its formula, hence is
strictly smaller than the common-coefficient theorem.
-/
theorem normalized_pullback_generator_local_coefficients_qprime
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
    ∀ (q' : M ⟶ D'.line),
    ∀ (U : S.affineOpens) (W : T.Opens) (h : W ≤
      (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom) ⁻¹ᵁ U.1)
      (x : T) (Z : T.Opens) (hZW : Z ≤ W) (hx : x ∈ Z)
      (a : Γ(P, Z)) (c : Γ(E, U.1) → Γ(T, Z)),
      (∀ t : Γ(E, U.1),
        let s := M.presheaf.map (homOfLE (hZW.trans h)).op
          (Scheme.Modules.tensorPullbackSection
            (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
            E U.1 t)
        q.app Z s = c t • a) →
      ∃ (b' : Γ(D'.line, Z)),
        ∀ t : Γ(E, U.1),
          let s := M.presheaf.map (homOfLE (hZW.trans h)).op
            (Scheme.Modules.tensorPullbackSection
              (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
              E U.1 t)
          q'.app Z s = c t • b' := by
  sorry

end AlgebraicGeometry.SymmetricProjTautologicalCharts
