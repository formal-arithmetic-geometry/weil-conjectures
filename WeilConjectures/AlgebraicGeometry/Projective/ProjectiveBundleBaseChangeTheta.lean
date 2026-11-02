/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleRealizationPullbackAtlas
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleRealizationThetaFromAtlas

/-! # Quotient-line comparison along normalized projective-bundle base change
Source: Stacks Project, Constructions, Tag 01O3.
(blueprint: lem-pur-projective-bundle-base-change-theta). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
attribute [local irreducible] Scheme.Modules.tensorPullback
  projectiveBundleTensorPullbackIso projectiveBundlePullbackId projectiveBundlePullbackComp
  projectiveBundlePullbackCongr projectiveBundlePullbackAdjunction projectiveBundlePullbackUnitIso
  projectiveBundlePullbackSection

end AlgebraicGeometry

namespace AlgebraicGeometry

/-- A fixed normalized coefficient comparison pulls the degree-one quotient line back to
the normalized quotient line on the source.
Source: Stacks Project, Tags 01OB and 01O3.
Proof: fix an affine base pair and put R = Γ(B,U), S = Γ(B',U'). Give S its R-algebra
structure through g.appLE, and the target graded ring the induced R-algebra structure.
The degreewise base-change condition gives base change on the direct sum of all degrees.
Give the target ring its source-ring algebra structure through b.map. The resulting scalar
tower is its scalar compatibility equation, so Algebra.IsPushout.equiv gives the algebra
isomorphism S tensor A(U) ≃ A'(U'). Its pure-tensor formula sends 1 tensor a to b(a).
In each degree, the same base-change condition says that b of the source degree spans the
target degree. The relative-Proj comparison has the corresponding basic-open and fraction
formulas by its definition on affine pairs. These are exactly the hypotheses of the
degree-one scalar-extension twist comparison. Apply it and conjugate by the specified
twist charts of D and D'. On standard opens its map sends the
pulled fraction a/f^m to b(a)/b(f)^m. These maps and inverses agree after affine refinement of
every overlap because coefficient maps commute with restriction. Glue the maps and inverses
by the module-sheaf axiom. Evaluating on each pulled section 1 tensor v gives the prescribed
quotient square by the coefficient generator equation. Pure pullback sections generate
locally, so linearity and sheaf separatedness give the global equation. The tensor pullback
comparisons are pinned to the same units, so the displayed comparisons are the required ones.
The argument includes empty bases and zero section rings and assumes no flatness.
(blueprint: lem-pur-projective-bundle-base-change-theta). -/
theorem exists_projectiveBundleBaseChangeTheta
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (D : ProjectiveBundleRealization B F) (D' : ProjectiveBundleRealization B' F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F)
    (b : Scheme.GradedAlgebraData.PullbackData g D.A.data D'.A.data)
    (hb : ∀ (U : B.affineOpens) (U' : B'.affineOpens) (h : U'.1 ≤ g ⁻¹ᵁ U.1)
      (x : F.val.obj (op U.1)),
      b.map h (D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ x)) =
        D'.A.sectionEquiv U' (SymmetricAlgebra.ι _ _ (e.inv.app U'.1
          (((Scheme.Modules.tensorPullback g).obj F).presheaf.map (homOfLE h).op
            (projectiveBundlePullbackSection g x))))) :
    ∃ theta : (Scheme.Modules.tensorPullback b.relProjComparison).obj D.L ≅ D'.L,
      projectiveBundleThetaQuotientLaw D D' g e b.relProjComparison b.isPullback.w theta := by
  obtain ⟨A⟩ := exists_projectiveBundleRealizationPullbackAtlas D D' g e b hb
  exact projectiveBundleRealizationTheta_of_atlas D D' g e b A

end AlgebraicGeometry
