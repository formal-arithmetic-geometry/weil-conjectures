/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjPullbackGeneratorLocalCoefficients
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjCrossTensorFromLocal

/-! # Degree-two relation on pulled module generators.
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
open Scheme.Modules CategoryTheory.MonoidalCategory

/-- The degree-two cross relation on actual pulled generators over affine opens.

Source: Stacks Project, Constructions, Tags 01N2, 01NQ, 01NR, and 01OB. -/
theorem normalized_pullback_generator_cross_tensor
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
    ∀ (U : S.affineOpens) (W : T.affineOpens)
      (h : W.1 ≤ (b.relProjComparison ≫
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom) ⁻¹ᵁ U.1)
      (m n : Γ(E, U.1)),
      let m' := M.presheaf.map (homOfLE h).op
        (Scheme.Modules.tensorPullbackSection
          (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
          E U.1 m)
      let n' := M.presheaf.map (homOfLE h).op
        (Scheme.Modules.tensorPullbackSection
          (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)
          E U.1 n)
      Scheme.Modules.tmulSection (q.app W.1 m') (q'.app W.1 n') =
        Scheme.Modules.tmulSection (q.app W.1 n') (q'.app W.1 m')  := by
  exact cross_tensor_of_local_coefficients_public
    (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom) E
    ((Scheme.Modules.tensorPullbackSectionComp b.relProjComparison
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
      (Scheme.Modules.tensorPullback b.relProjComparison).map D.quotient)
    ((eqToIso e).hom ≫
      (Scheme.Modules.tensorPullbackSectionComp
        (SymmetricAlgebraSheaf.gradedAlgebraData
          ((Scheme.Modules.tensorPullback g).obj E)).relProjHom g).hom.app E ≫ D'.quotient)
    (normalized_pullback_generator_local_coefficients g E D D' b hb e)

end AlgebraicGeometry.SymmetricProjTautologicalCharts
