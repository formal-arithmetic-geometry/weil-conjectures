/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import WeilConjectures.AlgebraicGeometry.FinitePresentationAffineLimitDescent
import WeilConjectures.AlgebraicGeometry.Modules.FinitePresentationTensorProduct

/-!
# Finite-presentation tensor models for an invertible module and its dual

Source: Stacks Project, Limits, Tag 0B8W, proof of (2), and Modules, Tags 01CT(2)
and 01CE(4) (blueprint: lem-trf-invertible-fp-tensor-models).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option maxHeartbeats 800000 in
-- Elaborating the explicit iterated tensor pullbacks exceeds the default heartbeat budget.
/-- An invertible module and its actual internal-Hom dual have finitely presented models
at one stage of an affine transition limit. Their tensor product and the stage's structure
module are finitely presented. The specified pulled-back tensor evaluation is invertible;
no invertibility or local freeness of either model is assumed or asserted.

Source: Stacks Project, Limits, Tag 0B8W, proof of (2); Modules, Tags 01CT(2), 01CE(4)
and 01CD (blueprint: lem-trf-invertible-fp-tensor-models).

Proof:
1. By `lem-pc-tensor-dual-invertible`, the dual of L is invertible and its actual evaluation
   is an isomorphism. Rank-one trivializations from `def-sc-invertible-module` give finite
   presentations of L and its dual, with zero relations and one generator.
2. Apply clause (1) of `lem-trf-fp-modules-affine-limit-descent` to L and its dual. Choose
   a common upper bound of the two resulting indices. Pull both models to that stage;
   `lem-pc-tensor-pullback-finite-presentation` preserves their finite presentation without
   flatness. The canonical composition comparisons of `def-pc-module-pullback`, together
   with the cone equations, give the two displayed pullback isomorphisms a and b.
3. By `lem-trf-fp-sheaf-tensor-product`, the tensor product of the two finitely presented
   models is finitely presented. The structure module has its one-generator presentation
   with zero relations and the identity as its presentation map.
4. The section-normalized comparison of `lem-weil-pbc-module-pullback-tensor` identifies
   the pullback of that tensor with the tensor of the pullbacks. Follow it by a tensor b
   and the evaluation of L. Each arrow is an isomorphism, so their displayed composite is
   an isomorphism. This uses evaluation only on the limit scheme. -/
theorem invertible_fp_tensor_models
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c)
    (L : c.pt.Modules) [L.IsInvertible] :
    (dual L).IsInvertible ∧ L.IsFinitePresentation ∧ (dual L).IsFinitePresentation ∧
      IsIso (dualEvaluation L) ∧
      ∃ (i : I) (A B : (D.obj (op i)).Modules),
        A.IsFinitePresentation ∧ B.IsFinitePresentation ∧
        ∃ (a : (tensorPullback (c.π.app (op i))).obj A ≅ L)
          (b : (tensorPullback (c.π.app (op i))).obj B ≅ dual L),
          (A ⊗ B).IsFinitePresentation ∧
          (𝟙_ (D.obj (op i)).Modules).IsFinitePresentation ∧
          IsIso ((Classical.choose (module_pullback_tensor (c.π.app (op i))) A B).hom ≫
            (a.hom ⊗ₘ b.hom) ≫ dualEvaluation L) := by
  classical
  have hfp (X : Scheme.{u}) (M : X.Modules) [M.IsInvertible] :
      M.IsFinitePresentation := by
    have := IsInvertible.sheafOfModules_isInvertible M
    have := SheafOfModules.IsInvertible.isFiniteLocallyFree M
    infer_instance
  have hdualInv : (dual L).IsInvertible := inferInstance
  have hLfp : L.IsFinitePresentation := hfp _ L
  have hNfp : (dual L).IsFinitePresentation := hfp _ (dual L)
  have heval : IsIso (dualEvaluation L) := inferInstance
  refine ⟨hdualInv, hLfp, hNfp, heval, ?_⟩
  obtain ⟨r, Ar, hAr, ⟨ar⟩⟩ := (finitePresentation_descent_affineLimit D c hc).1 L hLfp
  obtain ⟨s, Bs, hBs, ⟨bs⟩⟩ :=
    (finitePresentation_descent_affineLimit D c hc).1 (dual L) hNfp
  obtain ⟨i, hri, hsi⟩ := directed_of (· ≤ ·) r s
  let A := (tensorPullback (D.map (homOfLE hri).op)).obj Ar
  let B := (tensorPullback (D.map (homOfLE hsi).op)).obj Bs
  have hAfp : A.IsFinitePresentation := isFinitePresentation_tensorPullback _ Ar
  have hBfp : B.IsFinitePresentation := isFinitePresentation_tensorPullback _ Bs
  let a : (tensorPullback (c.π.app (op i))).obj A ≅ L :=
    affineLimitTensorPullbackComparison D c hri Ar ≪≫ ar
  let b : (tensorPullback (c.π.app (op i))).obj B ≅ dual L :=
    affineLimitTensorPullbackComparison D c hsi Bs ≪≫ bs
  refine ⟨i, A, B, hAfp, hBfp, a, b, ?_, hfp _ _, ?_⟩
  · exact isFinitePresentation_tensorProduct A B
  · infer_instance

end AlgebraicGeometry.Scheme.Modules
