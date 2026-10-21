/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.NoetherianSpace

import Sheaf.AlgebraicGeometry.LocallyFreeTensorSingle
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all Sheaf.Paper.IntegralConstructibleKernels
import all Sheaf.Paper.ConstructibleCokernelsExtensions
import Sheaf.Paper.IntegralLfpLocallyFreeResolution
import all Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-! # Local tensor calculations over ell-adic coefficients

Source: Bhatt--Scholze, Proposition 6.8.11(3), using locally finite free resolutions.
(blueprint: lem-sfb-lfp-tensor-single)
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj ZeroObject
open CategoryTheory Limits MonoidalCategory MonObj Opposite Pretriangulated
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory.TStructure.t

private theorem integral_tensor_single
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X))
    (hF : IsLocallyFinitelyPresented (condensedRingObj (integralCoeff ℓ E) X) F)
    (hG : IsLocallyFinitelyPresented (condensedRingObj (integralCoeff ℓ E) X) G) :
    ((DerivedCategory.singleFunctor _ 0).obj F ⊗
      (DerivedCategory.singleFunctor _ 0).obj G).IsGE (-1) ∧
    ∀ n : ℤ, IsLocallyFinitelyPresented (condensedRingObj (integralCoeff ℓ E) X)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((DerivedCategory.singleFunctor _ 0).obj F ⊗
          (DerivedCategory.singleFunctor _ 0).obj G)) := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let P : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :=
    IsLocallyFinitelyPresented R
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ localFinitePresentation_of_iso e h⟩
  have : P.ContainsZero :=
    ⟨0, isZero_zero _, locallyFinitelyPresented_of_isZero R (isZero_zero _)⟩
  have hpivot : IntegralMatrixPivots.{u} ℓ E := integralMatrix_pivot_cover ℓ E
  have hmatrix : IntegralMatrixKernels.{u} ℓ E := integralMatrixKernels_of_pivots ℓ E hpivot
  have hrational : RationalMatrixKernels.{u} ℓ E :=
    rationalMatrixKernels_of_integral ℓ E hmatrix
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, c, hc, hf⟩
    apply localFinitePresentation_of_iso (limit.isoLimitCone ⟨c, hc⟩)
    exact integral_lfp_kernel_of_rational ℓ E hrational X f hf.1 hf.2⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, c, hc, hf⟩
    exact localFinitePresentation_of_iso (colimit.isoColimitCocone ⟨c, hc⟩)
      (lfp_cokernel f hf.1 hf.2)⟩
  have : P.IsClosedUnderExtensions := ⟨fun hs h₁ h₃ ↦ lfp_extension _ hs h₁ h₃⟩
  let Q := DerivedCategory.homologyProperty P
  have : Q.IsTriangulated := inferInstance
  obtain ⟨F₁, F₀, f, g, w, hs, h₁, h₀⟩ := integral_lfp_locallyFree_resolution X ℓ E F hF
  let T := (tensorRight ((DerivedCategory.singleFunctor _ 0).obj G)).mapTriangle.obj
    hs.singleTriangle
  have hT : T ∈ distTriang _ :=
    (tensorRight ((DerivedCategory.singleFunctor _ 0).obj G)).map_distinguished _
      hs.singleTriangle_distinguished
  have h₁' : DerivedCategory.TStructure.t.IsGE T.obj₁ 0 :=
    (locallyFree_tensor_single (integralCoeff ℓ E) X F₁ G h₁ hG).1
  have h₀' : DerivedCategory.TStructure.t.IsGE T.obj₂ 0 :=
    (locallyFree_tensor_single (integralCoeff ℓ E) X F₀ G h₀ hG).1
  constructor
  · change DerivedCategory.TStructure.t.IsGE T.obj₃ (-1)
    have hb : DerivedCategory.TStructure.t.IsGE T.obj₂ (-1) :=
      DerivedCategory.TStructure.t.isGE_of_ge T.obj₂ (-1) 0 (by decide)
    have ha : DerivedCategory.TStructure.t.IsGE (T.obj₁⟦(1 : ℤ)⟧) (-1) :=
      DerivedCategory.TStructure.t.isGE_shift T.obj₁ 0 1 (-1) (by decide)
    exact DerivedCategory.TStructure.t.isGE₂ T.rotate
      (rot_of_distTriang _ hT) (-1) hb ha
  · change Q T.obj₃
    exact Q.ext_of_isTriangulatedClosed₃ T hT
      (locallyFree_tensor_single (integralCoeff ℓ E) X F₁ G h₁ hG).2
      (locallyFree_tensor_single (integralCoeff ℓ E) X F₀ G h₀ hG).2

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ]
  (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]

/-- The tensor of two locally finitely presented ell-adic module sheaves has
no cohomology below degree -1, and its cohomology is locally finitely presented.
Source: Bhatt--Scholze, Proposition 6.8.11(3), expanded using the library's
integral locally finite free resolution.
Proof: in the field cases local triviality makes the first factor locally finite free,
so the finite free tensor calculation gives the assertion (and a stronger lower bound 0).
For integral coefficients take the short exact two-term locally finite free resolution
of the first factor, and tensor its distinguished triangle with the second factor.
Both resolved terms have cohomology in degree zero and locally finite presentation.
The rotated triangle gives the lower bound -1. The upper bound 0 is the general
right t-exactness of derived tensor. Locally finitely presented integral module sheaves
are closed under kernels, cokernels and extensions; hence their homology property is
triangulated and the third term has locally finitely presented cohomology.
(blueprint: lem-sfb-lfp-tensor-single) -/
theorem lfp_tensor_single
    {ℓ : ℕ} [h : IsEllAdicFinitenessCoefficient ℓ Λ]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hF : IsLocallyFinitelyPresented (condensedRingObj Λ X) F)
    (hG : IsLocallyFinitelyPresented (condensedRingObj Λ X) G) :
    ((DerivedCategory.singleFunctor _ 0).obj F ⊗
      (DerivedCategory.singleFunctor _ 0).obj G).IsGE (-1) ∧
    ∀ n : ℤ, IsLocallyFinitelyPresented (condensedRingObj Λ X)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj G)) := by
  cases h with
  | continuous E =>
    have hfree : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
        Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (U.f i)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
          (((ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod _).obj F) := by
      let E' := ULift.{u} E
      let : NormedField E' :=
        { (inferInstance : NormedCommRing E'), (inferInstance : Field E') with
          norm_mul a b := norm_mul a.down b.down }
      have : IsCommMonObj (Profinite.continuousCoefficientRingObj E') :=
        Sheaf.isCommMonObj_sheafCompose_obj
          (coherentTopology Profinite.{u}) (Profinite.continuousCoefficientRingSheaf E')
          (by
            intro S a b
            apply ULift.ext
            change (a.down * b.down : C(S.unop, E')) = b.down * a.down
            exact mul_comm a.down b.down)
      let e := (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (liftCoefficientIso E)
      let φ := (upperStarFromPoint X).map e.hom
      have : IsMonHom e.hom := Sheaf.isMonHom_sheafCompose_map
        (coherentTopology Profinite.{u}) (liftCoefficientIso E).hom
      have : IsMonHom φ := inferInstance
      have hf := exists_finiteFree_cover_of_condensedField_lfp ℓ E' X
        ((Mod.comap (inv φ)).obj F) (lfp_comap (inv φ) hF)
      exact locally_free_of_iso (locally_free_comap φ hf)
        ((Mod.comapEquivalenceOfIsIso φ).counitIso.app F)
    obtain ⟨hb, hl⟩ := locallyFree_tensor_single _ X F G hfree hG
    have := hb
    exact ⟨DerivedCategory.TStructure.t.isGE_of_ge _ (-1) 0 (by decide), hl⟩
  | algebraicClosure =>
    obtain ⟨hb, hl⟩ := locallyFree_tensor_single _ X F G (algcl_lf ℓ X F hF) hG
    have := hb
    exact ⟨DerivedCategory.TStructure.t.isGE_of_ge _ (-1) 0 (by decide), hl⟩
  | integral E =>
    let := PadicAlgCl.normedFieldOfAlgebra ℓ E
    let : NormedAlgebra ℚ_[ℓ] E :=
      { norm_smul_le c x := by
          change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
            ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
            PadicAlgCl.norm_extends] }
    exact integral_tensor_single ℓ E X F G hF hG
  | unitBall E O hO =>
    have he : O = continuousIntegers ℓ E := by
      ext x
      rw [hO]
      change ‖x‖ ≤ 1 ↔ ‖x‖₊ ≤ 1
      simpa only [NNReal.coe_one, coe_nnnorm] using
        (NNReal.coe_le_coe : (‖x‖₊ : ℝ) ≤ ((1 : NNReal) : ℝ) ↔ ‖x‖₊ ≤ 1)
    subst O
    exact integral_tensor_single ℓ E X F G hF hG


end AlgebraicGeometry.ProEtale.CondensedRing
