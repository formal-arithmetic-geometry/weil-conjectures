/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPerverseSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverse.CondensedCurvePerverseStatement
public import WeilConjectures.AlgebraicGeometry.CurvePunctual.CurvePunctualSupport
public import WeilConjectures.AlgebraicGeometry.AffineLineConventions.AffineLineConventions
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstructibleTruncations
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.CategoryTheory.Simple

/-!
# Weil middle perverse simple objects

Source: latest blueprint, `prop-a1-curve-perverse-simples.proof.md`, middle-extension simplicity,
classification and saturation.
(blueprint: lem-a1-weil-middle-simple-case).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCurvePerverseStatement

/-- The classification in the pure degree-minus-one case.
Source: latest blueprint, `prop-a1-curve-perverse-simples.proof.md`, middle-extension simplicity,
classification and saturation.
Proof: The heart description and H^0 P = 0 identify P with F[1], where F has
no punctual subsheaf. If P is simple, choose a dense open j where N = j^*F is lisse.
The unit F -> j_*N has punctual kernel and cokernel, and its kernel is zero. The
rotated sheaf triangle gives a perverse short exact sequence with subobject the
punctual cokernel in degree zero and nonzero quotient (j_*N)[1]. Simplicity kills
the cokernel. If N had a proper nonzero lisse subsheaf N', remove the largest
punctual subsheaf from coker(j_*N' -> j_*N); its kernel in j_*N and the resulting
punctual-free quotient yield a nontrivial perverse sequence after shifting.
This proves irreducibility of N. Conversely a perverse subobject sequence of
(j_*N)[1] restricts on the dense lisse open of the blueprint to a subobject of the irreducible
restriction of N. Part (4) of lem-wf-dense-open-pi1-surjective preserves this
irreducibility and supplies the zero-or-full subobject dichotomy. In the zero
restriction case the no-punctual condition kills
H^-1 of the subobject, and the injective restriction unit for H^-1 of the quotient
is forced to be invertible by the unit isomorphism on N; hence the subobject is
zero. In the full restriction case the quotient's H^-1 is punctual and therefore
zero, so the quotient is zero. Nonzeroness follows by restricting j_*N to N.
Run the argument in the actual derived category of Weil modules. The exact
forgetful functor creates kernels and cokernels with their canonical Frobenius
structures. Choose dense opens over the finite field, using
lem-wf-dense-open-pi1-surjective (3)-(4) on
Weil groups. Irreducibility refers to Weil-stable subobjects. All units,
finite-support summands and saturation sequences are equivariant; the middle
image carries the canonical Frobenius base-change mate. No geometric
irreducibility is required.
(blueprint: lem-a1-weil-middle-simple-case). -/
theorem weil_middle_simple_case
    (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) [Fact (ringChar D.k).Prime]
    [Fact (ringChar D.k ≠ ell)]
    (C₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType C₀.hom]
    [QuasiCompact C₀.hom] [IsSeparated C₀.hom] [Smooth C₀.hom]
    (_hPure : Scheme.IsPureDimension C₀.left 1)
    (P : (CondensedRing.CurveWeil.upperZero D ell C₀ ⊓
      CondensedRing.CurveWeil.lowerZero D ell C₀).FullSubcategory)
    (_hCoh : IsZero ((DerivedCategory.homologyFunctor _ 0).obj P.obj.obj)) :
    Simple P ↔
  ∃ U₀ : Over (Spec (.of D.k₀)),
    Exists fun [_hft : LocallyOfFiniteType U₀.hom] ↦
      Exists fun [_hqc : QuasiCompact U₀.hom] ↦
        ∃ (j₀ : U₀ ⟶ C₀), IsOpenImmersion j₀.left ∧ DenseRange j₀.left ∧
          ∃ (M : WeilConjectures.NativeL2.WeilModule D ell U₀)
            (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) M.carrier),
            ¬ IsZero M ∧
            Simple (⟨M, hM⟩ : ObjectProperty.FullSubcategory
              (fun N : WeilConjectures.NativeL2.WeilModule D ell U₀ ↦
                IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) N.carrier)) ∧
            Nonempty (P.obj.obj ≅
              ((DerivedCategory.singleFunctor _ 0).obj
                (WeilConjectures.NativeL2.middleWeilImage D ell j₀ M))⟦(1 : ℤ)⟧) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedCurvePerverseStatement
