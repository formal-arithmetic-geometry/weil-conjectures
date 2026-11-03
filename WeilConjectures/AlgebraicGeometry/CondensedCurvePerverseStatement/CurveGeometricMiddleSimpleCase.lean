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
# Geometric middle perverse simple objects

Source: latest blueprint, `prop-a1-curve-perverse-simples.proof.md`, middle-extension simplicity,
classification and saturation.
(blueprint: lem-a1-geometric-middle-simple-case).
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
(blueprint: lem-a1-geometric-middle-simple-case). -/
theorem geometric_middle_simple_case
    (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (C : Over (Spec (.of k))) [LocallyOfFiniteType C.hom] [QuasiCompact C.hom]
    [IsSeparated C.hom] [Smooth C.hom] (_hPure : Scheme.IsPureDimension C.left 1)
    (P : (CondensedRing.FiniteOrClosedPerverseLEZero ell hk C ⊓
      CondensedRing.FiniteOrClosedPerverseGEZero ell hk C).FullSubcategory)
    (_hCoh : IsZero ((DerivedCategory.homologyFunctor _ 0).obj P.obj.obj)) :
    Simple P ↔
  ∃ (U : Scheme.{u}) (j : U ⟶ C.left), IsOpenImmersion j ∧ DenseRange j ∧
    ∃ (N : CondensedCurvePerverse.Modules (Profinite.padicAlgClRingObj ell) U)
      (hN : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) N),
      ¬ IsZero N ∧
      Simple (⟨N, hN⟩ : ObjectProperty.FullSubcategory
        (IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell))) ∧
      Nonempty (P.obj.obj ≅
        ((DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ell) j).obj N))⟦(1 : ℤ)⟧) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedCurvePerverseStatement
