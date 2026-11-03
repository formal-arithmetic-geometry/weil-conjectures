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
# Weil punctual perverse simple objects

Source: latest blueprint, `prop-a1-curve-perverse-simples.proof.md`, punctual simplicity and the
punctual classification case.
(blueprint: lem-a1-weil-punctual-simple-case).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCurvePerverseStatement

/-- The classification in the pure degree-zero case.
Source: latest blueprint, `prop-a1-curve-perverse-simples.proof.md`, punctual simplicity and the
punctual classification case.
Proof: The Weil heart description identifies P with G[0]. Its underlying geometric
sheaf G has finite closed support stable under Frobenius. In any perverse subobject
sequence of G[0], the six-term sequence makes the negative cohomology of the
subobject zero. The negative cohomology of the quotient embeds into punctual H^0
of the subobject, so it is punctual and is zero by the no-punctual-subobject
condition. Thus perverse subobjects here are exactly constructible Weil-sheaf
subobjects. Conversely sheaf subobject sequences are perverse by the heart
criterion for distinguished triangles.
Localization on the finite geometric support decomposes the underlying sheaf into
closed-point direct images. Frobenius permutes these geometric summands. Grouping
them into entire orbits gives Weil-stable summands indexed by closed points of C₀.
A simple Weil sheaf has precisely one nonzero orbit summand, even if that orbit
contains several geometric points. Exact fully faithful closed direct image
identifies it with the canonical middleWeilImage of a constructible Weil module E
on the geometric fibre of Spec k(x). Its Weil-stable subobjects correspond exactly
to those of E, so E is simple. Conversely a simple E has only zero and full
Weil-stable supported subobjects, and hence its degree-zero placement is simple
in the perverse Weil heart. The zero object satisfies neither alternative.
All kernels, cokernels, restriction maps and orbit decompositions retain their
canonical Frobenius structures. No geometric irreducibility is asserted.
(blueprint: lem-a1-weil-punctual-simple-case). -/
theorem weil_punctual_simple_case
    (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) [Fact (ringChar D.k).Prime]
    [Fact (ringChar D.k ≠ ell)]
    (C₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType C₀.hom]
    [QuasiCompact C₀.hom] [IsSeparated C₀.hom] [Smooth C₀.hom]
    (_hPure : Scheme.IsPureDimension C₀.left 1)
    (P : (CondensedRing.CurveWeil.upperZero D ell C₀ ⊓
      CondensedRing.CurveWeil.lowerZero D ell C₀).FullSubcategory)
    (_hCoh : IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj P.obj.obj)) :
    Simple P ↔
  ∃ (x : C₀.left) (hx : IsClosed ({x} : Set C₀.left)),
    letI : IsClosedImmersion (C₀.left.fromSpecResidueField x) :=
      (AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion).mp hx
    let Z₀ := Over.mk (C₀.left.fromSpecResidueField x ≫ C₀.hom)
    letI : LocallyOfFiniteType Z₀.hom := inferInstanceAs
      (LocallyOfFiniteType (C₀.left.fromSpecResidueField x ≫ C₀.hom))
    letI : QuasiCompact Z₀.hom := inferInstanceAs
      (QuasiCompact (C₀.left.fromSpecResidueField x ≫ C₀.hom))
    let i₀ : Z₀ ⟶ C₀ := Over.homMk (C₀.left.fromSpecResidueField x)
    ∃ (E : WeilConjectures.NativeL2.WeilModule D ell Z₀)
      (hE : IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicAlgClRingObj ell)
          (D.geometricFiber Z₀).left) E.carrier),
      Simple (⟨E, hE⟩ : WeilConjectures.condensedConstructibleWeilSheaves
        (Profinite.padicAlgClRingObj ell) (D.geometricFrobenius Z₀).hom) ∧
      Nonempty (P.obj.obj ≅
        (DerivedCategory.singleFunctor _ 0).obj
          (WeilConjectures.NativeL2.middleWeilImage D ell i₀ E)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedCurvePerverseStatement
