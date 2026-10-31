/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations
public import WeilConjectures.CategoryTheory.Site.SitePerfectScalarHomComparison
public import WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
@[expose] public section
set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
universe u
open CategoryTheory Opposite AlgebraicGeometry WeilConjectures
open AlgebraicGeometry.Scheme
namespace WeilConjectures
/-- The normalized evaluation square for the finite quotient scalar comparison.
The comparison is constrained by the componentwise ordinary-extension identification
and by equality of the two derived counits, so the conclusion is invariantly attached
to the specified quotient model.
Source: Stacks 07A4 and 08JJ; (blueprint: lem-sf-finite-quotient-hom-model-comparison-evaluation).

Proof: transpose both sides with the target closed adjunction. Use naturality of the
counit-normalized comparison, the K-flat tensor comparison squares in the source and
target models, and the finite quotient evaluation formula. Both transposes become the
same scalar extension of source evaluation; injectivity of the adjunction transpose
then gives the displayed equality for arbitrary P and Q. -/
theorem finiteQuotient_homModel_comparison_evaluation
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (m n : ℕ) (h : m ≤ n)
    [EssentiallySmall.{u + 1} W.ProEt]
    (A : SitePerfectScalarHomData.{u + 1, u, u, u + 2} (ProEt.topology W)
      (coefficientFiniteQuotient l E W h))
    (e : SheafOfModules.DerivedChangeOfRingsCochainModel.T.{u + 1, u, u + 1, u + 2, u + 2}
      (SitePerfectScalarHomData.scalar.{u + 1, u, u, u + 2} A) ≅
        coefficientFiniteQuotientDerived l E W h)
    (o : (SitePerfectScalarHomData.scalar.{u + 1, u, u, u + 2} A).E ≅
      coefficientFiniteQuotientExtension l E W h)
    (ho : ∀ M, o.hom.app M =
      eqToHom (((SitePerfectScalarHomData.scalar A).obj_eq M).trans
        (coefficientFiniteQuotientExtension_obj l E W h M).symm))
    (hnorm :
      letI : (coefficientFiniteQuotientExtension l E W h).PreservesZeroMorphisms := by
        letI : (coefficientFiniteQuotientExtension l E W h).Additive :=
          coefficientFiniteQuotientExtensionAdditive l E W h
        exact CategoryTheory.Functor.preservesZeroMorphisms_of_additive _
      ∀ P : CochainComplex (normalizedDVRModules l E W n) ℤ,
      e.hom.app (DerivedCategory.Q.obj P) ≫
          (CategoryTheory.derivedCochainCounit
            (coefficientFiniteQuotientExtension l E W h)
            (coefficientFiniteQuotientDerived l E W h)
            (coefficientFiniteQuotientCounit l E W h)).app P =
        (SitePerfectScalarHomData.scalar A).ε.app P ≫
          DerivedCategory.Q.map
            (show ((SitePerfectScalarHomData.scalar A).E.mapHomologicalComplex (.up ℤ)).obj P ⟶
                ((coefficientFiniteQuotientExtension l E W h).mapHomologicalComplex
                  (.up ℤ)).obj P from
              { f := fun i => o.hom.app (P.X i)
                comm' := by
                  intro i j hij
                  change o.hom.app (P.X i) ≫
                      (coefficientFiniteQuotientExtension l E W h).map (P.d i j) =
                    (SitePerfectScalarHomData.scalar A).E.map (P.d i j) ≫
                      o.hom.app (P.X j)
                  exact (o.hom.naturality (P.d i j)).symm })) :
    ∀ P Q : normalizedDVRDerived l E W n,
      siteScalarHomComparison.{u + 1, u, u, u + 2} _ (coefficientFiniteQuotient l E W h) A P Q ≫
          (coefficientFiniteInternalHom l E W m).map
            (Prod.mkHom (e.inv.app P).op (e.hom.app Q)) =
        e.hom.app ((coefficientFiniteInternalHom l E W n).obj (op P, Q)) ≫
          finiteIntrinsicReductionHom l E W h P Q := by
  sorry
end WeilConjectures
