/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Integral compact comparison on a smooth geometric curve

Source: latest blueprint, lem-a1-affine-hc0.proof.md, first paragraph and final
flat scalar extension. This statement contains no affine or support-vanishing hypothesis.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

attribute [local instance] IsAlgClosure.isAlgClosed

/-- Integral model, completeness of its actual compact image, and the flat comparison
on cohomology. This also applies to proper curves; no cohomological vanishing is claimed.

Source: latest blueprint lem-a1-affine-hc0.proof.md, paragraph 1 and final sentence
(blueprint: lem-a1-lattice-compact-comparison).

Proof: put C_0 = U_0 and use the identity open in p-real-integral. Smoothness implies
normality. Choose a geometric point and its fundamental group; thm-lisse supplies the
coefficient correspondences needed by the integral-model theorem. Enlarge the finite
extension E and transport its finite free integral sheaf to the continuous integer
coefficient ring of DerivedNakayama. The inclusion into Qbar defines b and its scalar
extension identifies L with F. A one-stratum finite free local presentation is
constructible and the integral criterion supplies finite Tor amplitude. The algebraically
closed base has finite ell-cohomological dimension. By ctf six-functor stability the
actual compact image belongs to Dbc on the point. The integral criterion there makes
that image derived complete. The prescribed scalar-six compact comparison and the
model isomorphism identify its derived extension by b with the compact image of F.
The map from integers to E is a localization, and E to Qbar is flat field extension;
thus b is flat. Apply the flat single-factor tensor cohomology comparison, followed
by exact geometric evaluation, to obtain the displayed comparison for each degree.
All these constructions concern the actual compactification c, using its canonical
comparison with the compactification used by the stability and scalar-six theorems. -/
theorem exists_curveLatticeCompactComparison
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (U₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
    [Smooth U₀.hom] [Nonempty U₀.left]
    (hDim : U₀.left.IsPureDimension 1)
    (hConnected : ConnectedSpace (D.geometricFiber U₀).left)
    (F : Mod (Sheaf (Scheme.ProEt.topology (D.geometricFiber U₀).left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) (D.geometricFiber U₀).left))
    (hF : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) F)
    (c : Compactification (D.geometricFiber U₀).hom) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra (Padic ell) E)
      (_ : FiniteDimensional (Padic ell) E)
      (b : DerivedNakayama.integerRing ell E ⟶ Profinite.padicAlgClRingObj ell)
      (_ : IsMonHom b)
      (L : AdicCompletion.Modules ell E (D.geometricFiber U₀).left),
      CondensedRing.LocallyFree (AdicCompletion.ring ell E (D.geometricFiber U₀).left) L ∧
      Nonempty ((Mod.extendScalars (coefficientMap b
        (D.geometricFiber U₀).left)).obj L ≅ F) ∧
      AlgebraicGeometry.ProEtale.IsDerivedComplete ell E (Spec (.of D.k))
        ((CondensedRing.rightDerivedLowerShriekOfCompactification
          (DerivedNakayama.integerRing ell E) c).obj
            ((DerivedCategory.singleFunctor _ 0).obj L)) ∧
      ∀ q : ℤ, Nonempty
        (((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PadicAlgCl ell)) q).obj
          ((condensedQbarCompactSections ell D.k c).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))) ≅
          (Mod.extendScalars (coefficientMap b (Spec (.of D.k))) ⋙
              CondensedQbarGeometricEvaluation.fieldFiber D.k ell).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((CondensedRing.rightDerivedLowerShriekOfCompactification
                (DerivedNakayama.integerRing ell E) c).obj
                  ((DerivedCategory.singleFunctor _ 0).obj L)))) := by
  sorry

end WeilConjectures
