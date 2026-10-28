/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.LisseTowerEtaleDescentData
public import Sheaf.Paper.ProEtaleLisseOrigin

/-! # Cohomology of the inverse finite scalar realization

Source: Stacks Project, Modules on Sites, exactness of inverse image and constants
(Tags 03DC and 093J); proetale.tex, locally constant comparison (Tag 099Y).
(blueprint: new-lem-weil-pbc-lisse-inverse-realization-cohomology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow lisseTowerFixedRealization

/-- The inverse fixed realization of the actual pullback has the bounds of its local
algebraic models and lisse pro-etale cohomology. This is a cohomology assertion only;
no etale derived model or comparison of derived objects is asserted.

Source: Stacks Project, proetale.tex, lemma-compare-locally-constant (Tag 099Y),
combined with exact inverse image and constants (Tags 03DC and 093J) and the
finite scalar equivalence of def-weil-pbc-lisse-tower-etale-descent-data.
(blueprint: new-lem-weil-pbc-lisse-inverse-realization-cohomology).

Proof: put F = lisseTowerFixedRealization (U.hom ≫ g) d n. Its inverse is the exact
finite scalar sheaf equivalence. Restrict its inverse image of the actual pullback
along each arrow of the covering sieve in hmodels. Pullback composition and the
canonical constant realization identify the restriction with the constant complex E.
Exactness commutes with H^q, so its cohomology restricts to the constant sheaf H^q(E).
Outside the supplied window these sheaves are zero; conservativity on a covering
sieve reflects zero, which proves the bounds. Since the quotient ring is finite,
the finitely generated modules H^q(E) are finite sets. The same restricted
cohomology identifications give local constancy and finite geometric stalks, hence
the asserted lisse predicate. To pass from a covering sieve to the covering family
used in that predicate, choose covering arrows through the points and refine over
affine opens; the definition of ProEt.topology supplies the required fpqc covering
condition. For the empty scheme zero detection uses the empty covering sieve, and
there are no geometric stalks to check. No compatibility of the chosen marking
isomorphisms on overlaps is needed for these cohomology properties. -/
theorem lisse_finite_level_inverse_realization_cohomology
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (n : ℕ)
    (N : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (hbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj E))
    (hfinite : ∀ q : ℤ, Module.Finite (lisseTowerEtaleRing d n)
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) q).obj E))
    (hmodels : ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
          (adicTowerPullback (W.hom ≫ g)
            ((pbcAdicRings X d).obj (op n))).obj N)) :
    let K := (lisseTowerFixedRealization (U.hom ≫ g) d n).asEquivalence.inverse.obj
      ((adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj N)
    (∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) ∧
      (∀ q : ℤ, IsLisseProEtaleFixedModuleSheaf U.left (lisseTowerEtaleRing d n)
        ((DerivedCategory.homologyFunctor _ q).obj K)) := by sorry

end AlgebraicGeometry.Scheme
