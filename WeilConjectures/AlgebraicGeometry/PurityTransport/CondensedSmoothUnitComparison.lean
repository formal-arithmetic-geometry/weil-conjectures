/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport

/-! # Evaluating ordinary condensed smooth purity at the unit

This is the unit-evaluation step of sk-cor-sp-all-coefficients, also for a relative map.
No Frobenius datum or native exceptional functor occurs in the statement.
(blueprint: lem-sf-condensed-smooth-unit-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- Evaluate the counit-compatible smooth purity isomorphism at the coefficient unit.
Source: sk-cor-sp-all-coefficients.proof.md, first paragraph
(blueprint: lem-sf-condensed-smooth-unit-comparison).
Proof: take the adjunction family of smooth_purity_transport. Its BrownComparison
compares the explicit smooth source with the supplied localizing right adjoint,
restricted to Dctf. Evaluate this comparison at the unit and forget the full-subcategory
membership proof. The inverse-image unit and tensor unitors give sourceUnit. Compose
the inverse Brown comparison with sourceUnit. -/
theorem condensed_smooth_unit_comparison (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (c : Coefficient ell) (s : SmoothDatum D)
    (hL : ∀ K, localizing ell c s.X.left K → localizing ell c s.Y.left
      ((rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification).obj K))
    (G : (localizing ell c s.Y.left).FullSubcategory ⥤
      (localizing ell c s.X.left).FullSubcategory)
    (b : localizingLowerShriek (c.obj ell) s.compactification hL ⊣ G)
    (hU : property ell c s.Y.left (unit ell c s.Y.left)) :
    Nonempty ((G.obj ((inclusion ell c s.Y.left).obj ⟨unit ell c s.Y.left, hU⟩)).obj ≅
      c.derivedLine ell s.X.left s.dim) := by
  obtain ⟨a, hBrown, _⟩ := smooth_purity_transport ell D hEll
  obtain ⟨hG, bctf, _, gamma, _, _⟩ := hBrown c s hL G b
  exact ⟨(property ell c s.X.left).ι.mapIso
      (gamma.app ⟨unit ell c s.Y.left, hU⟩).symm ≪≫
    sourceUnit ell c s.map s.dim⟩

end AlgebraicGeometry.ProEtale.PurityTransport
