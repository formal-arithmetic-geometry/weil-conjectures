/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.TransportCompact
public import WeilConjectures.SixFunctors.CondensedFrobeniusComparisonCoherence

/-! # Strict condensed Weil data and their specified scheme form

Source: latest blueprint def-pur-tate-datum, strict datum and u_K formula.
This repairs the recorded interface's missing all-coefficient u_K: its existing uK
is only for UniformPurityTateDatum at finite coefficients, whereas its condensed
strict datum has no scheme-form declaration.
(blueprint: def-pur-tate-datum).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport

namespace WeilConjectures.Purity.Condensed
variable (D : WeilConjectures.FiniteFieldDatum.{u})

/-- The recorded kappa on total-derived pullback coordinates. Both outer arrows
are the specified comparison of exact pullback with its total left derivation.
Source: def-pur-tate-datum, u = phi kappa; canonical comparison paragraph of the
item proof (blueprint: def-pur-tate-datum). -/
def kappa (Λ : ScalarSixRing.{u}) (T₀ : Over (Spec (.of D.k₀))) :
    actualPull Λ.X (D.puritySchemeFrobenius T₀) ≅
      actualPull Λ.X (D.purityGaloisMap T₀) :=
  leftDerivedUpperStarIsoMapDerivedCategory Λ.X (D.puritySchemeFrobenius T₀) ≪≫
    condensedFrobeniusComparison D Λ T₀ ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory Λ.X (D.purityGaloisMap T₀)).symm

/-- The scheme-form vertical map, with the specified kappa, for any induced datum.
Source: def-pur-tate-datum, scheme-Frobenius form
(blueprint: def-pur-tate-datum). -/
def uDatum (Λ : ScalarSixRing.{u}) (T₀ : Over (Spec (.of D.k₀)))
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X
      (D.purityFrobeniusFiber T₀).left))
    (phi : (actualPull Λ.X (D.purityGaloisMap T₀)).obj K ⟶ K) :=
  (kappa D Λ T₀).hom.app K ≫ phi

/-- A strict datum in the actual condensed finite-Tor category, independently of
any finite coefficient setting or stable lattice. Source: def-pur-tate-datum,
first displayed isomorphism (blueprint: def-pur-tate-datum). -/
structure StrictDatum (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (Λ : ScalarSixRing.{u})
    (_hΛ : IsPurityFrobeniusCoefficient ell E Λ)
    (T₀ : Over (Spec (.of D.k₀))) where
  K : ConstantModelConstructibleFiniteTor Λ.X (D.purityFrobeniusFiber T₀).left
  phi : (actualPull Λ.X (D.purityGaloisMap T₀)).obj K.obj ≅ K.obj

/-- The scheme-Frobenius form of the same strict datum, with the specified kappa.
Source: def-pur-tate-datum, u_K = phi_K kappa_K (blueprint: def-pur-tate-datum). -/
def StrictDatum.uK {ell : ℕ} [Fact ell.Prime]
    {E : PadicAlgCl.FiniteIntermediateField ell} {Λ : ScalarSixRing.{u}}
    {hΛ : IsPurityFrobeniusCoefficient ell E Λ} {T₀ : Over (Spec (.of D.k₀))}
    (W : StrictDatum D ell E Λ hΛ T₀) :=
  uDatum D Λ T₀ W.K.obj W.phi.hom

end WeilConjectures.Purity.Condensed
