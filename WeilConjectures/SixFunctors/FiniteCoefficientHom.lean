/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteHomArrow
public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom

import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomEtaleIso
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomDomainCalculus
import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescent
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomIntrinsicTensorComposition
import all WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
import all WeilConjectures.SixFunctors.Finite.Hom.FiniteHomSiteEquationDescent
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomComparisonTower

/-! # Constructible internal Hom and finite coefficient change

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-tower/thm-coef-finite-hom.md
(blueprint: thm-coef-finite-hom).

The indices `n`, `m`, `r` denote the positive exponents `n + 1`, `m + 1`, `r + 1`.
The finite coefficient constructions are the published evaluation transposes on the
ordinary derived categories of the two small sites. The pro-etale presentation uses
modules over the constant ring sheaf, without derived completion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u a b c d e f

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

private theorem scalarTensorSquare
    {A : Type a} {B : Type b} {D : Type c}
    [Category.{d} A] [Category.{e} B] [Category.{f} D]
    (T : A × A ⥤ A) (T' : B × B ⥤ B) (T'' : D × D ⥤ D)
    (F : A ⥤ B) (G : B ⥤ D) (J : A ⥤ D) (α : F ⋙ G ≅ J)
    (μ : T ⋙ F ≅ F.prod F ⋙ T') (ν : T' ⋙ G ≅ G.prod G ⋙ T'')
    (ξ : T ⋙ J ≅ J.prod J ⋙ T'')
    {I : A} {I' : B} {I'' : D} {U : Type e} {V W : Type f}
    (e₀ : U) (e₁ : V) (e₂ : W)
    (h : FiniteHomDomainScalarComposition T T' T'' I I' I'' F G J α
      (fun P Q ↦ μ.app (P, Q)) (fun P Q ↦ ν.app (P, Q))
      (fun P Q ↦ ξ.app (P, Q)) e₀ e₁ e₂) :
    ∀ P Q : A,
      G.map (μ.hom.app (P, Q)) ≫ ν.hom.app (F.obj P, F.obj Q) ≫
          T''.map (Prod.mkHom (α.hom.app P) (α.hom.app Q)) =
        α.hom.app (T.obj (P, Q)) ≫ ξ.hom.app (P, Q) := by
  obtain ⟨δ, δ', δ'', ε, ε', ε'', hδ, hδ', hδ'', _, _, _, hc, _⟩ := h
  intro P Q
  have hh := hc P Q
  rw [eq_of_heq (hδ P Q), eq_of_heq (hδ' _ _), eq_of_heq (hδ'' P Q)] at hh
  exact hh.symm

end WeilConjectures
