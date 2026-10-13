/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.AffinePerfectModuleModel

import Sheaf.AlgebraicGeometry.OpenDerivedRestrictionComparison
import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective
import Sheaf.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport
import Sheaf.AlgebraicGeometry.SchemeIsoPerfectTransport

/-! # Perfect source models on affine opens

Source: Stacks Project, Tags 06Z0, 08EB and 08EJ.
(blueprint: lem-sc-affine-open-perfect-source-model).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The perfect source has a bounded finite-projective model under any realization
of the explicit affine sheafification functor.
Source: Stacks Project, Tag 08EB and Tag 06Z0.
(blueprint: lem-sc-affine-open-perfect-source-model).

Proof: Use open_derived_restriction_comparison to restrict the quasi-coherent source
and to choose localizations on the open subscheme. Intersect each strictly perfect
neighbourhood of E with U. Exact restriction preserves the bounds and finite-free
retract equations, so the restricted source is perfect. Transport it through
U.toScheme ≅ Spec Gamma(U,O_X); this preserves perfectness by transporting the same
open neighbourhoods, complexes, bounds and retract equations. Apply
perfect_iff_affine_bounded_projective to obtain P and its bounded finite-projective
terms. The affine_localized_site_derived_transport comparison identifies its tilde
model on the spectrum with Q of affinePerfectSheafification(P). The given natural
comparison at P then gives the required isomorphism. The empty open has zero section
ring, and the same argument applies to its zero category. No support or scalar
compatibility is asserted here. -/
theorem affine_open_perfect_source_model
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedQCohCategory X) (hE : X.IsPerfect E.obj)
    (U : X.Opens) (hU : IsAffineOpen U) :
    let A := ↑(X.sheaf.obj.obj (op U))
    letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
      HasDerivedCategory.standard (ModuleCat.{u} A)
    let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    ∀ (F : DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))),
      Nonempty (DerivedCategory.Q ⋙ F ≅
        (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q) →
      ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
        (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i)) ∧
        (∀ i : ℤ, Module.Finite A (P.X i)) ∧
        (∀ i : ℤ, Module.Projective A (P.X i)) ∧
        Nonempty (F.obj (DerivedCategory.Q.obj P) ≅ R.obj E.obj) := by sorry

end AlgebraicGeometry.Scheme
