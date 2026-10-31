/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.PointRealizationStandardCohomology
public import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldDerivedScalarTower

/-! # The Shrink coefficient model in the common-stage point cohomology square

Source: Bhatt--Scholze 6.8.14(2) and the point coefficient convention, order 1509
(blueprint: lem-a1-point-common-scalar-cohomology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
namespace WeilConjectures

attribute [local instance 2000] HasDerivedCategory.ofIsGrothendieckAbelian

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion)

/-- Rewrite the common-stage point square over the small coefficient field, rather
than the actual subfield of Ω. This is only the common-stage scalar square: it does
not assert finite scalar compatibility, constructible heart exactness, or the
existence of the point cohomology data supplied as its input.
Source: Bhatt--Scholze 6.8.14(2), point coefficient convention, order 1509
(blueprint: lem-a1-point-common-scalar-cohomology).

Proof: let a be the Shrink algebra equivalence from Coefficient(E) to E.val, and b
its inclusion into Ω. The normalized point-stage isomorphism identifies inclusion(E)
followed by the common point realization with the stage realization followed by
extension along b. The stage realization is the finite point realization followed
by extension along a. Compose the inverse tensor-tower isomorphism for a,b with
the inverse normalized stage isomorphism. Its components are precisely the ones
below: the stage normalization is the identity under the recorded object equality
for pointQbarFibre. This also proves naturality of those specified components.
Write T_a, T_b, T_c for the derived scalar functors, with c = b.comp a, and
θ : T_a ⋙ T_b ≅ T_c for fieldScalarTower a b. Its termwise tensor associator
commutes with the exact good-truncation maps: applying it to cycles, boundaries
and their quotient gives
θ(H^j M) ≫ δ_c(M) = T_b(δ_a(M)) ≫ δ_b(T_a M) ≫ H^j(θ(M)).
The shift factors commute by fieldScalarTower_commShift. These formulas extend
from representing complexes through the fully faithful localization whiskering.
The input's stage_transport identifies stage cohomology with T_a(δ_finite)
followed by δ_a. In common_square use the normalized stage comparison γ, then
postcompose its equation with H^j(θ(F K)). Naturality of θ at δ_finite rewrites
its other occurrence as θ(F(H^j K)); the displayed field equation replaces the
two successive field comparisons by δ_c. The resulting equation is exactly
PointRealizationCohomologySquare for γ followed by F-whiskering of θ, which is
β.symm. Use pointExactDerivedComparison for T_c; its shift is the recorded
termwise derived shift. All fields, including E equal to an earlier stage, are
allowed; no faithful transition hypothesis is required. -/
theorem pointCommonScalarCohomology
    (P : PointRealizationStandardCohomologyData D l hl Ω) (E : Index l Ω) :
    ∃ (t : PointRealizationComparison
        (DerivedCategory.TStructure.t (C := ModuleCat.{u} (Coefficient.{u} l Ω E)))
        (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω))
        (DerivedCategory.fieldDerivedScalarExtension
          (E.val.subtype.comp (Shrink.algEquiv (Padic l) E.val).toRingHom)))
      (β : pointRealizationAmbient D l hl (Coefficient.{u} l Ω E) ⋙
          DerivedCategory.fieldDerivedScalarExtension
            (E.val.subtype.comp (Shrink.algEquiv (Padic l) E.val).toRingHom) ≅
        inclusion (l := l) (Ω := Ω) (Y := Spec (.of D.k)) E ⋙
          pointRealizationCommonAmbient D l hl Ω),
      t.commShift = (inferInstance :
        (DerivedCategory.fieldDerivedScalarExtension
          (E.val.subtype.comp (Shrink.algEquiv (Padic l) E.val).toRingHom)).CommShift ℤ) ∧
      (∀ K : Stage l Ω (Spec (.of D.k)) E,
        β.app K =
          (DerivedCategory.fieldScalarTower
            (Shrink.algEquiv (Padic l) E.val).toRingHom E.val.subtype).symm.app
              (((pointRationalFibre D l hl (Coefficient.{u} l Ω E)).obj K).obj) ≪≫
            ((DerivedCategory.pointFdQbarRealization l Ω).mapIso
              (eqToIso ((pointQbarFibre_existsUnique D l hl Ω).exists.choose_spec.1
                ((inclusion (l := l) (Ω := Ω) (Y := Spec (.of D.k)) E).obj K)))).symm) ∧
      PointRealizationCohomologySquare
        (P.finite (Coefficient.{u} l Ω E)) P.common (P.inclusion E) t β.symm := by
  sorry

end WeilConjectures
