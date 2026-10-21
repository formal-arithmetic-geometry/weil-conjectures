module

public import Sheaf.AlgebraicGeometry.FieldActionGeometricTransportData

/-! # Normalized field-action transport interfaces

Source: Bhatt--Scholze Example 4.1.10, Definition 6.8.3 and Proposition 6.8.4;
main-20261015 direct-images paragraph (3), normalized ordinary derived sections
(blueprint: def-sfb-field-action-coefficient-transport-data).

## Main definitions

* `CoefficientTransport`: normalized coefficient restriction, its field and forgotten
  naturality squares, and equality of the two specified coefficient projections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FieldActionTransport

open CondensedGalois

variable (k ks : Type u) [Field k] [Field ks] [Algebra k ks] [IsSepClosure k ks]

section CoefficientGeometry
variable (X : Scheme.{u}) (a : X ⟶ Spec (.of k))
  {R R' : Coefficients.{u}} (φ : R ⟶ R')
  [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)]
  [CategoryTheory.CondensedBar.ActionAbelian R' (ks ≃ₐ[k] ks)]
  [ForgetData k ks R] [ForgetData k ks R']
  (e : FieldData k ks R) (e' : FieldData k ks R')
  (c : ScalarTransport k ks φ e e')
  (d : OrdinaryData k ks X a R) (d' : OrdinaryData k ks X a R')
  [PointAdjunctionData R (geometricScheme.{u} k ks X a)]
  [PointAdjunctionData R' (geometricScheme.{u} k ks X a)]
  [PreservesFiniteLimits (fieldFunctor k ks e)]
  [PreservesFiniteColimits (fieldFunctor k ks e)]
  [PreservesFiniteLimits (fieldFunctor k ks e')]
  [PreservesFiniteColimits (fieldFunctor k ks e')]
  [PreservesFiniteLimits
    (CondensedRing.upperStar.{u} R.X (geometricProjection.{u} k ks X a))]
  [PreservesFiniteColimits
    (CondensedRing.upperStar.{u} R.X (geometricProjection.{u} k ks X a))]
  [PreservesFiniteLimits
    (CondensedRing.upperStar.{u} R'.X (geometricProjection.{u} k ks X a))]
  [PreservesFiniteColimits
    (CondensedRing.upperStar.{u} R'.X (geometricProjection.{u} k ks X a))]
  [Functor.Additive.{u + 1, u + 2, u + 1, u + 2} (CondensedRing.lowerStar.{u} R.X a)]
  [Functor.Additive.{u + 1, u + 2, u + 1, u + 2} (CondensedRing.lowerStar.{u} R'.X a)]
  [Functor.Additive.{u + 1, u + 2, u + 1, u + 2}
    (CondensedRing.lowerStar.{u} R.X (geometricProjection.{u} k ks X a))]
  [Functor.Additive.{u + 1, u + 2, u + 1, u + 2}
    (CondensedRing.lowerStar.{u} R'.X (geometricProjection.{u} k ks X a))]
  (g : GeometricTransport k ks X a R e d) (g' : GeometricTransport k ks X a R' e' d')

/-- Equality of the three specified coefficient projections: the geometric field map,
its scalar-adjunction transpose beta in the action category, and its forgotten
counit-adjoint point projection. All comparisons are fixed by ordinary section maps,
canonical derived units and the scalar/geometric adjunction squares.
Source: field-action node, coefficient projection and forgotten projection paragraphs
(blueprint: def-sfb-field-action-coefficient-transport-data). -/
structure CoefficientTransport where
  /-- Canonical scalar/geometric squares for the structure morphism. -/
  arithmetic : MorphismScalar φ a
  /-- Canonical scalar/geometric squares for geometric base change. -/
  geometric : MorphismScalar φ (geometricProjection.{u} k ks X a)
  /-- The scalar-restriction comparison for the actual geometric section functors. -/
  restriction : CoefficientComparison (restrictX φ X) c.restriction.functor
    d.geometric.functor d'.geometric.functor
  /-- On all sections this restriction comparison is the identity. -/
  sections : ∀ (M : Modules R'.toMon X) (P : Profinite.{u})
    (x : Profinite.CondensedAction.sectionModule R.toMon
      (d.geometric.functor.obj ((restrictX φ X).obj M)).module P),
    ((d'.geometric.sections.hom.app M).app (op P)).hom
      (((c.restriction.underlying.hom.app (d'.geometric.functor.obj M)).hom.hom.app
        (op P)).hom
        ((((restriction.ordinary.hom.app M).val).hom.hom.app (op P)).hom x)) =
      ((d.geometric.sections.hom.app ((restrictX φ X).obj M)).app (op P)).hom x
  /-- Field and geometric derived-object identifications commute with coefficient
  restriction. Naturality then gives every input morphism M to Res M'. -/
  restriction_square : ∀ M : DerivedCategory (Modules R'.toMon X),
    g.derived.hom.app ((restrictX φ X).mapDerivedCategory.obj M) ≫
        restriction.derived.hom.app M =
      (fieldFunctor k ks e).mapDerivedCategory.map (arithmetic.direct.derived.hom.app M) ≫
        c.derived.restriction.hom.app ((push R' a).obj M) ≫
          c.restriction.functor.mapDerivedCategory.map (g'.derived.hom.app M)
  /-- The field-side scalar transpose is also the canonical counit-adjoint projection. -/
  arithmetic_counit : ∀ M : DerivedCategory (Modules R.toMon X),
    scalarProjection (scalarDerivedAdjunction φ X)
      (scalarDerivedAdjunction φ (Spec (.of k))) (push R a) (push R' a)
      arithmetic.direct.derived M =
    ((geometricAdjunction R' a).homEquiv _ _)
      (arithmetic.pullExtension.extension.hom.app ((push R a).obj M) ≫
        (derivedExtend φ X).map ((geometricAdjunction R a).counit.app M))
  /-- Applying the same field equivalence identifies the canonical coefficient
  projection with exactly beta, the scalar-adjunction transpose defined in the node. -/
  projection : ∀ M : DerivedCategory (Modules R.toMon X),
    (fieldFunctor k ks e').mapDerivedCategory.map
      (scalarProjection (scalarDerivedAdjunction φ X)
        (scalarDerivedAdjunction φ (Spec (.of k))) (push R a) (push R' a)
        arithmetic.direct.derived M) ≫
          g'.derived.hom.app ((derivedExtend φ X).obj M) =
      c.derived.extension.hom.app ((push R a).obj M) ≫
        c.derivedExtension.map (g.derived.hom.app M) ≫
          scalarProjection (scalarDerivedAdjunction φ X) c.derivedAdjunction
            d.geometric.functor.rightDerivedFunctor d'.geometric.functor.rightDerivedFunctor
            restriction.derived M
  /-- The canonical point pullback/scalar exchange. -/
  pointScalars : PointScalar φ (geometricScheme.{u} k ks X a)
  /-- Forgetting beta gives precisely the point counit-adjoint projection, under the
  geometric pullback scalar exchange. No mere invertibility assertion replaces this. -/
  forgotten_projection : ∀ M : DerivedCategory (Modules R.toMon X),
    c.underlyingDerived.extension.inv.app (d.geometric.functor.rightDerivedFunctor.obj M) ≫
      CategoryTheory.CondensedBar.forgetAction.mapDerivedCategory.map
        (scalarProjection (scalarDerivedAdjunction φ X) c.derivedAdjunction
          d.geometric.functor.rightDerivedFunctor d'.geometric.functor.rightDerivedFunctor
          restriction.derived M) ≫
            g'.forgotten.hom.app ((derivedExtend φ X).obj M) =
      (condensedDerivedExtend φ).map (g.forgotten.hom.app M) ≫
        pointProjection φ (geometricScheme.{u} k ks X a) pointScalars
          ((pull R (geometricProjection.{u} k ks X a)).obj M) ≫
          (pointModules.{u} R'.toMon (geometricScheme.{u} k ks X a)).rightDerivedFunctor.map
            (geometric.pullExtension.extension.inv.app M)
  /-- Restriction commutes with actual point direct image by its canonical derived unit. -/
  pointRestriction : CoefficientComparison
    (restrictX φ (geometricScheme.{u} k ks X a)) (restrictCondensed φ)
    (pointModules.{u} R.toMon (geometricScheme.{u} k ks X a))
    (pointModules.{u} R'.toMon (geometricScheme.{u} k ks X a))
  /-- The ordinary point restriction comparison is the identity on abelian sheaves. -/
  point_identity : ∀ N : Modules R'.toMon (geometricScheme.{u} k ks X a),
    (pointRestriction.ordinary.hom.app N).hom = 𝟙 _
  /-- The forgotten object identification is also natural in coefficient restriction. -/
  forgotten_restriction : ∀ M : DerivedCategory (Modules R'.toMon X),
    CategoryTheory.CondensedBar.forgetAction.mapDerivedCategory.map
        (restriction.derived.hom.app M) ≫
      c.underlyingDerived.restriction.hom.app (d'.geometric.functor.rightDerivedFunctor.obj M) ≫
        (restrictCondensed φ).mapDerivedCategory.map (g'.forgotten.hom.app M) =
      g.forgotten.hom.app ((restrictX φ X).mapDerivedCategory.obj M) ≫
        (pointModules.{u} R.toMon (geometricScheme.{u} k ks X a)).rightDerivedFunctor.map
          (geometric.pullRestriction.extension.inv.app M) ≫
            pointRestriction.derived.hom.app ((pull R' (geometricProjection.{u} k ks X a)).obj M)
  /-- Canonical coefficient restriction comparisons also preserve the shifts. -/
  restriction_shift : NatTrans.CommShift restriction.derived.hom ℤ

end CoefficientGeometry



end AlgebraicGeometry.ProEtale.FieldActionTransport
