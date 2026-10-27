module

public import Sheaf.AlgebraicGeometry.FieldActionCoefficientTransportData
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.Paper.SectionDerivedPushpullNormalization
import Sheaf.Paper.RingedCoefficientProjectionCocycle
import Sheaf.CategoryTheory.RingedDerivedCompositionCocycle
import Sheaf.Paper.SheafSliceDerivedComparison
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.Paper.InternalScalarPullbackNormalization
import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.Paper.RingedComparisonTensorAdjunction
import Sheaf.Paper.RingedProjectionFirstShift
import Sheaf.Paper.DerivedAdjunctionShift
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.Paper.ProjectionMateExact

/-! # Scalar projection mates for field geometric sections

Source: Bhatt--Scholze, Example 4.1.10; blueprint direct-images paragraph (3),
geometric/coefficient normalization; Stacks Tags 07A4, 07A6, 0D6E and 0B56
(blueprint: lem-sfb-field-scalar-projection-mate-coherence).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.FieldActionTransport

open CondensedGalois

/-- Reuse the existing additive direct image at the fixed internal module categories.
Source: blueprint direct-images paragraph (3), actual ordinary section functors
(blueprint: lem-sfb-field-scalar-projection-mate-coherence). -/
instance fieldScalarProjectionPushAdditive (A : Coefficients.{u}) {Y Z : Scheme.{u}}
    (f : Y ⟶ Z) :
    Functor.Additive.{u + 1, u + 2, u + 1, u + 2}
      (C := Modules A.toMon Y) (D := Modules A.toMon Z) (CondensedRing.lowerStar.{u} A.X f) :=
  coefficientPushAdditive A f

/-- The shift of condensed scalar extension is the canonical left-adjoint shift of
exact scalar restriction. Source: blueprint direct-images paragraph (3), shift clause
(blueprint: lem-sfb-field-scalar-projection-mate-coherence). -/
instance condensedScalarProjectionCommShift {A B : Coefficients.{u}} (f : A ⟶ B) :
    (condensedDerivedExtend f).CommShift ℤ :=
  (condensedScalarAdjunction f).leftAdjointCommShift ℤ

variable (k ks : Type u) [Field k] [Field ks] [Algebra k ks] [IsSepClosure k ks]
  (X : Scheme.{u}) (a : X ⟶ Spec (.of k))
  {R R' : Coefficients.{u}} (φ : R ⟶ R')
  [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)]
  [CategoryTheory.CondensedBar.ActionAbelian R' (ks ≃ₐ[k] ks)]
  [ForgetData k ks R] [ForgetData k ks R']
  (e : FieldData k ks R) (e' : FieldData k ks R')
  (c : ScalarTransport k ks φ e e')
  (d : OrdinaryData k ks X a R) (d' : OrdinaryData k ks X a R')
  [PointAdjunctionData R (geometricScheme.{u} k ks X a)]
  [PointAdjunctionData R' (geometricScheme.{u} k ks X a)]
  (g : GeometricTransport k ks X a R e d) (g' : GeometricTransport k ks X a R' e' d')

/-- The scalar transpose, geometric counit projection and forgotten point projection
are the same specified arrows, naturally in every unbounded input and every integer shift.
The given restriction comparisons are normalized by total-derived units and by identity
ordinary section maps; no flatness or exactness of scalar extension is assumed.
Source: Bhatt--Scholze Example 4.1.10; blueprint direct-images paragraph (3);
Stacks Tags 07A4, 07A6, 0D6E, 0B56
(blueprint: lem-sfb-field-scalar-projection-mate-coherence).

Proof plan (the nine steps of the node):
1. Internal scalar/pullback normalization gives the K-flat exchange without flatness.
   Ring-sheaf change of coefficients supplies its restriction mate. The internal and
   section-model adjunctions use the same ordinary tensor pullback and K-injective
   direct image, so the pre-derived-adjunction uniqueness identifies them.
2. Apply ringed-comparison/tensor-adjunction conjugacy to the coefficient square.
   Its counit equation and the K-flat scalar unit normalization fix both directions.
3. Transpose the field scalar map. Using conjugacy, naturality of the geometric counit
   and the scalar unit, its geometric adjunct is exchange followed by scalar extension
   of the counit. The two adjunction triangles give injectivity of transposition.
4. Transport through the field equivalences. The normalized derived-composition
   cocycle identifies the two restriction routes, so the transported map is beta.
5. Restrict to the free-orbit sheaf slices at the separable closure and its base change.
   The slice counit equation restricts the same adjunct and K-flat exchange.
6. Compose with the separably closed field presentation. Both geometric left adjoints
   are exact, so composition-adjunction normalization identifies their composite counit
   with the point counit. Transposition gives precisely the pointProjection below.
7. Internal/section scalar-adjunction comparison and ringed conjugacy give its R-linear
   form. Its adjunct is restriction exchange followed by scalar exchange and the scalar
   extension of the point counit: this is the projection mate with tensor factor R'.
8. Naturality of adjunction bijections supplies the three natural transformations.
   Normalized direct-image and coefficient-projection cocycles give restriction squares.
9. Derived-adjunction shift compatibility and the signed K-flat tensor exchanges give
   canonical shifts for every comparison. The first-input projection-shift lemma gives
   shifts in M as well as the scalar tensor argument. These equations supply exactly
   CoefficientTransport, with its prescribed restriction comparisons. -/
theorem field_scalar_projection_mate_coherence [CompactSpace X] [QuasiSeparatedSpace X]
    (arithmeticRestriction : CoefficientComparison.{u}
      (restrictX φ X) (restrictX φ (Spec (.of k)))
      (CondensedRing.lowerStar.{u} R.X a) (CondensedRing.lowerStar.{u} R'.X a))
    (arithmetic_identity : ∀ N : Modules R'.toMon X,
      (arithmeticRestriction.ordinary.hom.app N).hom = 𝟙 _)
    (restriction : CoefficientComparison.{u} (restrictX φ X) c.restriction.functor
      d.geometric.functor d'.geometric.functor)
    (section_identity : ∀ (N : Modules R'.toMon X) (P : Profinite.{u})
      (x : Profinite.CondensedAction.sectionModule R.toMon
        (d.geometric.functor.obj ((restrictX φ X).obj N)).module P),
      ((d'.geometric.sections.hom.app N).app (op P)).hom
        (((c.restriction.underlying.hom.app (d'.geometric.functor.obj N)).hom.hom.app
          (op P)).hom
          ((((restriction.ordinary.hom.app N).val).hom.hom.app (op P)).hom x)) =
        ((d.geometric.sections.hom.app ((restrictX φ X).obj N)).app (op P)).hom x) :
    ∃ t : CoefficientTransport.{u} k ks X a φ e e' c d d' g g',
      t.arithmetic.direct = arithmeticRestriction ∧ t.restriction = restriction ∧
      NatTrans.CommShift t.arithmetic.direct.derived.hom ℤ ∧
      NatTrans.CommShift t.geometric.direct.derived.hom ℤ ∧
      NatTrans.CommShift t.pointRestriction.derived.hom ℤ ∧
      NatTrans.CommShift t.arithmetic.pullExtension.extension.hom ℤ ∧
      NatTrans.CommShift t.geometric.pullExtension.extension.hom ℤ ∧
      NatTrans.CommShift t.pointScalars.square.extension.hom ℤ ∧
      ∃ (χ : push R a ⋙ derivedExtend φ (Spec (.of k)) ⟶ derivedExtend φ X ⋙ push R' a)
        (β : d.geometric.functor.rightDerivedFunctor ⋙ c.derivedExtension ⟶
          derivedExtend φ X ⋙ d'.geometric.functor.rightDerivedFunctor)
        (π : (pointModules.{u} R.toMon (geometricScheme.{u} k ks X a)).rightDerivedFunctor ⋙
          condensedDerivedExtend φ ⟶ derivedExtend φ (geometricScheme.{u} k ks X a) ⋙
            (pointModules.{u} R'.toMon (geometricScheme.{u} k ks X a)).rightDerivedFunctor),
        (∀ M : DerivedCategory (Modules R.toMon X),
          χ.app M = scalarProjection (scalarDerivedAdjunction φ X)
            (scalarDerivedAdjunction φ (Spec (.of k))) (push R a) (push R' a)
            arithmeticRestriction.derived M) ∧
        (∀ M : DerivedCategory (Modules R.toMon X),
          β.app M = scalarProjection (scalarDerivedAdjunction φ X) c.derivedAdjunction
            d.geometric.functor.rightDerivedFunctor d'.geometric.functor.rightDerivedFunctor
            restriction.derived M) ∧
        (∀ H : DerivedCategory (Modules R.toMon (geometricScheme.{u} k ks X a)),
          π.app H = pointProjection φ (geometricScheme.{u} k ks X a) t.pointScalars H) ∧
        NatTrans.CommShift χ ℤ ∧ NatTrans.CommShift β ℤ ∧ NatTrans.CommShift π ℤ ∧
        (∀ M : DerivedCategory (Modules R.toMon X),
          ((pointDerivedAdjunction (R := R)
            (Y := geometricScheme.{u} k ks X a)).homEquiv _ _).symm
              ((restrictCondensed φ).mapDerivedCategory.map
                (π.app ((pull R (geometricProjection.{u} k ks X a)).obj M)) ≫
                t.pointRestriction.derived.inv.app
                  ((derivedExtend φ (geometricScheme.{u} k ks X a)).obj
                    ((pull R (geometricProjection.{u} k ks X a)).obj M))) =
            t.pointScalars.square.restriction.hom.app
              ((condensedDerivedExtend φ).obj
                ((pointModules.{u} R.toMon (geometricScheme.{u} k ks X a)).rightDerivedFunctor.obj
                  ((pull R (geometricProjection.{u} k ks X a)).obj M))) ≫
              (restrictX φ (geometricScheme.{u} k ks X a)).mapDerivedCategory.map
                (t.pointScalars.square.extension.hom.app
                  ((pointModules.{u} R.toMon
                    (geometricScheme.{u} k ks X a)).rightDerivedFunctor.obj
                    ((pull R (geometricProjection.{u} k ks X a)).obj M)) ≫
                  (derivedExtend φ (geometricScheme.{u} k ks X a)).map
                    ((pointDerivedAdjunction (R := R)
                      (Y := geometricScheme.{u} k ks X a)).counit.app
                      ((pull R (geometricProjection.{u} k ks X a)).obj M)))) := by
  sorry

end AlgebraicGeometry.ProEtale.FieldActionTransport
