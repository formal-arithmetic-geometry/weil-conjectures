/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PointTateFiberCanonicalComparisons

/-! # Derived coordinates of the canonical point Tate comparisons

Source: coefficient comparison lemma, steps 4--5.
(blueprint: lem-pur-point-tate-derived-comparison-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] AlgebraicGeometry.Scheme.residueLisseAlgebraHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings TensorProduct
namespace WeilConjectures.PointTateFiber

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]


/-- The canonical comparison squares commute with the specified exact-single and
size-descent identifications. These equations involve the constructed maps and no
choice of a root generator.

Source: coefficient comparison lemma, steps 4--5; the normalization clauses of
pointSectionsScalarExtension and pointRationalFibreScalar_existsUnique.
(blueprint: lem-pur-point-tate-derived-comparison-coordinates).

Proof: expand rationalLineNormalization and pointRationalNormalization. Their
initial composites are precisely rationalSizeNormalization. On a degree-zero
integral line the remaining pointFibreRationalDownIso is the derived natural
isomorphism of the normalized coefficient tensor transport. Compatibility of
mapDerivedCategoryNatIso with single objects, and the composition formula for
mapDerivedCategorySingleFunctor, identify it with down.map(rawRationalSingle),
the down/single comparison, and single.map of the tensor transport, in that order.
For the completed square expand completedSectionsComparison and
completedLineComparison. Substitute the definition of pointSectionsScalarExtensionIso:
its inverse is the derived sections-tensor map followed by sections of the
completion comparison. The latter cancels its inverse in completedLineComparison.
Naturality of the exact-single comparisons moves the ordinary line isomorphism
through sections. The result is single.map of pointSectionsTensor followed by
sections of canonicalSheaf, which is single.map canonicalIntegral.
For the rational point square apply the defining normalized equation of
pointRationalFibreScalar_existsUnique on the integral signed line. Naturality of
the size-descent comparisons moves the fibre of integralLineComparison through
pointIntegralRationalNormalization. Insert the rational scalar extension object
equality occurring in rationalLineComparison; transport cancels with the same
object equality in the defining scalar comparison. Rationalize the completed
square just proved. The localization-tensor associator is the specified
pointTensorRationalization, so its inverse followed by rationalization of
canonicalIntegral is exactly canonicalRational. Finally cancel the inverse scalar
comparison and insert the exact-single comparisons. This gives the displayed
point equation, retaining the recorded lift/tensor and size-descent maps. -/
theorem canonicalDerivedCoordinates (hl : l ≠ D.p) :
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (m : ℤ),
      (rationalLineNormalization D l F hl m).hom =
        (rationalSizeNormalization D l F hl m).hom ≫
          (Functor.mapDerivedCategory.{u + 1, u + 2, u + 1, u + 1, u + 2, u + 2}
            (pointFibreCoefficientDown F)).map
            (rawRationalSingle D l F m).hom ≫
          ((pointFibreCoefficientDown F).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
          (DerivedCategory.singleFunctor _ 0).map
            ((pointFibreRationalDown_existsUnique D l F).exists.choose.hom.app
              (integralTwistLine l F (Spec (.of D.k)) m))) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (L : Type u) [Field L] [Algebra (Padic l) L]
        [FiniteDimensional (Padic l) L] (ι : F →ₐ[Padic l] L) (m : ℤ),
      (DerivedCategory.singleFunctor _ 0).map
          (canonicalIntegral D l hl F L ι m).hom =
        completedSectionsComparison D l F hl L ι m (canonicalSheaf D l hl)) ∧
    (∀ (F : Type u) [Field F] [Algebra (Padic l) F]
        [FiniteDimensional (Padic l) F] (L : Type u) [Field L] [Algebra (Padic l) L]
        [FiniteDimensional (Padic l) L] (ι : F →ₐ[Padic l] L) (m : ℤ),
      letI := frobeniusPointPrimeInvertible D l hl
      (Functor.mapDerivedCategory.{u, u + 2, u, u + 1, u + 1, u + 2}
        (ModuleCat.uliftFunctor.{u + 1, u} L)).map
          (rationalPointComparison D l F hl L ι m (canonicalSheaf D l hl)).hom.hom ≫
        (rationalLineNormalization D l L hl m).hom =
      (pointFibreTensorLiftIso l F L ι).hom.app
          ((pointRationalFibre D l hl F).obj
            (sfRationalTwistingCoefficient l F (Spec (.of D.k)) m)).obj ≫
        (pointCoefficientFieldDerivedTensor l F L ι).map
          (rationalLineNormalization D l F hl m).hom ≫
        ((ModuleCat.extendScalars ι.toRingHom).mapDerivedCategorySingleFunctor 0).hom.app
          (rational D l F m) ≫
        (DerivedCategory.singleFunctor _ 0).map (canonicalRational D l hl F L ι m).hom) := by sorry

end WeilConjectures.PointTateFiber
