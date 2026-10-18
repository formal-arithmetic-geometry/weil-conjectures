module

public import Mathlib.Algebra.Ring.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import Sheaf.AlgebraicGeometry.PullbackConstantModule
import Sheaf.CategoryTheory.Sites.InverseImageBilinearAdjunction
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Canonical derived étale inverse-image composition is monoidal.

(blueprint: lem-kun-derived-pullback-composition-monoidal)

This is the statement node `lem-kun-derived-pullback-composition-monoidal`.
The proof follows its seven recorded steps.  First choose K-flat representatives with
flat terms and use `def-kun-derived-tensor`,
`lem-weil-pbc-site-derived-tensor-descent`, `prop-weil-pbc-inverse-image-modules-exact`,
and `lem-weil-pbc-exact-functor-derived-factorization` to reduce to termwise maps.
Second, apply the bilinear-adjunction construction of
`lem-sfb-site-inverse-image-bilinear-adjunction` to the tensor comparison and use the
unit-normalized composition map of
`lem-weil-pbc-inverse-image-composition-module-linear`; the two composites agree on
each total-tensor summand with the same Koszul signs.  Third descend this equality
through the K-flat equivalence, using `lem-kun-inverse-image-monoidal` and
`def-kun-derived-tensor`, which gives the displayed tensor equation and its naturality.
Fourth apply the same calculation to the constant complex, using
`lem-kun-pullback-constant` and the unit normalization to obtain the constant-sheaf
comparison equation.  Fifth evaluate the comparison on the left and right unit
constraints from `lem-kun-tensor-unit`; the bilinear adjunction and the constant
comparison identify both displayed unit equations, and descent gives them for every
object.  Sixth, for three morphisms, use the fibre-product coherence in
`def-pc-fibre-product`, the pasted-unit identity of
`lem-cat-right-adjoint-composition`, and the uniqueness clause of
`lem-weil-pbc-inverse-image-composition` to identify the two normalized composites;
inverting gives the final associativity equation.  Finally all maps are canonical
natural transformations, so naturality passes through localization. -/
theorem canonicalDerivedPullbackCompositionMonoidal
    (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z T : Scheme.{u}}
    (uMap : Y ⟶ X) (vMap : Z ⟶ Y) (tMap : T ⟶ Z)
    (M N : DerivedCategoryModule Λ X) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) vMap uMap (vMap ≫ uMap) rfl).hom.app
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).obj N) ≫
      (vMap)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.map
        ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) uMap M N).hom) ≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) vMap
        ((uMap)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.obj M)
        ((uMap)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.obj N)).hom =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) (vMap ≫ uMap) M N).hom ≫
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) vMap uMap (vMap ≫ uMap) rfl).hom.app M ⊗ₘ
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) vMap uMap (vMap ≫ uMap) rfl).hom.app N) ∧
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) vMap uMap (vMap ≫ uMap) rfl).hom.app
        (𝟙_ _) ≫
      (vMap)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.map
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) uMap).hom ≫
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) vMap).hom =
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) (vMap ≫ uMap)).hom) ∧
    (∀ {V V' : Scheme.{u}} (w : V ⟶ V')
        (K : DerivedCategoryModule Λ V'),
      (w)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.map
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) V' K).hom =
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) w (𝟙_ _) K).hom ≫
          ((leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) w).hom ⊗ₘ
            𝟙 ((w)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.obj K)) ≫
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) V
            ((w)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.obj K)).hom) ∧
    (∀ {V V' : Scheme.{u}} (w : V ⟶ V')
        (K : DerivedCategoryModule Λ V'),
      (w)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.map
          (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) V' K).hom =
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) w K (𝟙_ _)).hom ≫
          (𝟙 ((w)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.obj K) ⊗ₘ
            (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) w).hom) ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) V
            ((w)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.obj K)).hom) ∧
    (∀ (K : DerivedCategoryModule Λ X),
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) tMap (vMap ≫ uMap)
          (tMap ≫ vMap ≫ uMap) (by simp)).hom.app K ≫
        (tMap)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) vMap uMap
            (vMap ≫ uMap) rfl).hom.app K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (tMap ≫ vMap) uMap
          (tMap ≫ vMap ≫ uMap) (by simp)).hom.app K ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) tMap vMap
          (tMap ≫ vMap) rfl).hom.app
          ((uMap)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctor.obj K))
    := by
  sorry

end AlgebraicGeometry.Etale

end
