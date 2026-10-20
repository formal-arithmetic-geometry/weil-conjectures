/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!
# Triangles for the external exchange and projection comparison

Source: blueprint, main-20261015, `lem-trf-ordinary-kunneth.proof.md`, displayed
comparison and Step 2, "Both sides of the comparison are exact in Q"
(blueprint: lem-trf-external-comparison-triangles).

The helpers name the source, target and actual three-factor comparison. Inverse image
is written as its left derived functor, canonically identified with termwise inverse
image by `leftDerivedUpperStarIsoMapDerivedCategory`. The exchange is transported along
this identification from the recorded exact-inverse-image exchange.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A]
  {k : Type u} [Field k] {X Y Z : Scheme.{u}}
  (f : X ⟶ Y) (b : Y ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))
  (c : Z ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))

/-- The source `Q ↦ p_Y^* Rf_* L ⊗ᴸ p'_Z{}^* Q`, on the bounded below category.
Source: blueprint, ordinary Kunneth proof, displayed comparison before Step 1
(blueprint: lem-trf-external-comparison-triangles). -/
noncomputable abbrev externalComparisonSource
    (L : DerivedCategoryModule A X) :=
  DerivedCategory.Plus.ι (C := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ⋙
    L((pullback.snd b c)^*[ModuleCat.{u + 1} A]) ⋙
      (derivedTensor (ModuleCat.{u + 1} A) (pullback b c)).obj
        (L((pullback.fst b c)^*[ModuleCat.{u + 1} A]).obj
          (R((f)_*[ModuleCat.{u + 1} A]).obj L))

/-- The target `Q ↦ Rh_*(p_X^* L ⊗ᴸ p_Z^* Q)`, valued in the unbounded category.
Source: blueprint, ordinary Kunneth proof, displayed comparison before Step 1
(blueprint: lem-trf-external-comparison-triangles). -/
noncomputable abbrev externalComparisonTarget
    (L : DerivedCategoryModule A X) :=
  DerivedCategory.Plus.ι (C := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ⋙
    L((pullback.snd (f ≫ b) c)^*[ModuleCat.{u + 1} A]) ⋙
      (derivedTensor (ModuleCat.{u + 1} A) (pullback (f ≫ b) c)).obj
        (L((pullback.fst (f ≫ b) c)^*[ModuleCat.{u + 1} A]).obj L) ⋙
      R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} A])

/-- Exchange for the product square, transported from exact inverse image to `Lu^*`.
Source: Stacks Tag 07A7 and blueprint, ordinary Kunneth proof, displayed comparison
(blueprint: lem-trf-external-comparison-triangles). -/
noncomputable def externalComparisonExchange
    (L : DerivedCategoryModule A X) :
    L((pullback.fst b c)^*[ModuleCat.{u + 1} A]).obj
        (R((f)_*[ModuleCat.{u + 1} A]).obj L) ⟶
      R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} A]).obj
        (L((pullback.fst (f ≫ b) c)^*[ModuleCat.{u + 1} A]).obj L) :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
      (pullback.fst b c)).hom.app _ ≫
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
      (CommSq.mk (pullback.mapOverBaseRight_fst f b c).symm)).app L ≫
    R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} A]).map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.fst (f ≫ b) c)).inv.app L)

/-- The specified comparison: exchange tensor identity, projection map, then
`Rh_*(1 ⊗ c_Q)`. The inverse of `leftDerivedUpperStarComp` is the descended module-linear
inverse-image composition map for `p_Z = h ≫ p'_Z` (Stacks Tag 03D8).
Source: blueprint, ordinary Kunneth proof, displayed comparison before Step 1
(blueprint: lem-trf-external-comparison-triangles). -/
noncomputable def externalComparisonMap
    (L : DerivedCategoryModule A X)
    (Q : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (externalComparisonSource A f b c L).obj Q ⟶
      (externalComparisonTarget A f b c L).obj Q :=
  ((derivedTensor (ModuleCat.{u + 1} A) (pullback b c)).map
    (externalComparisonExchange A f b c L)).app
      (L((pullback.snd b c)^*[ModuleCat.{u + 1} A]).obj Q.obj) ≫
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A)
      (pullback.mapOverBaseRight f b c)).app
        (L((pullback.fst (f ≫ b) c)^*[ModuleCat.{u + 1} A]).obj L)).app
          (L((pullback.snd b c)^*[ModuleCat.{u + 1} A]).obj Q.obj) ≫
    R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} A]).map
      (((derivedTensor (ModuleCat.{u + 1} A) (pullback (f ≫ b) c)).obj
        (L((pullback.fst (f ≫ b) c)^*[ModuleCat.{u + 1} A]).obj L)).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
            (pullback.mapOverBaseRight f b c) (pullback.snd b c)
            (pullback.snd (f ≫ b) c)
            (pullback.mapOverBaseRight_snd f b c).symm).inv.app Q.obj))

/-- For a bounded-flat-representable `L`, the actual external comparison is a natural
transformation between triangulated functors, commutes with the canonical shift by one,
and supplies all three components of a morphism of image distinguished triangles.
Source: blueprint, ordinary Kunneth proof, Step 2
(blueprint: lem-trf-external-comparison-triangles).

Proof plan:
1. Constant-coefficient inverse image is exact by
   `prop-weil-pbc-inverse-image-modules-exact`; its termwise derived functor is triangulated
   by `lem-weil-pbc-exact-functor-derived-factorization` and
   `lem-weil-pbc-exact-functor-derived-functor`.
2. K-injectives exist by `prop-pur-kinjective-resolutions-exist`. Apply
   `lem-pc-right-derived-functor-triangulated`, `lem-kun-derived-tensor-triangulated` and
   `lem-weil-pbc-triangulated-functor-composite` to the two displayed composites, and
   restrict their source to the strictly full triangulated subcategory D+.
3. Factor the actual comparison as exchange tensor identity, the projection map, and
   direct image of identity tensor the composition comparison.
4. The second-variable tensor shift multiplies first-degree-p summands by (-1)^p.
   A degree-zero map in the first variable commutes with this scalar. Descend this
   equality through `lem-weil-pbc-site-derived-tensor-descent` for the fixed exchange map.
5. `lem-weil-pbc-ringed-projection-mate-exact` gives naturality and shift compatibility
   of the projection map, whose counit mate agrees with the recorded projection map.
6. The module composition isomorphism of
   `lem-weil-pbc-inverse-image-composition-module-linear` is termwise, so commutes with
   shifts; tensoring and direct image preserve the equation.
7. Compose these equations by `lem-weil-pbc-commshift-nattrans-comp-whisker` to obtain
   s_G alpha[1] = alpha[1] s_F for this very composite.
8. Naturality gives the first two triangle squares. The third is
   F(w) s_F alpha[1] = F(w) alpha_at_shift s_G = alpha G(w) s_G.
   Both image triangles are distinguished by step 2; their components are exactly alpha.
No invertibility of alpha is used or asserted. -/
theorem externalComparison_triangles
    (L : DerivedCategoryModule A X)
    (_hL : ∃ (a b : ℤ)
      (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ),
      IsBoundedFlatComplex A a b P ∧ Nonempty (L ≅ DerivedCategory.Q.obj P)) :
    (externalComparisonSource A f b c L).IsTriangulated ∧
    (externalComparisonTarget A f b c L).IsTriangulated ∧
    ∃ α : externalComparisonSource A f b c L ⟶ externalComparisonTarget A f b c L,
      (∀ Q, α.app Q = externalComparisonMap A f b c L Q) ∧
      (∀ Q, α.app (Q⟦(1 : ℤ)⟧) ≫
          ((externalComparisonTarget A f b c L).commShiftIso (1 : ℤ)).hom.app Q =
        ((externalComparisonSource A f b c L).commShiftIso (1 : ℤ)).hom.app Q ≫
          (α.app Q)⟦(1 : ℤ)⟧') ∧
      (∀ (T : Triangle
          (DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))),
        T ∈ distTriang _ →
        (externalComparisonSource A f b c L).mapTriangle.obj T ∈ distTriang _ ∧
        (externalComparisonTarget A f b c L).mapTriangle.obj T ∈ distTriang _ ∧
        ∃ φ : (externalComparisonSource A f b c L).mapTriangle.obj T ⟶
            (externalComparisonTarget A f b c L).mapTriangle.obj T,
          φ.hom₁ = α.app T.obj₁ ∧ φ.hom₂ = α.app T.obj₂ ∧ φ.hom₃ = α.app T.obj₃) :=
  sorry

end AlgebraicGeometry.Etale
