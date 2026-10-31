/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleInverseImageCompositionModuleLinear
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinearCore
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.AlgebraicGeometry.ProjectionMateExact

/-!
# Triangles and the external direct-image comparison

Source: the current blueprint, `sec-six-functors/sk-lem-sf-kunneth-star/`
`lem-trf-ordinary-kunneth.proof.md`, displayed comparison and Step 2, "Both sides of the
comparison are exact in Q" (blueprint: lem-trf-external-comparison-triangles).

The derived pullbacks below are canonically identified with termwise exact inverse image by
`leftDerivedUpperStarIsoMapDerivedCategory`. The exchange is the recorded exact-inverse-image
mate transported along these identifications. The last comparison is the inverse of
`leftDerivedUpperStarComp`, hence the descent of the module inverse-image composition map.
All targets are ambient unbounded derived categories; only the variable factor is in D⁺.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A]
  {k : Type u} [Field k] {X Y Z : Scheme.{u}}
  (f : X ⟶ Y) (b : Y ⟶ Spec (.of k)) (c : Z ⟶ Spec (.of k))

/-- The actual product map `f × id_Z` between the two fiber products over `Spec k`.
Source: the blueprint displayed comparison preceding Step 1
(blueprint: lem-trf-external-comparison-triangles). -/
noncomputable abbrev externalComparisonProductMap : pullback (f ≫ b) c ⟶ pullback b c :=
  pullback.lift (pullback.fst (f ≫ b) c ≫ f) (pullback.snd (f ≫ b) c)
    ((Category.assoc _ _ _).trans pullback.condition)

/-- The source functor `Q ↦ p_Y^* Rf_* L ⊗ᴸ p'_Z{}^* Q`, restricted to D⁺.
Source: the blueprint displayed comparison and Step 2
(blueprint: lem-trf-external-comparison-triangles). -/
noncomputable abbrev externalComparisonSource (L : DerivedCategoryModule A X) :
    _root_.DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategoryModule A (pullback b c) :=
  _root_.DerivedCategory.Plus.ι ⋙
    L((pullback.snd b c)^*[ModuleCat.{u + 1} A]) ⋙
      (derivedTensor (ModuleCat.{u + 1} A) (pullback b c)).obj
        (L((pullback.fst b c)^*[ModuleCat.{u + 1} A]).obj
          (R((f)_*[ModuleCat.{u + 1} A]).obj L))

/-- The target functor `Q ↦ R(f × id_Z)_*(p_X^* L ⊗ᴸ p_Z^* Q)`, restricted to D⁺.
Source: the blueprint displayed comparison and Step 2
(blueprint: lem-trf-external-comparison-triangles). -/
noncomputable abbrev externalComparisonTarget (L : DerivedCategoryModule A X) :
    _root_.DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategoryModule A (pullback b c) :=
  _root_.DerivedCategory.Plus.ι ⋙
    L((pullback.snd (f ≫ b) c)^*[ModuleCat.{u + 1} A]) ⋙
      (derivedTensor (ModuleCat.{u + 1} A) (pullback (f ≫ b) c)).obj
        (L((pullback.fst (f ≫ b) c)^*[ModuleCat.{u + 1} A]).obj L) ⋙
          R((externalComparisonProductMap f b c)_*[ModuleCat.{u + 1} A])

/-- The fixed exchange morphism, using the recorded unbounded exchange and the canonical
identification of derived pullback with exact inverse image on constant-coefficient modules.
Source: the blueprint displayed comparison; Stacks Tag 07A7
(blueprint: lem-trf-external-comparison-triangles). -/
noncomputable def externalComparisonExchange (L : DerivedCategoryModule A X) :
    L((pullback.fst b c)^*[ModuleCat.{u + 1} A]).obj
        (R((f)_*[ModuleCat.{u + 1} A]).obj L) ⟶
      R((externalComparisonProductMap f b c)_*[ModuleCat.{u + 1} A]).obj
        (L((pullback.fst (f ≫ b) c)^*[ModuleCat.{u + 1} A]).obj L) :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
      (pullback.fst b c)).hom.app _ ≫
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
      (CommSq.mk (pullback.lift_fst _ _ _).symm)).app L ≫
    R((externalComparisonProductMap f b c)_*[ModuleCat.{u + 1} A]).map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.fst (f ≫ b) c)).inv.app L)

/-- The specified comparison: exchange tensored with the identity, then the ordinary
projection morphism, then direct image of tensoring with the composition comparison.
Source: the blueprint displayed comparison preceding Step 1; Stacks Tags 0B56 and 03D8
(blueprint: lem-trf-external-comparison-triangles). -/
noncomputable def externalComparisonMap (L : DerivedCategoryModule A X)
    (Q : _root_.DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (externalComparisonSource A f b c L).obj Q ⟶
      (externalComparisonTarget A f b c L).obj Q :=
  ((derivedTensor (ModuleCat.{u + 1} A) (pullback b c)).map
      (externalComparisonExchange A f b c L)).app _ ≫
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A)
      (externalComparisonProductMap f b c)).app
        (L((pullback.fst (f ≫ b) c)^*[ModuleCat.{u + 1} A]).obj L)).app _ ≫
    R((externalComparisonProductMap f b c)_*[ModuleCat.{u + 1} A]).map
      (((derivedTensor (ModuleCat.{u + 1} A) (pullback (f ≫ b) c)).obj
        (L((pullback.fst (f ≫ b) c)^*[ModuleCat.{u + 1} A]).obj L)).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
            (externalComparisonProductMap f b c) (pullback.snd b c)
            (pullback.snd (f ≫ b) c) (pullback.lift_snd _ _ _).symm).inv.app
              ((_root_.DerivedCategory.Plus.ι).obj Q)))

/-- For a bounded flat model of L, the external comparison is a natural transformation
of triangulated functors, commutes with the canonical shifts, and supplies all three
components of a morphism of the image distinguished triangles, including the last square.
Source: the blueprint `lem-trf-ordinary-kunneth.proof.md`, displayed comparison and Step 2
(blueprint: lem-trf-external-comparison-triangles).

Proof (the eight steps of the DAG):
1. Constant-coefficient inverse image is exact. Its termwise derived functor has the
canonical identity shift and is identified with derived pullback.
2. K-injective resolutions give the triangulated unbounded direct image. Derived tensor
with a fixed object is triangulated. Compose these functors and restrict to D⁺.
3. Factor the displayed comparison as exchange tensored with the identity, projection,
and direct image of tensoring with the inverse-image composition isomorphism.
4. For the first factor, the second-variable tensor shift multiplies first degree p by
(-1)^p. A degree-zero map in the first factor commutes with this sign. Descend this
identity from K-flat representatives; bifunctoriality also gives naturality.
5. The projection factor is the ringed projection mate for constant coefficients. Its
canonical pullback tensor comparison and derived adjunction give naturality and shift
compatibility by lem-weil-pbc-ringed-projection-mate-exact, precomposed with p'_Z{}^*.
6. The sheaf composition isomorphism is applied degreewise, so it commutes with termwise
shift. Tensoring on the left gives the same (-1)^p on either path. Descend and apply Rh_*.
7. Compose the three natural shift-compatible transformations. Their shift equations
compose to the displayed equation for this actual comparison.
8. Naturality supplies the first two squares of every image triangle. Naturality at the
connecting morphism followed by the shift equation supplies its third square. Both
image triangles are distinguished by step 2. No comparison is assumed invertible. -/
theorem externalComparison_triangles (L : DerivedCategoryModule A X)
    (_hL : ∃ (a b : ℤ)
      (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ),
      IsBoundedFlatComplex A a b P ∧ Nonempty (L ≅ _root_.DerivedCategory.Q.obj P)) :
    (externalComparisonSource A f b c L).IsTriangulated ∧
    (externalComparisonTarget A f b c L).IsTriangulated ∧
    ∃ α : externalComparisonSource A f b c L ⟶ externalComparisonTarget A f b c L,
      (∀ Q, α.app Q = externalComparisonMap A f b c L Q) ∧
      (∀ Q, α.app (Q⟦(1 : ℤ)⟧) ≫
          ((externalComparisonTarget A f b c L).commShiftIso (1 : ℤ)).hom.app Q =
        ((externalComparisonSource A f b c L).commShiftIso (1 : ℤ)).hom.app Q ≫
          (α.app Q)⟦(1 : ℤ)⟧') ∧
      (∀ (T : Triangle (_root_.DerivedCategory.Plus
          (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))),
        T ∈ distTriang _ →
          (externalComparisonSource A f b c L).mapTriangle.obj T ∈ distTriang _ ∧
          (externalComparisonTarget A f b c L).mapTriangle.obj T ∈ distTriang _ ∧
          ∃ φ : (externalComparisonSource A f b c L).mapTriangle.obj T ⟶
              (externalComparisonTarget A f b c L).mapTriangle.obj T,
            φ.hom₁ = α.app T.obj₁ ∧ φ.hom₂ = α.app T.obj₂ ∧ φ.hom₃ = α.app T.obj₃) := by
  sorry

end AlgebraicGeometry.Etale
