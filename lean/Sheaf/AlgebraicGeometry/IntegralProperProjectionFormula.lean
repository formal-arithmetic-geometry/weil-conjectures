/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.BaseChange.Derived
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.PullbackConstantModule
import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormulaBoundedBelow
import Sheaf.AlgebraicGeometry.GeometricPointDerivedConstants
import Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction
import Sheaf.AlgebraicGeometry.GeometricPointProjectionComparison
import Sheaf.AlgebraicGeometry.IntegralDerivedTensorBoundedTorsion

/-!
# The integral proper projection formula

Source: Stacks Project, Tag 0F0F, Lemma 59.92.5, and blueprint
`sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-0f0f.md`
(blueprint: lem-kun-0f0f).

Abelian sheaves are encoded as modules over the universe lift of the integers. This is
only the coefficient-universe convention: the canonical integer action is unique.
The two boundedness conclusions and invertibility in the ambient derived category express
invertibility in its strictly full bounded-below subcategory.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The canonical integral projection map for a proper morphism is an isomorphism in `D⁺`
when its first argument has torsion cohomology. Source: Stacks Project, Tag 0F0F,
Lemma 59.92.5 (blueprint: lem-kun-0f0f).

Proof:
1. Choose lower bounds `a,b` for `E,K`. Exact inverse image
   (prop-weil-pbc-inverse-image-modules-exact) preserves `b`. The integral tensor estimate
   (lem-kun-integral-derived-tensor-bounded-torsion) bounds `E ⊗ᴸ f⁻¹K` below by `a+b-1`
   and makes its cohomology torsion. Direct image preserves lower bounds
   (lem-kun-tensor-t-est). The same integral estimate bounds the source below by `a+b-1`.
2. At a geometric point `s = Spec Ω → Y`, form `Z = X ×[Y] s`. Properness survives
   base change (lem-weil-pbc-proper-base-change). The fibre is quasi-compact since it is
   finite type over an affine scheme (def-weil-pbc-scheme-conventions). Intersections of
   affine opens are closed subschemes of their product over `Ω`, hence affine by
   lem-weil-pbc-fibre-product-affine-spectra and def-weil-closed-immersion. Their product
   over `ℤ` maps through the quotient imposing `Ω`-bilinearity. The absolute diagonal is
   therefore quasi-compact (def-weil-quasi-separated-morphism), so `Z` is qcqs.
3. Proper base change (thm-weil-pbc-bounded-below) applies both to `E` and to
   `E ⊗ᴸ f⁻¹K`. Inverse-image monoidality (lem-kun-inverse-image-monoidal) and
   lem-kun-proj-formula-natural identify the pulled-back map with the projection map
   of `Z → s`. The exchanges of def-kun-unbounded-exchange and
   def-weil-pbc-derived-exchange agree on bounded-below objects: both are adjoint
   transposes of the square comparison followed by inverse image of the same counit.
4. By lem-kun-stalk-as-pullback and lem-exc-abelian-sheaves-gmodules, sheaves on `s` are
   abelian groups. The constant-germ isomorphism
   (lem-weil-pbc-constant-sheaf-geometric-stalk) identifies the constant sheaf functor
   (def-kun-constant-sheaf) with the inverse equivalence. Constant sheafification
   (def-weil-pbc-sheafification) is left adjoint to sections; hence geometric stalk
   composed with direct image from `Z` is sections on `Z`. Exactness passes these
   adjunctions to derived categories. The canonical pullback of constants is the one
   in lem-kun-pullback-constant. On constant local sections the tensor constraints send
   `m ⊗ n` to its constant section; sheafification and K-flat representatives extend
   this compatibility to derived tensors. Thus the actual counit-mate map of
   def-kun-projection-formula-map becomes def-kun-constant-projection-morphism for
   `Z`, which is invertible by lem-kun-0f0e.
5. The map is now invertible at every geometric point. Exact geometric stalks
   (prop-weil-pbc-geometric-stalks-exact) identify its cohomology stalks with the
   cohomology of its stalks. Conservativity (lemma-weil-pbc-geometric-stalk-conservative)
   makes every cohomology map invertible. Its cone is acyclic, proving invertibility. -/
theorem isIso_rightDerivedLowerStarProjectionMap_integral_of_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (E : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))
    (K : _root_.DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))
    (hE : DerivedCategory.torsionCohomology (ULift.{u + 1} ℤ) X E.obj) :
    _root_.DerivedCategory.TStructure.t.plus
        (((derivedTensorRightDerivedLowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f).obj
          E.obj).obj K.obj) ∧
      _root_.DerivedCategory.TStructure.t.plus
        (((rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f).obj E.obj).obj K.obj) ∧
      IsIso (((rightDerivedLowerStarProjectionMap
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f).app E.obj).app K.obj) := by
  sorry

end AlgebraicGeometry.Etale
