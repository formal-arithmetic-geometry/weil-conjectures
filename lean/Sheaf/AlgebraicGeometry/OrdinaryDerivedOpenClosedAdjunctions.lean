/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

/-!
# The ordinary derived open-closed adjunctions

Source: blueprint sec-smooth-purity/sk-prop-sf-open-closed-triangle
(blueprint: prop-weil-open-closed-recollement-adjunctions).

The adjunctions themselves are the existing
`derivedOpenImmersionLowerShriekUpperStarAdjunction` and
`mapDerivedUpperStarLowerStarAdjunction`, specialized to module coefficients.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace ProEtale

/-- The pro-étale open/closed recollement adjunctions required by the recorded
open/closed node.  Source: blueprint sec-smooth-purity/sk-prop-sf-open-closed-triangle
(blueprint: prop-weil-open-closed-recollement-adjunctions).
Proof, following the dependency node's six steps:
1. At each finite constant coefficient stage use the module inverse-image/direct-image
   adjunction and the exact extension-by-zero adjunction. The coefficient-ring
   identification makes these the specified module operations.
2. Exact functors preserve quasi-isomorphisms. Descend the termwise open unit and
   counit through localization; their triangle identities descend too, giving the
   unbounded open adjunction (lem-weil-pbc-exact-functor-derived-factorization and
   lem-weil-pbc-localization-universal-property).
3. The sheaf open unit is invertible (lem-exc-proetale-open-unit). Its degreewise
   inverses form a chain map, hence the derived unit is invertible.
4. Resolve a closed-side complex by K-injectives. The exact inverse image ensures
   that its right adjoint preserves K-injectives. Applying direct image to a
   resolution between K-injectives gives the canonical computation comparison.
5. Compose the K-injective Hom comparison with the termwise sheaf adjunction.
   Localization gives the natural bijection defining the closed derived adjunction;
   its comparison is natural and independent of the chosen resolution.
6. On a K-injective representative its actual counit is the localized sheaf counit
   conjugated by the computation comparison. The sheaf counit is invertible by
   lem-exc-proetale-closed-fully-faithful; naturality extends this to every derived
   object. No boundedness or constructibility hypothesis is needed.
Sources: Stacks Tags 03D7, 03DI, 03DJ, 09BN, 08BJ, 079P and 07A5. -/
theorem proEtaleOpenClosedAdjunctions
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i]
    (_hij : Set.range i.base = (Set.range j.base)ᶜ) :
    IsIso (AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).unit ∧
    IsIso (AlgebraicGeometry.ProEtale.derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) i).counit := by
  constructor
  · exact Adjunction.isIso_mapDerivedCategoryAdjunction_unit
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
  · have := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).preservesKInjectiveComplexes
    exact Adjunction.counit_isIso_of_R_fully_faithful _

end ProEtale

namespace Etale

/-- The open unit and closed counit are invertible on the entire ordinary derived
categories. Source: blueprint sk-prop-sf-open-closed-triangle
(blueprint: prop-weil-open-closed-recollement-adjunctions).
Proof: extension by zero and inverse image are exact; descend their sheaf adjunction
termwise. The open unit is already invertible on sheaves. A closed direct image is
fully faithful and preserves K-injective complexes since its left adjoint is exact;
its total derived functor is fully faithful. Thus the counit of i* ⊣ Ri* is invertible.
These are the stated adjunctions, and their unit and counit are their descended maps. -/
theorem ordinaryDerivedOpenClosedAdjunctions
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i]
    (_hij : Set.range i.base = (Set.range j.base)ᶜ) :
    IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).unit ∧
    IsIso (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit := by
  constructor <;> infer_instance

end AlgebraicGeometry.Etale
