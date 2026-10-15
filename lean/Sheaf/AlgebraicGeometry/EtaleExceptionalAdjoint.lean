/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.Compactification.Refinement
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import Sheaf.AlgebraicGeometry.KInjectiveResolutions
import Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit

/-! # The ordinary ambient exceptional adjoint

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/
thm-amb-etale-exceptional-adjoint.md; Stacks Project, Tag 0F5Y
(blueprint: thm-amb-etale-exceptional-adjoint).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The ordinary unbounded compact-support functor for a fixed compactification has a
right adjoint, conventionally denoted `f^×`, for finite commutative coefficients.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/
thm-amb-etale-exceptional-adjoint.md; Stacks Project, Tag 0F5Y
(blueprint: thm-amb-etale-exceptional-adjoint).

Proof:
1. Present each small etale site in a common universe. Module sheaves form a Grothendieck
   abelian category by lem-pur-ringed-site-grothendieck-abelian. By
   lem-kun-grothendieck-derived-coproducts, derived coproducts are termwise, including the
   empty coproduct.
2. Extension by zero is exact (lem-weil-pbc-extension-by-zero-exact), so its degreewise
   descent is triangulated (lem-sf-exact-functor-derived-triangulated). Its adjunction
   with restriction (lem-weil-pbc-extension-by-zero-adjunction) shows that it preserves
   coproducts, hence so does its descent.
3. Resolve by K-injectives (prop-weil-pbc-kinjective-resolutions-exist). Maps to such
   resolutions compute derived Hom (lem-weil-pbc-kinjective-hom-derived). The cone of a
   map of K-injectives is K-injective, using the acyclic Hom-complex characterization
   of def-weil-pbc-kinjective-resolutions. Direct image respects shifts and cone matrices,
   so its total right derived functor is exact. By lem-amb-proper-coproducts it preserves
   coproducts for the finite coefficients and Noetherian proper finite-type morphism.
   Thus the composite Rr_* Dj_! is exact and preserves coproducts.
4. Apply lem-grothendieck-derived-brown-right-adjoint to that composite on the whole
   ordinary unbounded derived category. This supplies the right adjoint with no
   boundedness or constructibility restriction and needs no compactification comparison.
-/
theorem isLeftAdjoint_rightDerivedLowerShriekOfCompactification
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {f : X ⟶ S} (c : Compactification f)
    [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian c.Z] [CompactSpace c.Z]
    [IsLocallyNoetherian S] [CompactSpace S] :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).IsLeftAdjoint := by
  sorry

end AlgebraicGeometry.Etale
