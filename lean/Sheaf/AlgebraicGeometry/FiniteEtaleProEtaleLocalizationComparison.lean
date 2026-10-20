/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing

/-!
# Finite etale localization extension agrees with direct image

Source: blueprint `prop-exc-finite-etale-adjoint`, proof paragraphs 1--2
(blueprint: lem-sf-finite-etale-proetale-localization-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

/-- The sheafified left Kan extension along finite etale localization is naturally
isomorphic to direct image. This concerns ordinary module sheaves, with arbitrary
commutative coefficients.

Source: blueprint `prop-exc-finite-etale-adjoint`, proof paragraphs 1--2, the finite
sum/product comparison before the adjunction and derived passage
(blueprint: lem-sf-finite-etale-proetale-localization-comparison).

Proof: cover the base by etale neighbourhoods on which the finite etale map is a
finite disjoint union of copies of the base. These form a pro-etale cover, since
etale maps are open and a finite subfamily of their images covers each affine test
open. On a split member, the sheaf condition identifies a sheaf with the tuple of
its restrictions to the sheets. The left Kan extension followed by sheafification
is the finite coproduct of this tuple: the indexing category has one terminal
object for each lift, and locally a lift selects a sheet. The direct image is the
finite product of the tuple by its base-change formula. The finite biproduct map
has identity diagonal entries and zero off-diagonal entries; its inverse is the
sum of inclusions composed with projections. Both maps are invariant under
permutations of the sheets. Refine an overlap by clopen intersections of the two
systems of sheets; there the two descriptions differ by such a permutation.
Consequently the maps and their inverses agree on overlaps and glue uniquely.
The same uniqueness proves naturality and both inverse identities. For zero sheets
both functors give the zero sheaf, so no surjectivity assumption is necessary. -/
theorem finiteEtale_localizationExtensionIso {V X : Scheme.{u}} (e : V ⟶ X)
    [IsFinite e] [Etale e] (R : Type (u + 1)) [CommRing R] :
    Nonempty
      (Functor.sheafPullbackConstruction.sheafPullback
          (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale e))
          (ModuleCat.{u + 1} R) (Scheme.ProEt.topology V) (Scheme.ProEt.topology X) ≅
        lowerStar (ModuleCat.{u + 1} R) e) := by
  sorry

end AlgebraicGeometry.ProEtale
