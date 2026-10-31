/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleExceptionalOriginTransfer
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-! Comparison of residue maps across the étale/pro-étale site comparison.
(blueprint: lem-sf-proetale-residue-comparison)

The helper records the tensor-comparison square for a finite residue module and the bounded-below
full-faithfulness argument which reflects an isomorphism back to the étale model.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- Residue isomorphisms of a morphism between exceptional étale origins follow from the
corresponding residue isomorphisms after comparison to the pro-étale site.

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-lem-sf-kunneth-star/
sk-lem-sf-kunneth-star.proof.md, residue comparison component
(blueprint: lem-sf-proetale-residue-comparison).

Proof: use strong monoidality and constant-sheaf comparison to build the natural tensor square.
The Tor intervals put both residue origins in the bounded-below subcategory, where comparison is
fully faithful. Reflect each pro-etale residue isomorphism through this square and full
faithfulness to obtain the etale residue isomorphism. -/
theorem etale_residue_isIso_of_pro_residue_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    {E E' : Etale.DerivedCategoryModule A S}
    (hE : exceptionalTransportEtaleObjects A S E)
    (hE' : exceptionalTransportEtaleObjects A S E')
    (hplusE : _root_.DerivedCategory.TStructure.t.plus E)
    (hplusE' : _root_.DerivedCategory.TStructure.t.plus E')
    (w : E ⟶ E')
    {K K' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))}
    (e : (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj E ≅ K)
    (e' : (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj E' ≅ K')
    (u : K ⟶ K')
    (hw : (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.map w =
      e.hom ≫ u ≫ e'.inv)
    (hres : ∀ m : Ideal A, m.IsMaximal →
      IsIso (((derivedTensor (ModuleCat.{u + 1} A) S).map u).app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A (A ⧸ m)))))) :
    ∀ m : Ideal A, m.IsMaximal → IsIso ((Etale.reductionModIdeal A S m).map w) := by
  sorry

end AlgebraicGeometry.ProEtale
