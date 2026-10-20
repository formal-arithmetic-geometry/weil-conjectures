/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.OrgogozoGoodModification
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes

/-!
# Bounded constructibility on the transported etale site

Source: blueprint sec-proper-base-change/sk-thm-p1,
node def-weil-pbc-constructible-complexes, order 1108
(blueprint: def-weil-pbc-constructible-complexes).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.OrientedNearbyCycles

/-- Bounded constructibility for the transported etale derived category. The second
conjunct is the canonical AsSmall transport of constructible cohomology sheaves to the
small etale site; it is the transported form of def-weil-pbc-constructible-complexes.
Source: blueprint sec-proper-base-change/sk-thm-p1,
node def-weil-pbc-constructible-complexes, order 1108
(blueprint: def-weil-pbc-constructible-complexes). -/
def IsBoundedConstructible (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (K : EtaleDerived X Λ) : Prop :=
  IsBounded (etaleDatum X) (Coeff Λ) K ∧
    ∀ q : ℤ, ∃ F : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (Coeff.{u, u + 1} Λ)),
      Scheme.IsConstructibleEtaleModuleSheaf F ∧
        Nonempty
          (orgogozoModuleSections X Λ
              ((DerivedCategory.homologyFunctor
                ((etaleDatum X).modules (Coeff Λ)) q).obj K) ≅
            (AsSmall.down : EtaleSite.{u, u + 1} X ⥤ X.Etale).op ⋙ F.obj)

end AlgebraicGeometry.OrientedNearbyCycles
