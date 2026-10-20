/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.AlgebraicGeometry.DerivedCategories

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives

/-!
# Bounded-below Leray isomorphism

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
`sk-prop-sf-kunneth-ordinary/lem-kun-leray-bdd.md`
(blueprint: lem-kun-leray-bdd)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- For a morphism of schemes, bounded-below derived global sections satisfy Leray.
Source: blueprint node `lem-kun-leray-bdd` (blueprint: lem-kun-leray-bdd).
Construction and proof plan:
1. Choose an integer lower bound for `E`. The categories of abelian étale sheaves have
   enough injectives (`lem-weil-pbc-module-sheaves-enough-injectives`), so choose a bounded
   below injective representative `I` (`lem-weil-pbc-dplus-injective-representative`). It is
   K-injective. Direct image preserves injectives
   (`lem-weil-pbc-direct-image-preserves-injectives`) and zero objects, so `f_* I` is also
   bounded below and K-injective, and computes `Rf_* E` (`def-weil-pbc-direct-image`).
2. Compute both derived global-sections objects on these representatives
   (`def-weil-pbc-etale-cohomology`, `def-weil-pbc-global-sections-functor`). Degreewise,
   sections of `f_* I` over `Y` are sections of `I` over `Y ×_Y X`. The projection to `X`
   is an isomorphism by the fibre-product universal property (`def-pc-fibre-product`).
   Restriction gives a chain isomorphism, whose inverse is the asserted comparison.
3. A morphism of derived objects is represented by a unique homotopy class between the
   K-injective representatives (`lem-weil-pbc-kinjective-hom-derived`). The section maps
   commute with that class and with homotopies, proving naturality and independence of
   representatives. Iterated fibre-product projections give the same restriction as the
   single projection, proving composition compatibility; the identity projection proves
   identity compatibility. The unbounded convention agrees naturally with this one by
   `lem-kun-rgamma-unbounded-bounded` (not yet stated, hence not imported).

The construction below is the component of the inverse natural composition isomorphism
`Functor.rightDerivedFunctorPlusCompIso'`, for `lowerStarCompGlobalSectionsIso`. Thus it
specifies the canonical comparison, rather than an arbitrary objectwise isomorphism.
Its naturality is inherited from that natural isomorphism; the unit and associativity laws
are `rightDerivedFunctorPlusCompIso_id_comp`, `rightDerivedFunctorPlusCompIso_comp_id`, and
`rightDerivedFunctorPlusCompIso'_assoc`. -/
noncomputable def rightDerivedGlobalSectionsLerayPlus {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj E ≅
      ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj
        (((f)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlus.obj E)) := by
  letI : ((f)_*[AddCommGrpCat.{u + 1}]).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
  exact ((Functor.rightDerivedFunctorPlusCompIso' _ _
    (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} f)).symm.app E)

end AlgebraicGeometry.Etale
