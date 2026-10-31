/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.CategoryTheory.ModuleObjects.Free

/-!
# Finite locally projective pro-etale coefficient modules

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-localization,
sk-lem-formal-closed-support-stratum-hom.md, finite locally projective hypothesis
(blueprint: def-pur-condensed-finite-locally-projective).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Every site object has a covering sieve on whose domains the module is a retract
of a finite free module. Ranks may vary and may be zero. Restriction to a site object
is the canonical inverse image to its small pro-etale site, equivalent to slice restriction.
Source: blueprint stratum Hom lemma, finite locally projective hypothesis
(blueprint: def-pur-condensed-finite-locally-projective). -/
def IsFiniteLocallyProjective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (X : Scheme.{u}) (L : supportModules Λ X) : Prop :=
  ∀ V : X.ProEt, ∃ R : Sieve V, R ∈ Scheme.ProEt.topology X V ∧
    ∀ (W : X.ProEt) (f : W ⟶ V), R f →
      ∃ (r : ℕ)
        (ι : (supportPullback Λ W.hom).obj L ⟶ Mod.finiteFree (condensedRingObj Λ W.left) r)
        (π : Mod.finiteFree (condensedRingObj Λ W.left) r ⟶
          (supportPullback Λ W.hom).obj L), ι ≫ π = 𝟙 _

end AlgebraicGeometry.ProEtale.CondensedRing
