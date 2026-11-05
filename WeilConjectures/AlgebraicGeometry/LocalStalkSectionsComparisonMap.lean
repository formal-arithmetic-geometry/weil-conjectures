/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleObjectCohomologyStalkComplex
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-! # The canonical degree-zero local-scheme comparison map

Source: Stacks Project, Tag 03Q6, the pullback maps in Lemma 59.51.5.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

namespace LocalStalkSections

variable {X : Scheme.{u + 1}} (i : X.Opens ⥤ X.Etale)
  (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (x : X)

variable (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
    Sheaf (Spec (X.presheaf.stalk x)).smallEtaleTopology AddCommGrpCat.{u + 1})
  (hH : H ⊣ (X.fromSpecStalk x).Etale.sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} X.smallEtaleTopology
    (Spec (X.presheaf.stalk x)).smallEtaleTopology)

end LocalStalkSections
