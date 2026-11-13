/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.Grp.Ulift

import WeilConjectures.AlgebraicGeometry.EtaleULiftInjectiveExtension
import WeilConjectures.AlgebraicGeometry.EtaleSmallInjectiveCriterion

/-! Coefficient universe lift on the small étale site. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Coefficient lift preserves injective abelian sheaves on the small étale site.
Source: Stacks Project, Injectives, Lemma 19.7.3, Tag 01DO. -/
theorem etale_ulift_injective (X : Scheme.{u})
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective I] :
    Injective
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj I) := by
  apply etale_injective_of_small_extensions X
  intro A B hB f hf g
  exact etale_ulift_injective_extension X I hB f g

end AlgebraicGeometry.Scheme
